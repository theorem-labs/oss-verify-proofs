(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainG2.v (commit ce1a656b52b7, file sha256 d7d939d9cd0b) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainG2.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 9564bfd9c706) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainG2.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the CELL facts Drain's entry shell asks - the two caches' header
   words, the mutex word, the two Quarantine constants - read off DMiface.qview's qv_cells / qv_const
   (DMiface.v:80-84) instead of cgif's allocator relation.  The extraction is the released seed's (YFev.v:64-128:
   rootT_vals / rootG_vals / mutex_vals / const_vals), with the cells taken straight from YG0n.quar_cells, so it
   holds at any instance whose qview holds.  DMdrainE takes these as its hypotheses VQT / VQG / VQW / VMAX / VMIN.
   rule 24: no function proved (kind: cell extraction; the lane's reuse search is the internal file LOOKUP-B1-drain.txt,
   `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24
   check B1LookupCheck CONFIRM).
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFex YFf2 YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFew YFff YFeu YFey YFgj YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Open Scope am_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (mem : word -> option byte).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
(* the instance object is the image's allocator (qview's qv_inst with TfibSyms) *)
Hypothesis AQ : A_QUAR = as_inst B + o_quar.
(* qview's cells and constants *)
Hypothesis QC : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (quar_cells X).
Hypothesis QK : val_mem tfibsegs m0 (as_inst B + o_q_max) 8 kQuarantineMax /\
  val_mem tfibsegs m0 (as_inst B + o_q_min) 8 kQuarantineMin /\
  val_mem tfibsegs m0 (as_inst B + o_q_cmutex + 2) 2 0.

Lemma cell_q : forall c e (w : nat) e', In c (quar_cells X) -> c = ACell e w (AV e') ->
val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros c e w e' Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem e w e'). exact (proj1 (Forall_forall _ _) QC _ Hin).
Qed.
Lemma cell_qZ : forall c e (w : nat) x, In c (quar_cells X) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. intros c e w x Hin E. exact (cell_q c e w (ANum x) Hin E). Qed.

Lemma rootT_q : val_mem tfibsegs m0 (T + t_qc) 8 (YFgj.TSZv tq) /\ val_mem tfibsegs m0 (T + t_qc + 8) 8 (YFgj.TFv ly tq) /\
val_mem tfibsegs m0 (T + t_qc + 16) 8 (YFgj.TLv ly tq) /\ val_mem tfibsegs m0 (T + t_qc + 24) 8 (YFgj.TBv tq).
Proof.
assert (IN : forall c, In c (qc_cells (AT t_qc) tq) -> In c (quar_cells X)).
{ intros c Hc. unfold quar_cells. right; right. apply in_app_iff. left. exact Hc. }
unfold YFgj.TSZv, YFgj.TFv, YFgj.TLv, YFgj.TBv. splits.
- apply (cell_qZ _ (AT t_qc) 8 _ (IN _ ltac:(unfold qc_cells; left; reflexivity)) eq_refl).
- replace (T + t_qc + 8) with (aeval B ly (aoff (AT t_qc) 8)) by (cbn; lia).
  replace (match Tq with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match Tq with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct Tq; reflexivity).
  apply (cell_q _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; left; reflexivity)) eq_refl).
- replace (T + t_qc + 16) with (aeval B ly (aoff (AT t_qc) 16)) by (cbn; lia).
  replace (match rev Tq with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev Tq with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct (rev Tq); reflexivity).
  apply (cell_q _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; right; left; reflexivity)) eq_refl).
- replace (T + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
  apply (cell_qZ _ _ 8 _ (IN _ ltac:(unfold qc_cells; do 3 right; left; reflexivity)) eq_refl).
Qed.

Lemma rootG_q : val_mem tfibsegs m0 (A_QUAR + 160) 8 (YFgj.GSZv gq) /\ val_mem tfibsegs m0 (A_QUAR + 168) 8 (YFgj.GFv ly gq) /\
val_mem tfibsegs m0 (A_QUAR + 176) 8 (YFgj.GLv ly gq) /\ val_mem tfibsegs m0 (A_QUAR + 184) 8 (YFgj.GBv gq).
Proof.
assert (IN : forall c, In c (qc_cells (AInst o_q_size) gq) -> In c (quar_cells X)).
{ intros c Hc. unfold quar_cells. right; right. apply in_app_iff. right. exact Hc. }
rewrite AQ. unfold YFgj.GSZv, YFgj.GFv, YFgj.GLv, YFgj.GBv. splits.
- replace (as_inst B + o_quar + 160) with (aeval B ly (AInst o_q_size)) by (cbn; unfold o_quar, o_q_size; lia).
  apply (cell_qZ _ (AInst o_q_size) 8 _ (IN _ ltac:(unfold qc_cells; left; reflexivity)) eq_refl).
- replace (as_inst B + o_quar + 168) with (aeval B ly (aoff (AInst o_q_size) 8)) by (cbn; unfold o_quar, o_q_size; lia).
  replace (match G with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match G with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct G; reflexivity).
  apply (cell_q _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; left; reflexivity)) eq_refl).
- replace (as_inst B + o_quar + 176) with (aeval B ly (aoff (AInst o_q_size) 16)) by (cbn; unfold o_quar, o_q_size; lia).
  replace (match rev G with [] => 0 | b :: _ => SB + b_self b end) with (aeval B ly (match rev G with [] => ANum 0 | b :: _ => batch_exp b end)) by (destruct (rev G); reflexivity).
  apply (cell_q _ _ 8 _ (IN _ ltac:(unfold qc_cells; right; right; left; reflexivity)) eq_refl).
- replace (as_inst B + o_quar + 184) with (aeval B ly (aoff (AInst o_q_size) 24)) by (cbn; unfold o_quar, o_q_size; lia).
  apply (cell_qZ _ _ 8 _ (IN _ ltac:(unfold qc_cells; do 3 right; left; reflexivity)) eq_refl).
Qed.

(* The mutex word at Drain's entry: both locks free and the two bytes after them zero (DMdrainE's VQW). *)
Lemma mutex_q : val_mem tfibsegs m0 (A_QUAR + 152) 4 0.
Proof.
assert (C1 : val_mem tfibsegs m0 (as_inst B + o_q_cmutex) 1 0).
{ apply (cell_qZ (z1 (AInst o_q_cmutex) 0) (AInst o_q_cmutex) 1 0); [|reflexivity]. unfold quar_cells. left. reflexivity. }
assert (C2 : val_mem tfibsegs m0 (as_inst B + o_q_rmutex) 1 0).
{ apply (cell_qZ (z1 (AInst o_q_rmutex) 0) (AInst o_q_rmutex) 1 0); [|reflexivity]. unfold quar_cells. right; left. reflexivity. }
destruct QK as (_ & _ & C3).
rewrite AQ. unfold o_quar, o_q_cmutex, o_q_rmutex in *.
intros k Hk. cbn in Hk.
assert (CASES : k = 0%nat \/ k = 1%nat \/ k = 2%nat \/ k = 3%nat) by lia.
destruct CASES as [-> |[-> |[-> | ->]]].
- pose proof (C1 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E. rewrite Z.add_0_r. rewrite <- Z.add_assoc. exact E.
- pose proof (C2 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E.
  replace (as_inst B + 728 + 152 + Z.of_nat 1) with (as_inst B + (728 + 153)) by lia. exact E.
- pose proof (C3 0%nat ltac:(lia)) as E.
  replace (as_inst B + 728 + 152 + Z.of_nat 2) with (as_inst B + (728 + 152) + 2 + Z.of_nat 0) by lia. exact E.
- pose proof (C3 1%nat ltac:(lia)) as E.
  replace (as_inst B + 728 + 152 + Z.of_nat 3) with (as_inst B + (728 + 152) + 2 + Z.of_nat 1) by lia. exact E.
Qed.

Lemma const_q : val_mem tfibsegs m0 (A_QUAR + 64) 8 kQuarantineMax /\ val_mem tfibsegs m0 (A_QUAR + 72) 8 kQuarantineMin.
Proof.
destruct QK as (K1 & K2 & _). rewrite AQ. unfold o_q_max, o_q_min, o_quar in *.
split; [replace (as_inst B + 728 + 64) with (as_inst B + (728 + 64)) by lia; exact K1
       | replace (as_inst B + 728 + 72) with (as_inst B + (728 + 72)) by lia; exact K2].
Qed.
End g.
End f.
