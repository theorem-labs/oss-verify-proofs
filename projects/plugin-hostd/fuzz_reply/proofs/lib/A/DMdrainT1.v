(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainT1.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 f56eb7f80567) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 1 image addresses moved by code-verified function pairs (1 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 6 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the first leg of the drain's composition - Quarantine::Drain's
   entry walk, from 0x337ec to the three outcomes of DMsegD.postDm (the return without recycling, the no-merge
   entry to the dequeue loop at 0x33a8c, and MergeBatches' entry at 0x33b74) - over the seed DMdrainE builds
   from DMiface.qview.  The CHECK_GE premise both entry segments take
   (kQuarantineMax < LBv -> kBatchBytes * LSZv <= LBv, the die path 0x339fc -> 0x33b58) is discharged here, and
   unconditionally: every batch weighs at least kBatchBytes, so the quarantine's bytes are at least
   kBatchBytes per batch.
   rule 24: no function proved (kind: composition of segments already walked, DMseg_dme.segDEm /
   DMseg_dmn.segDNm; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches
   Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   - [bytes_ge_count]: the CHECK_GE fact, from the batches' weights;
   - [drain_entry_run]: SRr from Drain's entry to DMsegD.postDm.
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFff AFev AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMsegD DMseg_dme DMseg_dmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Every batch weighs at least kBatchBytes when its chunks have non-negative user sizes, so a cache's bytes are
   at least kBatchBytes per batch: the CHECK_GE at 0x339fc cannot fail. *)
Lemma bytes_ge_count : forall l : list batch,
(forall k, In k (flat_map b_items l) -> 0 <= ck_n k) ->
kBatchBytes * Z.of_nat (length l) <= sum_bytes l.
Proof.
induction l as [|b t IH]; intros HN; cbn [length]; [cbn; unfold kBatchBytes; lia|].
rewrite AFey.sum_bytes_cons, Nat2Z.inj_succ.
assert (HB : kBatchBytes <= b_bytes b).
{ unfold b_bytes. assert (A : 0 <= fold_right (fun k acc => ck_n k + acc) 0 (b_items b)).
  { assert (HI : forall k, In k (b_items b) -> 0 <= ck_n k)
      by (intros k Hk; apply HN; apply in_flat_map; exists b; split; [left; reflexivity | exact Hk]).
    induction (b_items b) as [|k l IHl]; cbn [fold_right]; [lia|].
    pose proof (HI k (or_introl eq_refl)). pose proof (IHl (fun k' Hk' => HI k' (or_intror Hk'))). lia. }
  lia. }
assert (HT : kBatchBytes * Z.of_nat (length t) <= sum_bytes t).
{ apply IH. intros k Hk. apply HN. apply in_flat_map. apply in_flat_map in Hk as (b' & Hb' & Hk').
  exists b'. split; [right; exact Hb' | exact Hk']. }
unfold kBatchBytes in *. lia.
Qed.

Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (gq tq : qcache).
Variable mat0 : list word.
Hypothesis FH : AFgj.free_hyps W ly regs0 mem0 gq tq.
(* the quarantine's byte counts are its batches' weights (DMiface.qview's qv_wf) *)
Hypothesis HGs : qc_bytes gq = sum_bytes (qc_list gq).
Hypothesis HTs : qc_bytes tq = sum_bytes (qc_list tq).
Hypothesis HNN : forall k, In k (flat_map b_items (qc_list gq ++ qc_list tq)) -> 0 <= ck_n k.

Lemma check_ge : kQuarantineMax < AFgj.LBv gq tq -> kBatchBytes * AFgj.LSZv gq tq <= AFgj.LBv gq tq.
Proof.
intros _. unfold AFgj.LBv, AFgj.LSZv, AFgj.GBv, AFgj.TBv, AFgj.GSZv, AFgj.TSZv.
pose proof (bytes_ge_count (qc_list gq ++ qc_list tq) HNN) as HS.
rewrite length_app, YG03.sum_bytes_app in HS. rewrite HGs, HTs. unfold kBatchBytes in *. lia.
Qed.

Theorem drain_entry_run :
SRr tfibsegs W (mkCfg (mkst regs0 (w64 0x337ec) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
(DMsegD.postDm W ly regs0 mem0 md0 gq tq).
Proof.
pose proof check_ge as CG.
destruct (qc_list gq) as [|b t] eqn:EG.
- exact (DMseg_dme.segDEm W ly regs0 mem0 md0 gq tq mat0 FH EG CG).
- exact (DMseg_dmn.segDNm W ly regs0 mem0 md0 gq tq mat0 FH ltac:(rewrite EG; discriminate) CG).
Qed.
End e.
End c.
