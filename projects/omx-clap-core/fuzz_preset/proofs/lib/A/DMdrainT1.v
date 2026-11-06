(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainT1.v (commit 67deba317dfb, blob fe65d03a65a5) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 1 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFff AFev AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMsegDA DMseg_dme DMseg_dmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

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
SRr tfibsegs W (mkCfg (mkst regs0 (w64 0x341cc) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0))
(DMsegDA.postDm W ly regs0 mem0 md0 gq tq).
Proof.
pose proof check_ge as CG.
destruct (qc_list gq) as [|b t] eqn:EG.
- exact (DMseg_dme.segDEm W ly regs0 mem0 md0 gq tq mat0 FH EG CG).
- exact (DMseg_dmn.segDNm W ly regs0 mem0 md0 gq tq mat0 FH ltac:(rewrite EG; discriminate) CG).
Qed.
End e.
End c.
