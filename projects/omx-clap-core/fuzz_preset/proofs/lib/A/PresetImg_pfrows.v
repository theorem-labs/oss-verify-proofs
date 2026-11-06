(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_pfrows.v (commit eb934de95d13, blob ead097f561d8) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0n YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetRelroGeoA.
Open Scope Z_scope.

#[local] Existing Instance CfImg_A.

Lemma errb_ial_apart_preset_A : forall B, TfibSyms B -> YG0ncf.errb_ial_apart_t (ci := CfImg_A) B.
Proof.
intros B TS a Ha. rewrite (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
cbn [cf_errbuf_obj CfImg_A] in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

Lemma pf_cells_static_preset_A : forall B, TfibSyms B -> YG0ncf.pf_cells_static_t (ci := CfImg_A) B.
Proof.
intros B TS a Ha. rewrite (ts_owned B TS), (ts_inst B TS).
cbn [cf_toolname_cell cf_pfcb_cell CfImg_A] in Ha. split.
- apply Exists_exists. destruct Ha as [Ha | Ha].
  + exists (nth 0 Tfib_owned_static (0, 0)). split; [apply nth_In; vm_compute; lia |].
    remember (nth 0 Tfib_owned_static (0, 0)) as r eqn:Er. vm_compute in Er. subst r.
    unfold YG0n.in_zr. cbn [fst snd]. lia.
  + exists (nth 3 Tfib_owned_static (0, 0)). split; [apply nth_In; vm_compute; lia |].
    remember (nth 3 Tfib_owned_static (0, 0)) as r eqn:Er. vm_compute in Er. subst r.
    unfold YG0n.in_zr. cbn [fst snd]. lia.
- unfold TFIB_INST, YG0ncf.kInstObjSize. lia.
Qed.

Lemma pf_cells_owned_preset_A : forall B, TfibSyms B -> YG0ncf.pf_cells_owned_t (ci := CfImg_A) B.
Proof.
intros B TS. unfold YG0ncf.pf_cells_owned_t.
split; [exact (pf_cells_static_preset_A B TS) | exact (PresetRelroGeoA.pf_ial_apart_preset_A B TS)].
Qed.
