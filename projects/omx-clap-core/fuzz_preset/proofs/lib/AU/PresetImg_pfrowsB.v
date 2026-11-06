(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_pfrowsB.v (commit 4d286b2e618d, file sha256 1cd72098ecb6) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 2 list indices re-picked, and 0 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, for a Theorem Labs lane's cf layer round 3 at plugin-hostd/fuzz_reply).
   rule 24: no function proved (kind: image rows; closed facts about reply's image B, fuzz_reply.asan-ubsan, pin
   10ffb5f9202a; no function walk).

   Image B's twin of A/ReplyImg_pfrows.v: the two unit rows round 3's ARcf_nil_init (Reusable/YGcfNilInit.v:100-101)
   takes at the image's symbol facts:
   - errb_ial_apart_preset_B: the layer's errb_ial_apart_t (Reusable/YG0ncf.v:160): the error-message-buffer object
     [cf_errbuf_obj, + 56) lies below the internal allocator's arena (TFIB_IAL_LO) and so outside the arena and its
     flag (TFIB_IAL_FLAG).
   - pf_cells_owned_preset_B: the layer's pf_cells_owned_t (Reusable/YG0ncf.v:207) = pf_cells_static_t /\
     pf_ial_apart_t. The static half is pf_cells_static_preset_B below: the toolname cell lies in the first region of
     Tfib_owned_static, the pfcb cell in the fifth, and both lie outside the instance object [TFIB_INST,
     + kInstObjSize). The arena half is a prior worker's PresetRelroGeoB.pf_ial_apart_preset_B, cited.
   Every bound is a NAME: the CfImg_B fields (B/CfImgB.v), the TfibSyms constants and Tfib_owned_static of B/YF0m.v,
   and YG0ncf.kInstObjSize. The owned regions are computed (vm_compute of nth over Tfib_owned_static), not retyped. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09 YG0f YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0n YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetRelroGeoB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfIalApartPreset.
Open Scope Z_scope.

(* Image B's CfImg for the texts below, as B/CfRBridgeRulesB.v takes it. *)
#[local] Existing Instance CfImg_B.

(* errb_ial_apart_t at TfibSyms. *)
Lemma errb_ial_apart_preset_B : forall B, TfibSyms B -> YG0ncf.errb_ial_apart_t (ci := CfImg_B) B.
Proof.
intros B TS a Ha. rewrite (ts_ial_lo B TS), (ts_ial_hi B TS), (ts_ial_flag B TS).
cbn [cf_errbuf_obj CfImg_B] in Ha. unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG. lia.
Qed.

(* pf_cells_static_t at TfibSyms: the toolname cell in owned region 0, the pfcb cell in owned region 4. *)
Lemma pf_cells_static_preset_B : forall B, TfibSyms B -> YG0ncf.pf_cells_static_t (ci := CfImg_B) B.
Proof.
intros B TS a Ha. rewrite (ts_owned B TS), (ts_inst B TS).
cbn [cf_toolname_cell cf_pfcb_cell CfImg_B] in Ha. split.
- apply Exists_exists. destruct Ha as [Ha | Ha].
  + exists (nth 0 Tfib_owned_static (0, 0)). split; [apply nth_In; vm_compute; lia |].
    remember (nth 0 Tfib_owned_static (0, 0)) as r eqn:Er. vm_compute in Er. subst r.
    unfold YG0n.in_zr. cbn [fst snd]. lia.
  + exists (nth 3 Tfib_owned_static (0, 0)). split; [apply nth_In; vm_compute; lia |].
    remember (nth 3 Tfib_owned_static (0, 0)) as r eqn:Er. vm_compute in Er. subst r.
    unfold YG0n.in_zr. cbn [fst snd]. lia.
- unfold TFIB_INST, YG0ncf.kInstObjSize. lia.
Qed.

(* pf_cells_owned_t at TfibSyms: the static half above and the arena half of PresetRelroGeoB. *)
Lemma pf_cells_owned_preset_B : forall B, TfibSyms B -> YG0ncf.pf_cells_owned_t (ci := CfImg_B) B.
Proof.
intros B TS. unfold YG0ncf.pf_cells_owned_t.
split; [exact (pf_cells_static_preset_B B TS) | exact (CfIalApartPreset.pf_ial_apart_B B TS)].
Qed.
