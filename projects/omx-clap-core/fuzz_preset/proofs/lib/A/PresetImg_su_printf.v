(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_su_printf.v (commit eb934de95d13, blob 51d6ce353d3f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 2 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0c YK09 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB01 AB03.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

Definition presetA_printf_cb_cell : Z := 0x13cbd0.

Definition presetA_printf_cb_fn : Z := 0x55d0c.

Lemma presetA_su_printf_handoff_all : forall s, In s AB01.HS_tfib_list ->
  In (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8 (ELit presetA_printf_cb_fn))
     (s_know (a_ss s)).
Proof.
  assert (H : forallb (kn_mem (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8
                                       (ELit presetA_printf_cb_fn)))
                AB01.HS_tfib_list = true) by (vm_compute; reflexivity).
  intros s Hs. exact (kn_mem_In _ s (proj1 (forallb_forall _ _) H s Hs)).
Qed.

Corollary presetA_su_printf_handoff : forall h s, AB01.HS_tfib h = Some s ->
  In (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8 (ELit presetA_printf_cb_fn))
     (s_know (a_ss s)).
Proof. intros h s H. exact (presetA_su_printf_handoff_all s (AB01.HS_tfib_In h s H)). Qed.

Lemma presetA_su_printf_join :
  In (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8 (ELit presetA_printf_cb_fn))
     (s_know (a_ss AB03.JS_tfib_band)).
Proof.
  assert (H : kn_mem (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8 (ELit presetA_printf_cb_fn))
                AB03.JS_tfib_band = true) by (vm_compute; reflexivity).
  exact (kn_mem_In _ _ H).
Qed.

Theorem presetA_su_printf :
  (forall s, In s AB01.HS_tfib_list ->
     In (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8 (ELit presetA_printf_cb_fn))
        (s_know (a_ss s)))
  /\ In (KWord {| a_base := ELit 0; a_off := presetA_printf_cb_cell |} 8 (ELit presetA_printf_cb_fn))
        (s_know (a_ss AB03.JS_tfib_band)).
Proof. exact (conj presetA_su_printf_handoff_all presetA_su_printf_join). Qed.

About presetA_su_printf_handoff_all.
About presetA_su_printf_handoff.
About presetA_su_printf_join.
About presetA_su_printf.
Print Assumptions presetA_su_printf.
