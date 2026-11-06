(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: GENERATED for omx-clap-core/fuzz_preset's ASan image (ELF sha256 bff8519bbe3ea0e4) by the internal file gen_pins.py: named pins of owned cells that stay unchanged after start-up. Each is a cell of Tfib_const_abs (AR's const law keeps it) and lies inside Tfib_owned_static (no program store reaches it). No instruction of the image stores to either cell (the internal file storescan.py: 0 direct stores, 0 through a pointer loaded from the slot, and no other data word holds either address). *)
(* Generator: tools/startup/gen_pins.py sha256 bccacb86dd704b529160b01f93352cc9d66ee35b6c5481fbab6bd7b91b7937fa; image sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590; A/AF0m.v blob 97f423adf6ebdee1e409e001a5e3cb7acc241b0a. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
Import ListNotations.
Open Scope Z_scope.
Definition A_REAL_MEMCPY : Z := 0xa3e88.       (* __interception::real_memcpy, writable .data, 8 bytes *)
Definition A_GOT_REAL_MEMCPY : Z := 0xa2038.   (* the .got slot holding A_REAL_MEMCPY *)
Definition A_MEMCPY : Z := 0x9b2b4.            (* memcpy: real_memcpy's value *)
(* Membership is decided by SEARCH over the list after vm_compute, never by position: re-sorting or extending
   Tfib_const_abs cannot make these lemmas name a different row (the generator also prints the index, as information). *)
Lemma pin_real_memcpy : In (z8 (ANum A_REAL_MEMCPY) A_MEMCPY) Tfib_const_abs.
Proof. vm_compute; repeat (first [left; reflexivity | right]). Qed.
Lemma pin_got_real_memcpy : In (z8 (ANum A_GOT_REAL_MEMCPY) A_REAL_MEMCPY) Tfib_const_abs.
Proof. vm_compute; repeat (first [left; reflexivity | right]). Qed.
Lemma own_real_memcpy : exists r, In r Tfib_owned_static /\ fst r <= A_REAL_MEMCPY /\ A_REAL_MEMCPY + 8 <= fst r + snd r.
Proof. exists (0xa3d20, 10360). split; [vm_compute; repeat (first [left; reflexivity | right]) | unfold A_REAL_MEMCPY; cbn [fst snd]; lia]. Qed.
Lemma own_got_real_memcpy : exists r, In r Tfib_owned_static /\ fst r <= A_GOT_REAL_MEMCPY /\ A_GOT_REAL_MEMCPY + 8 <= fst r + snd r.
Proof. exists (0xa2030, 56). split; [vm_compute; repeat (first [left; reflexivity | right]) | unfold A_GOT_REAL_MEMCPY; cbn [fst snd]; lia]. Qed.
