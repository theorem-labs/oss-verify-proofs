(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGi8.v (a working branch 84ee52cd012, file sha256 0629b0c04da0) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at d1f93c50c87) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc 0474699fc83547e0 (a working branch 83209f9d9cd8), --assume-source, --resolve the internal file resolve-102.txt (5 lines name this file); 0 numerals changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGi6 AGi7.
Import ListNotations. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
Lemma sweep_hi : sweep clz_okb (Z.to_nat 32771) 32768 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* The pages of a secondary map up to AGi9.SEC_NMAX + 8192 bytes: 65539 .. 262142. *)
Lemma sweep_hi2 : sweep clz_okb (Z.to_nat 65532) 65539 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma sweep_hi3 : sweep clz_okb (Z.to_nat 131072) 131071 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma clz_index : forall p, 18 <= p <= 262142 -> Z.lxor (clzS (4096 * p)) 63 = Z.log2 p + 12.
Proof.
intros p Hp. destruct (Z_lt_le_dec p 32768) as [Hlt|Hge];
[|destruct (Z_lt_le_dec p 65539) as [Hlt2|Hge2]; [|destruct (Z_lt_le_dec p 131071) as [Hlt3|Hge3]]].
- pose proof (sweep_val _ _ _ sweep_lo p) as H. rewrite Z2Nat.id in H by (clear; lia). specialize (H ltac:(lia)).
cbv beta in H. apply Z.eqb_eq in H. exact H.
- pose proof (sweep_val _ _ _ sweep_hi p) as H. rewrite Z2Nat.id in H by (clear; lia). specialize (H ltac:(lia)).
cbv beta in H. apply Z.eqb_eq in H. exact H.
- pose proof (sweep_val _ _ _ sweep_hi2 p) as H. rewrite Z2Nat.id in H by (clear; lia). specialize (H ltac:(lia)).
cbv beta in H. apply Z.eqb_eq in H. exact H.
- pose proof (sweep_val _ _ _ sweep_hi3 p) as H. rewrite Z2Nat.id in H by (clear; lia). specialize (H ltac:(lia)).
cbv beta in H. apply Z.eqb_eq in H. exact H.
Qed.
