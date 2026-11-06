(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X07z X0b1.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X11l.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition gcqb_bytes : list byte := match image_bytes bsegs A_gc_quant_bound 64 with Some b => b | None => [] end.

Lemma sb_gcqb_at : forall m, mem_inv bsegs m -> exists tab : list word, length tab = 16%nat /\ ro_cells bsegs m A_gc_quant_bound (f32 tab).
Proof.
intros m MI.
assert (L : length gcqb_bytes = (4 * 16)%nat) by (vm_compute; reflexivity).
pose proof (ro_cells_image bsegs m A_gc_quant_bound gcqb_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_gc_quant_bound; lia)
ltac:(rewrite L; unfold A_gc_quant_bound; cbn; lia)) as R.
destruct (bytes_are_f32 16 gcqb_bytes L) as (ws & Lws & E).
exists ws. split; [exact Lws|].
destruct R as [_ B]. split; [apply cells_wf_f32|]. rewrite E. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition gcqb_bytes : list byte := match image_bytes asegs A_gc_quant_bound 64 with Some b => b | None => [] end.

Lemma sb_gcqb_at : forall m, mem_inv asegs m -> exists tab : list word, length tab = 16%nat /\ ro_cells asegs m A_gc_quant_bound (f32 tab).
Proof.
intros m MI.
assert (L : length gcqb_bytes = (4 * 16)%nat) by (vm_compute; reflexivity).
pose proof (ro_cells_image asegs m A_gc_quant_bound gcqb_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold A_gc_quant_bound; lia)
ltac:(rewrite L; unfold A_gc_quant_bound; cbn; lia)) as R.
destruct (bytes_are_f32 16 gcqb_bytes L) as (ws & Lws & E).
exists ws. split; [exact Lws|].
destruct R as [_ B]. split; [apply cells_wf_f32|]. rewrite E. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
