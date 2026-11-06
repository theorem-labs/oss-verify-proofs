(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1dk X1dg X1ck.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cells_bytes_f32 : forall ws, cells_bytes (f32 ws) = u32s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. rewrite f32_cons. cbn [cells_bytes cbytes u32s]. rewrite IH. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma u32arr_of_f32 : forall m A ws, rw_cells segs m A (f32 ws) -> u32arr segs m A ws.
Proof.
intros m A ws [[Hwf Hb] Hw]. rewrite cells_bytes_f32 in Hb. rewrite cells_size_f32 in Hw. split; [exact Hb|].
replace (4 * Z.of_nat (length ws))%Z with (Z.of_nat (4 * length ws)) by lia. exact Hw.
Qed.

Lemma f32_of_u32arr : forall m A ws, u32arr segs m A ws -> rw_cells segs m A (f32 ws).
Proof.
intros m A ws [Hb Hw]. split; [split; [apply cells_wf_f32| rewrite cells_bytes_f32; exact Hb]|].
rewrite cells_size_f32. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact Hw.
Qed.

Lemma u32arr_read_nth : forall m A ws (i : Z) a,
u32arr segs m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 4 * i) ->
ov_read_bytes segs m a 4 = Some (le4 (nth (Z.to_nat i) ws (Z_to_bv 64 0))).
Proof.
intros m A ws i a H Hi Ha. eapply u32arr_read; [exact H| apply nth_error_nth'; lia| lia| exact Ha].
Qed.
End WithSegs.
