(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes Image ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AObj ItAKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BIface InfBTables U2BIface_fit2_draft.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma fws_window : forall f n o k, (o + k <= n)%nat ->
  fws f n = fws f o ++ fws (fun i => f (Z.of_nat o + i)) k ++ skipn (o + k) (fws f n).
Proof.
  intros f n o k H. apply nth_error_ext'.
  - rewrite !length_app, length_skipn, !fws_length. lia.
  - intros j Hj. rewrite fws_length in Hj. rewrite fws_nth by exact Hj.
    destruct (Nat.lt_ge_cases j o) as [L|G].
    + rewrite nth_error_app1 by (rewrite fws_length; exact L). rewrite fws_nth by exact L. reflexivity.
    + rewrite nth_error_app2 by (rewrite fws_length; exact G). rewrite fws_length.
      destruct (Nat.lt_ge_cases (j - o) k) as [L2|G2].
      * rewrite nth_error_app1 by (rewrite fws_length; exact L2). rewrite fws_nth by exact L2.
        replace (Z.of_nat o + Z.of_nat (j - o)) with (Z.of_nat j) by lia. reflexivity.
      * rewrite nth_error_app2 by (rewrite fws_length; exact G2). rewrite fws_length, nth_error_skipn.
        replace (o + k + (j - o - k))%nat with j by lia. rewrite fws_nth by exact Hj. reflexivity.
Qed.

Notation amem := (word -> option byte).
Section CANSEC1. Context {rc : runConstT}.

Lemma ctab_of_codes : forall (RNG : footprint) (m : amem) (S o nd : Z) (cf : Z -> Z),
  f32arr bsegs m (S + 1384) 1444 cf -> (forall i, 0 <= i < 1444 -> 0 <= cf i < 4294967296) ->
  0 <= o -> 0 <= nd -> o + nd <= 1444 -> S mod 8 = 0 -> 0 < S -> S + 7176 <= 2 ^ 47 ->
  state_sh RNG m S ->
  ctab_at RNG m (S + 1384 + 4 * o) nd (fun i => cf (o + i)).
Proof.
  intros RNG m S o nd cf [HB _] HR O0 N0 ON S8 S0 SL (SHS & RS & RSS).
  unfold ctab_at.
  split.
  { rewrite (fws_window cf 1444 (Z.to_nat o) (Z.to_nat nd) ltac:(lia)) in HB. rewrite !u32s_app in HB.
    apply bytes_at_app in HB. destruct HB as [_ HB]. apply bytes_at_app in HB. destruct HB as [HB _].
    rewrite u32s_length, fws_length in HB.
    replace (S + 1384 + Z.of_nat (4 * Z.to_nat o)) with (S + 1384 + 4 * o) in HB by lia.
    replace (fws (fun i => cf (Z.of_nat (Z.to_nat o) + i)) (Z.to_nat nd)) with (fws (fun i => cf (o + i)) (Z.to_nat nd)) in HB; [exact HB|].
    unfold fws. apply map_ext. intros a. rewrite Z2Nat.id by lia. reflexivity. }
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact N0|].
  split; [eapply rng_sub'; [exact RS| lia]|].
  split; [intros i Hi; apply HR; lia|].
  exists (Z.shiftr S 3 + 2147450880), (Z.shiftr S 3 + 2147450880 + 897).
  split; [exact SHS|]. split; [replace (Z.shiftr S 3 + 2147450880 + 897 - (Z.shiftr S 3 + 2147450880)) with 897 by lia; exact RSS|].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  split; [Z.div_mod_to_equations; lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma fws_lenfix : fws (arr_get lenfix_a) 512 = zw lenfix_l.
Proof. vm_compute. reflexivity. Qed.
Lemma fws_distfix : fws (arr_get distfix_a) 32 = zw distfix_l.
Proof. vm_compute. reflexivity. Qed.

Lemma ctab_lenfix : forall (RNG : footprint) (m : amem),
  mem_inv bsegs m -> rng_aimg RNG -> rng_aimg_sh RNG -> shadow_bytes m 2147469580 2147469836 (fun _ => 0) ->
  ctab_at RNG m 149600 512 (arr_get lenfix_a).
Proof.
  intros RNG m MI RI RISH SH. unfold ctab_at.
  split. { change (Z.to_nat 512) with 512%nat. rewrite fws_lenfix. exact (lenfix_bytes m MI). }
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [eapply rng_sub'; [exact RI| lia]|].
  split; [intros i Hi; destruct (lenfix_nth i Hi) as [_ R]; exact R|].
  exists 2147469580, 2147469836. split; [exact SH|]. split; [eapply rng_sub'; [exact RISH| lia]|].
  split; [lia|]. split; [lia|]. split; [vm_compute; discriminate|]. vm_compute. reflexivity.
Qed.

Lemma ctab_distfix : forall (RNG : footprint) (m : amem),
  mem_inv bsegs m -> rng_aimg RNG -> rng_aimg_sh RNG -> shadow_bytes m 2147469900 2147469916 (fun _ => 0) ->
  ctab_at RNG m 152160 32 (arr_get distfix_a).
Proof.
  intros RNG m MI RI RISH SH. unfold ctab_at.
  split. { change (Z.to_nat 32) with 32%nat. rewrite fws_distfix. exact (distfix_bytes m MI). }
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [eapply rng_sub'; [exact RI| lia]|].
  split; [intros i Hi; destruct (distfix_nth i Hi) as [_ R]; exact R|].
  exists 2147469900, 2147469916. split; [exact SH|]. split; [eapply rng_sub'; [exact RISH| lia]|].
  split; [lia|]. split; [lia|]. split; [vm_compute; discriminate|]. vm_compute. reflexivity.
Qed.

End CANSEC1.
