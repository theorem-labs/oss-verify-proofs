(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Plain Require PImgRun.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Spec S0StdioDefs S0ExitBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac Image ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require Import S0SoDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition so_ok {RCa1 : RunCtx}  (M : word -> option byte) (k : nat) : Prop := (k = 0%nat /\ so_pristine M) \/ so_wmode M k.

Lemma so_ok_exit {RCa1 : RunCtx}  : forall M k can, so_ok M k -> S0StdioDefs.ssp_cells M can ->
   (k = 0%nat /\ exists wp1 rp1, S0ExitBase.file_clean M 0x1f8b0 wp1 rp1)
   \/ (exists (wb wp : Z) (bufp bufsz rp1 : word), S0StdioDefs.stdout_pending M wb wp bufp bufsz rp1 can (Spec.zero_lines k)).
Proof.
  intros M k can [[-> P] | W] SSP.
  - left. split; [reflexivity | apply so_pristine_clean; exact P].
  - destruct k as [|k].
    + left. split; [reflexivity | apply so_wmode_clean; exact W].
    + right. do 5 eexists. apply (so_wmode_pending M (S k) can W ltac:(lia) SSP).
Qed.

Lemma so_ok_frame {RCa1 : RunCtx}  : forall M M' k, so_ok M k ->
  (forall a, 0x1f8b0 <= a < 0x1f998 \/ 0x501d0 <= a < 0x505d8 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> so_ok M' k.
Proof.
  intros M M' k [[-> P] | W] AG.
  - left. split; [reflexivity|]. eapply so_pristine_frame; [exact P | exact AG].
  - right. eapply so_wmode_frame; [exact W | exact AG].
Qed.

Lemma mem_inv_none {RCa1 : RunCtx}  : forall (M : word -> option byte) i, mem_inv (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments psegs rc_inp rc_sp rc_mb) M -> 0x10000 <= i < 0x1e000 -> M (Z_to_bv 64 i) = None.
Proof.
  intros M i MI Hi. destruct (M (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (MI _ _ E) as X.
  rewrite PImgRun.run_p_ro_addr_in, p_ro_addr, unsigned_lit in X by (rewrite ?unsigned_lit by lia; lia).
  exfalso. apply andb_false_iff in X. destruct X as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia.
Qed.
