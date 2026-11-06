(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec SeqExec StepTac Hoare WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocKitOL.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac.
Import ListNotations.
Open Scope bv_scope.

Lemma rl_fetch_OL : forall {RL : Reloc} {RC : RelocCodeOL RL} b c (w : bv 32),
  code_has canon_code_OL b c (bv_unsigned w) = true -> fetch_word rl_segs (rl (rl_delta b) c) = Some w.
Proof. intros RL RC b c w H. exact (code_sound rl_segs rl_delta canon_code_OL b c w rl_code_ol_ok H). Qed.

(* [comment removed for export] *)
Ltac rl_ret_ok_try_OL RL b c off :=
  let c0 := eval vm_compute in (c + off)%Z in
  let z0 := eval vm_compute in (code_lookup canon_code_OL b c0) in
  lazymatch z0 with
  | Some ?w0 => exact (rl_ret_ok_near _ _ c0 c _ (rl_fetch_OL b c0 (Z_to_bv 32 w0) ltac:(vm_cast_no_check (@eq_refl bool true))) eq_refl)
  | None =>          (* [comment removed for export] *)
      let r := eval vm_compute in (site_find canon_sites_OL 0%nat c0) in
      lazymatch r with
      | Some (?i, _, _) =>
          let s := eval vm_compute in (nth_error canon_sites_OL i) in
          lazymatch s with
          | Some ?cs => exact (rl_ret_ok_near _ _ c0 c _ (rl_site_F_OL i cs (@eq_refl _ (Some cs))) eq_refl)
          end
      end
  end.

Ltac rl_ret_ok_OL :=
  lazymatch goal with
  | |- ret_ok (Z_to_bv 64 (?c + @rl_delta ?RL ?b)) => change (ret_ok (rl (@rl_delta RL b) c)); rl_ret_ok_OL
  | |- ret_ok (rl (@rl_delta ?RL ?b) ?c) =>
      first [ rl_ret_ok_try_OL RL b c 0%Z | rl_ret_ok_try_OL RL b c (-4)%Z | rl_ret_ok_try_OL RL b c 4%Z | rl_ret_ok_try_OL RL b c (-8)%Z
            | rl_ret_ok_try_OL RL b c 8%Z | rl_ret_ok_try_OL RL b c (-12)%Z | rl_ret_ok_try_OL RL b c 12%Z | rl_ret_ok ]
  end.

Ltac rl_vmc_OL :=
  first [ rl_ret_ok_OL
        | lazymatch goal with
          | |- context [@rl_delta _ _] => fail 1 "rl_vmc_OL: the goal mentions a delta (no computation on open terms)"
          | _ => vm_compute; reflexivity
          end ].
