(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BIface InfBBase InfBTables InfB_w7tab InfB_w7tab16.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive ltk : Set := LTDyn (o : Z) | LTFix.
Definition lt_TA (S : Z) (k : ltk) : Z := match k with LTDyn o => S + 1384 + 4 * o | LTFix => 149600 end.
Definition lt_rd (cf : Z -> Z) (k : ltk) : Z -> Z := match k with LTDyn o => rdc cf (CDyn o) | LTFix => rdc (fun _ => 0) CLenfix end.
Definition lt_XT (S : Z) (k : ltk) : Z := match k with LTDyn _ => S | LTFix => 149600 end.
Definition lt_NS (k : ltk) : Z := match k with LTDyn _ => 897 | LTFix => 256 end.
Definition lt_ok (k : ltk) (nd : Z) : Prop := match k with LTDyn o => 0 <= o /\ 0 <= nd /\ o + nd <= 1444 | LTFix => nd = 512 end.

Section CANSEC1. Context {rc : runConstT}.
Lemma lt_facts : forall (RNG : footprint) (m : amem) (S : Z) (cf : Z -> Z) (k : ltk) (nd : Z),
  lt_ok k nd -> f32arr bsegs m (S + 1384) 1444 cf -> (forall i, 0 <= i < N_CODES -> 0 <= cf i < 4294967296) -> mem_inv bsegs m ->
  shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0) ->
  shadow_bytes m 2147469580 2147469836 (fun _ => 0) ->
  S mod 8 = 0 -> rng RNG S 7176 -> rng RNG (Z.shiftr S 3 + 2147450880) 897 -> rng_aimg RNG -> rng_aimg_sh RNG -> ablk S (S + 7176) ->
  dtab m (lt_TA S k) nd (lt_rd cf k) /\ dtab16 m (lt_TA S k) nd (lt_rd cf k)
  /\ shadow_bytes m (Z.shiftr (lt_XT S k) 3 + 2147450880) (Z.shiftr (lt_XT S k) 3 + 2147450880 + lt_NS k) (fun _ => 0)
  /\ lt_XT S k mod 8 = 0 /\ 0 <= lt_XT S k /\ lt_XT S k <= lt_TA S k /\ lt_TA S k + 4 * nd <= lt_XT S k + 8 * lt_NS k
  /\ rng RNG (Z.shiftr (lt_XT S k) 3 + 2147450880) (lt_NS k) /\ rng RNG (lt_TA S k) (4 * nd) /\ 0 < lt_TA S k /\ lt_TA S k + 4 * nd < 140737488355328.
Proof.
  intros RNG m S cf k nd LOK CODES CFR MI SHS SHLF S8 RS RSS RI RISH SB.
  pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). unfold AIMG_HI in SB1. change (2 ^ 47) with 140737488355328 in SB4.
  destruct k as [o|]; cbn [lt_TA lt_rd lt_XT lt_NS lt_ok] in *.
  - destruct LOK as (O0 & ND0 & OND).
    split; [apply dtab_dyn; [exact CODES| exact CFR| exact O0| exact ND0| exact OND]|].
    split; [apply dtab16_dyn; [exact CODES| exact CFR| exact O0| exact ND0| exact OND]|].
    split; [exact SHS|]. split; [exact S8|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact RSS|]. split; [eapply rng_sub'; [exact RS| lia]|]. split; lia.
  - subst nd.
    split; [apply dtab_lenfix; exact MI|]. split; [apply dtab16_lenfix; exact MI|].
    split; [exact SHLF|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [eapply rng_sub'; [exact RISH| cbv; split; discriminate]|].
    split; [eapply rng_sub'; [exact RI| cbv; split; discriminate]|]. split; lia.
Qed.
End CANSEC1.
