(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_ctrl_parseF.v, with its module paths, module names, addresses and numbers changed; 5648 of its 6995 lines of code are new or changed and 2192 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_ctrl_parseF.v, with its module paths and module names changed; 15 of its 30 lines of code are new or changed and 6980 lines of the source are left out. *)
(* lib/B/Prog/C_reac_ctrl_parseOn.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0), route (C) (a Theorem Labs lane 09:20Z): the
   general lemmas that the re-based stretch of reac_ctrl_parse (lib/B/Prog/C_reac_ctrl_parseLib.v, Sections SetupFB and
   RoFB) uses with its shadow hypothesis `lib.B.ShadowRwOn.shadow_rw_on P m` in place of the universal form
   lib.B.AsanRT.shadow_rw (every shadow byte).  reac_ctrl_parseF.v (ctrl's accepted run) is unchanged apart from comment text; each
   lemma here is the shadow_rw_on twin of one of its general lemmas, with the region guard P carried through (the
   originals argue per address), or a small range fact about lib.B.Prog.sh_word_on.sh_word_on:
     shadow_rw_on_mono_mem  <- lib.B.Prog.reac_ctrl_parseF.shadow_rw_mono (wmono + rd_mono, reac_ctrl_parseF.v:340)
     shadow16_stk_on        <- lib.B.Prog.reac_ctrl_parseF.shadow16_stk (the frame's 16 shadow bytes, :695)
     sh_word_on_frame16     the 16 shadow bytes [fra / 8 + ASAN_K, + 16) of a 128-byte frame at fra are inside the
                            aligned shadow-word span sh_word_on fra 128.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_parseF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.Prog.rng_asan B.Prog.sh_word_on.
Local Open Scope Z_scope.

(* lib.B.Prog.reac_ctrl_parseF.shadow_rw_mono for a region P: every shadow byte of P present and readable in m stays so
   in m'. *)
Lemma shadow_rw_on_mono_mem : forall (P : Z -> Prop) m m', lib.B.ShadowRwOn.shadow_rw_on P m ->
  wmono rsegs m m' -> rd_mono m m' -> lib.B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P m m' H Hw Hr a Hp Ha. destruct (H a Hp Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

(* lib.B.Prog.reac_ctrl_parseF.shadow16_stk for a region P that holds the frame's 16 shadow bytes. *)
Lemma shadow16_stk_on : forall (P : Z -> Prop) mc fra,
  lib.B.ShadowRwOn.shadow_rw_on P mc ->
  (forall a, fra / 8 + ASAN_K <= a < fra / 8 + ASAN_K + 16 -> P a) ->
  0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
  2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
  stk rsegs mc (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16).
Proof.
  intros P mc fra SR HP H0 HFRA SHlo SHhi. split; [lia|]. split; [lia|].
  intros a Ha. apply SR; [apply HP; lia|]. replace a with (fra / 8 + ASAN_K + (a - (fra / 8 + ASAN_K))) by lia.
  apply frame_shadow_in; [exact H0 | exact HFRA | exact SHlo | exact SHhi | lia].
Qed.

(* The frame's 16 shadow bytes, at the addresses the run forms (fra / 8 + ASAN_K + i), lie in the aligned shadow-word
   span of its 128 bytes: sh_al8_lo fra <= fra / 8 + ASAN_K and fra / 8 + ASAN_K + 15 <= shadow_addr (fra + 127). *)
Lemma sh_word_on_frame16 : forall fra a, fra / 8 + ASAN_K <= a < fra / 8 + ASAN_K + 16 ->
  lib.B.Prog.sh_word_on.sh_word_on fra 128 a.
Proof.
  intros fra a Ha. unfold lib.B.Prog.sh_word_on.sh_word_on, lib.B.Prog.rng_asan.sh_al8_lo,
    lib.B.Prog.rng_asan.sh_al8_hi, shadow_addr.
  split; [lia|]. unfold ASAN_K in *. Z.div_mod_to_equations. lia.
Qed.
