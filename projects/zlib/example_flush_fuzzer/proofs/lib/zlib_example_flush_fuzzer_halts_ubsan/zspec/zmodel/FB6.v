(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate
  DeflateInvKeep SendModel DeflFastModel OverlayFBS RefFlushBlk11 RefFlushPend1 RefDeflFastOk DeflateInv DeflInvFbo DeflInvMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition FB6 (s : deflate_state) (buf : option Z) (len last : Z) : Prop :=
  fb_safe s buf len last /\ BINV (ds_lit_bufsize s * 4) s /\ cty s /\ 512 <= ds_lit_bufsize s
  /\ tfb_keeps s (tr_flush_block s buf len last) /\ len < 2 ^ 32
  /\ match buf with Some off => len <> 0 -> off + len <= 2 * ds_w_size s | None => True end
  /\ (exists syms, FBS syms s buf len last).

Theorem FB6_of_drun : forall rm hb fz ws hs PBL ILEN OCAP tot0 s last,
  0 <= rm -> 2048 <= PBL -> drunR rm hb fz ws hs PBL ILEN OCAP tot0 s -> (last = 0 \/ last = 1) ->
  FB6 s (fbo_buf s) (fbo_len s) last.
Proof.
  intros rm hb fz ws hs PBL ILEN OCAP tot0 s last Hrm HPBL D Hl.
  pose proof (fbo_run ws hs PBL ILEN OCAP tot0 tfb_safe_holds tfb_room_holds HPBL rm hb fz s last Hrm D Hl) as [OK _].
  destruct OK as (LZ & BS & TFB & _). destruct TFB as (B & FS & K & L32 & BUF).
  pose proof D as [[C I CL Ews Ehs Epbl _ _ _ _] _ _].
  unfold FB6. rewrite Epbl, Ews. split; [exact FS|]. split; [exact B|]. split; [exact (di_cty _ _ _ _ I)|]. split; [lia|].
  split; [exact K|]. split; [exact L32|]. split; [exact BUF|].
  exact (drun_FBS rm hb fz ws hs PBL ILEN OCAP tot0 s last Hrm D Hl).
Qed.
