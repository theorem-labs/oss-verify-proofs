(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlParser.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AYajl_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition yphi_shape_stmt (Y : ay_params) : Prop :=
  forall st len u1 u2 d bs1 bs2, y_phi_buf Y (mkBuf st len u1 d bs1) = y_phi_buf Y (mkBuf st len u2 d bs2).

Definition yphi_first_stmt (Y : ay_params) : Prop :=
  forall (d : yptr) used bs,
    y_acharge Y YAJL_BUF_INIT_SIZE + y_phi_buf Y (mkBuf BS_ok YAJL_BUF_INIT_SIZE used (Some d) bs) <= y_phi_buf Y (mkBuf BS_ok 0 used None bs).

Definition yphi_grow_stmt (Y : ay_params) : Prop :=
  forall len used want (d : yptr) bs,
    0 <= used < len -> len < 2^31 -> 0 < want -> used + want < 2^28 -> ens_need_loop ENS_FUEL want len used <> len ->
    y_acharge Y (ens_need_loop ENS_FUEL want len used) + y_free_cost Y + y_phi_buf Y (mkBuf BS_ok (ens_need_loop ENS_FUEL want len used) used (Some d) bs)
      <= y_phi_buf Y (mkBuf BS_ok len used (Some d) bs).

Definition yphi_err_stmt (Y : ay_params) : Prop := y_phi_buf Y (mkBuf BS_overflow 0 0 None []) = 0.

(* [comment removed for export] *)
Definition yphi_hand_free_stmt (Y : ay_params) : Prop :=
  forall h L, y_free_cost Y + y_phi_buf Y (h_decbuf h) + (y_free_cost Y + y_phi_buf Y (lx_buf (h_lexer h))) + y_free_cost Y <= y_phi_hand Y h L.

(* [comment removed for export] *)
Definition yphi_hand_lex1_stmt (Y : ay_params) : Prop :=
  forall h L, y_phi_buf Y (lx_buf (h_lexer h)) <= y_phi_hand Y h L.
Definition yphi_hand_lex2_stmt (Y : ay_params) : Prop :=
  forall h L lx' off', y_phi_hand Y (h_set_lex_off h lx' off') L - y_phi_buf Y (lx_buf lx') <= y_phi_hand Y h L - y_phi_buf Y (lx_buf (h_lexer h)).

(* [comment removed for export] *)
Definition yalloc_hand (hb lb db sb : yptr) (bb : nat) : yhandle :=
  mkHandle hb lb (mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1) None 0 db ybuf_zero [ST_start] 128 (Some sb).
Definition yphi_new_alloc_stmt (Y : ay_params) : Prop :=
  forall L (hb lb db sb : yptr) (bb : nat), 0 <= L ->
    y_acharge Y 104 + y_acharge Y 48 + 2 * y_acharge Y 32 + y_acharge Y 128 + 4 * y_free_cost Y + 2 * y_phi_buf Y ybuf_zero
    + y_phi_hand Y (yalloc_hand hb lb db sb bb) L <= y_phi_new Y L.

(* [comment removed for export] *)
Definition yphi_hand_shape_stmt (Y : ay_params) : Prop :=
  forall h1 h2 L, h_lexer h1 = h_lexer h2 -> h_decbuf h1 = h_decbuf h2 -> h_bytesConsumed h1 = h_bytesConsumed h2 ->
    h_used h1 = h_used h2 -> h_stack_size h1 = h_stack_size h2 -> h_stack_blk h1 = h_stack_blk h2 ->
    y_phi_hand Y h1 L = y_phi_hand Y h2 L.

(* [comment removed for export] *)
Definition ypushc (Y : ay_params) (size : Z) : Z := y_acharge Y (size + YAJL_BS_INC) + y_free_cost Y.
Definition yphi_hand_split_stmt (Y : ay_params) (phr : Z -> Z -> Z -> Z -> Z) : Prop :=
    (forall h L, y_phi_hand Y h L = y_phi_buf Y (lx_buf (h_lexer h)) + y_phi_buf Y (h_decbuf h) + phr (h_bytesConsumed h) (h_used h) (h_stack_size h) L)
    /\ (forall c u s L, 0 <= phr c u s L)
    /\ (forall c c' u s L, c <= c' -> phr c' u s L <= phr c u s L)                                   (* [comment removed for export] *)
    /\ (forall c u s L, 0 < u -> phr c (u - 1) s L <= phr c u s L)                                   (* [comment removed for export] *)
    /\ (forall c c' u s L, 0 <= c -> c < c' <= L -> 0 <= s -> u < s -> phr c' (u + 1) s L <= phr c u s L)      (* [comment removed for export] *)
    /\ (forall c c' u s L, 0 <= c -> c < c' <= L -> 0 <= s -> u = s ->                               (* [comment removed for export] *)
           ypushc Y s + phr c' u (s + YAJL_BS_INC) 0 <= phr c u s L                                   (* [comment removed for export] *)
        /\ phr c' (u + 1) (s + YAJL_BS_INC) L + ypushc Y s <= phr c u s L + y_arefund Y s)            (* [comment removed for export] *)
    /\ (forall c c' u s L, 0 <= c' -> 0 <= L -> phr c' u s 0 <= phr c u s L).                           (* [comment removed for export] *)
End RC__1.
