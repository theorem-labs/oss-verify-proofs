(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re X1od
X1r8 X1nu X1ob X1o3 X1o0 X1ny X1o2 X1o1.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.

Lemma pm_granule_step : forall {ptr ptr'} (f : ptr -> ptr') (h : hstate ptr) hdr, granule_step (pm_h f h) hdr = granule_step h hdr.
Proof. reflexivity. Qed.
#[global] Hint Rewrite @pm_granule_step : erw.

Section HarnessRel.
Variable sel : option bool.
Variable X : list event -> Prop.
Context {St ptr : Type}.
Variable K : St -> Model -> Prop.
Local Notation REL := (X1o3.REL sel X K).
Local Hint Extern 0 (Erasable ptr) => exact (Er_ptr ptr) : typeclass_instances.

Variable lib_malloc : Z -> M St (option ptr).
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.
Variable bits_unpack_unsigned : bits_st ptr -> Z -> M St (Z * bits_st ptr).
Variable bits_peek : bits_st ptr -> M St (Z * bits_st ptr).
Variable bits_advance : bits_st ptr -> Z -> M St (bits_st ptr).
Variable bits_remaining : bits_st ptr -> M St Z.
Hypothesis Hmal : forall n, REL erase (lib_malloc n) (p_malloc n).
Hypothesis Hcal : forall m n, REL erase (lib_calloc m n) (p_calloc m n).
Hypothesis Hrea : forall p p' n, REL erase (lib_realloc p n) (p_realloc p' n).
Hypothesis Hfree : forall p p', REL erase (lib_free p) (p_free p').
Hypothesis Hnot : forall msg, REL erase (spx_notify msg) (p_notify msg).
Hypothesis Hwarn : forall msg, REL erase (spx_warning msg) (p_warning msg).
Local Notation pu := (bits_unpack_unsigned_M (St:=pst) (ptr:=unit)).
Local Notation pp := (bits_peek_M (St:=pst) (ptr:=unit)).
Local Notation pa := (bits_advance_M (St:=pst) (ptr:=unit)).
Local Notation pr := (bits_remaining_M (St:=pst) (ptr:=unit)).
Hypothesis Hbu : forall b n, REL erase (bits_unpack_unsigned b n) (pu (erase b) n).
Hypothesis Hbp : forall b, REL erase (bits_peek b) (pp (erase b)).
Hypothesis Hba : forall b n, REL erase (bits_advance b n) (pa (erase b) n).
Hypothesis Hbr : forall b, REL erase (bits_remaining b) (pr (erase b)).

Local Notation rops f := (f lib_malloc lib_calloc lib_realloc lib_free spx_notify spx_warning bits_unpack_unsigned bits_peek bits_advance bits_remaining).
Local Notation pops f := (f p_malloc p_calloc p_realloc p_free p_notify p_warning pu pp pa pr).

Lemma REL_cleanup : forall h, REL erase (cleanup lib_free h) (cleanup p_free (erase h)).
Proof. intros h. unfold cleanup, h_decoder_destroy. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (cleanup _ _) _) => apply REL_cleanup : rel.

Lemma REL_process_header : forall h pdata bytes,
REL erase (process_header lib_calloc lib_free spx_notify h pdata bytes) (process_header p_calloc p_free p_notify (erase h) pdata bytes).
Proof. intros h pdata bytes. unfold process_header, h_decoder_init, h_decoder_destroy. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (process_header _ _ _ _ _ _) _) => apply REL_process_header : rel.

Lemma REL_decode_loop : forall n st b,
REL erase (decode_loop spx_notify bits_unpack_unsigned bits_peek bits_advance bits_remaining n st b)
(decode_loop p_notify pu pp pa pr n (erase st) (erase b)).
Proof. induction n as [|n IH]; intros st b; cbn [decode_loop]; unfold h_decode; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (decode_loop _ _ _ _ _ _ _ _) _) => apply REL_decode_loop : rel.

Lemma REL_packet_loop : forall fuel h pn,
REL erase (packet_loop lib_calloc lib_realloc lib_free spx_notify spx_warning bits_unpack_unsigned bits_peek bits_advance bits_remaining fuel h pn)
(packet_loop p_calloc p_realloc p_free p_notify p_warning pu pp pa pr fuel (erase h) pn).
Proof. induction fuel as [|fuel IH]; intros h pn; cbn [packet_loop]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (packet_loop _ _ _ _ _ _ _ _ _ _ _ _) _) => apply REL_packet_loop : rel.

Lemma REL_page_loop : forall fuel h,
REL erase (rops page_loop fuel h) (pops page_loop fuel (erase h)).
Proof. induction fuel as [|fuel IH]; intros h; cbn [page_loop]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (page_loop _ _ _ _ _ _ _ _ _ _ _ _) _) => apply REL_page_loop : rel.

Lemma REL_chunk_loop : forall fuel payload h,
REL erase (rops chunk_loop fuel payload h) (pops chunk_loop fuel payload (erase h)).
Proof. induction fuel as [|fuel IH]; intros payload h; cbn [chunk_loop]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (chunk_loop _ _ _ _ _ _ _ _ _ _ _ _ _) _) => apply REL_chunk_loop : rel.

Theorem REL_LLVMFuzzerTestOneInput : forall payload,
REL erase (rops LLVMFuzzerTestOneInput payload) (p_fuzz_one payload).
Proof. intros payload. unfold p_fuzz_one, LLVMFuzzerTestOneInput, ogg_sync_init, stream_zero. rel. Qed.

End HarnessRel.
