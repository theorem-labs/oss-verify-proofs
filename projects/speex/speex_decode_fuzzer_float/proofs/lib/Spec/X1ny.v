(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re X1od
X1r8 X1nu X1ob X1o3 X1o0.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.

Section PureBits.
Context {ptr ptr' : Type} (f : ptr -> ptr').
Lemma pm_unpack_unsigned : forall b n,
speex_bits_unpack_unsigned (pm_bits f b) n = (fst (speex_bits_unpack_unsigned b n), pm_bits f (snd (speex_bits_unpack_unsigned b n))).
Proof. intros b n. unfold speex_bits_unpack_unsigned. cbn [pm_bits sb_nbBits sb_overflow]. destruct (_ || _); reflexivity. Qed.
Lemma pm_peek : forall b, speex_bits_peek (pm_bits f b) = (fst (speex_bits_peek b), pm_bits f (snd (speex_bits_peek b))).
Proof. intros b. unfold speex_bits_peek. cbn [pm_bits sb_nbBits sb_overflow]. destruct (_ || _); reflexivity. Qed.
Lemma pm_advance : forall b n, speex_bits_advance (pm_bits f b) n = pm_bits f (speex_bits_advance b n).
Proof. intros b n. unfold speex_bits_advance. cbn [pm_bits sb_nbBits sb_overflow]. destruct (_ || _); reflexivity. Qed.
Lemma pm_remaining : forall b, speex_bits_remaining (pm_bits f b) = speex_bits_remaining b.
Proof. reflexivity. Qed.
End PureBits.

Section Bits.
Variable sel : option bool.
Variable X : list event -> Prop.
Context {St ptr : Type}.
Variable K : St -> Model -> Prop.
Local Notation REL := (X1o3.REL sel X K).
Local Hint Extern 0 (Erasable ptr) => exact (Er_ptr ptr) : typeclass_instances.

Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.
Hypothesis Hcal : forall m n, REL erase (lib_calloc m n) (p_calloc m n).
Hypothesis Hrea : forall p p' n, REL erase (lib_realloc p n) (p_realloc p' n).
Hypothesis Hfree : forall p p', REL erase (lib_free p) (p_free p').
Hypothesis Hnot : forall msg, REL erase (spx_notify msg) (p_notify msg).
Hypothesis Hwarn : forall msg, REL erase (spx_warning msg) (p_warning msg).

Lemma REL_speex_bits_init : REL erase (speex_bits_init lib_calloc) (speex_bits_init p_calloc).
Proof. unfold speex_bits_init. rel. Qed.

Lemma REL_speex_bits_destroy : forall b, REL erase (speex_bits_destroy lib_free b) (speex_bits_destroy p_free (erase b)).
Proof. intros b. unfold speex_bits_destroy. rel. Qed.

Lemma REL_speex_bits_read_from : forall b pkt len,
REL erase (speex_bits_read_from lib_realloc spx_notify spx_warning b pkt len)
(speex_bits_read_from p_realloc p_notify p_warning (erase b) pkt len).
Proof. intros b pkt len. unfold speex_bits_read_from. rel. Qed.

Lemma REL_speex_packet_to_header : forall pkt size,
REL erase (speex_packet_to_header lib_calloc lib_free spx_notify pkt size)
(speex_packet_to_header p_calloc p_free p_notify pkt size).
Proof. intros pkt size. unfold speex_packet_to_header. rel. Qed.

Lemma REL_bits_unpack_unsigned_M : forall (b : bits_st ptr) n,
REL erase (bits_unpack_unsigned_M (St:=St) b n) (bits_unpack_unsigned_M (St:=pst) (ptr:=unit) (erase b) n).
Proof. intros b n. unfold bits_unpack_unsigned_M. apply REL_ret. rnorm. rewrite pm_unpack_unsigned. reflexivity. Qed.
Lemma REL_bits_peek_M : forall (b : bits_st ptr), REL erase (bits_peek_M (St:=St) b) (bits_peek_M (St:=pst) (ptr:=unit) (erase b)).
Proof. intros b. unfold bits_peek_M. apply REL_ret. rnorm. rewrite pm_peek. reflexivity. Qed.
Lemma REL_bits_advance_M : forall (b : bits_st ptr) n, REL erase (bits_advance_M (St:=St) b n) (bits_advance_M (St:=pst) (ptr:=unit) (erase b) n).
Proof. intros b n. unfold bits_advance_M. apply REL_ret. rnorm. rewrite pm_advance. reflexivity. Qed.
Lemma REL_bits_remaining_M : forall (b : bits_st ptr), REL erase (bits_remaining_M (St:=St) b) (bits_remaining_M (St:=pst) (ptr:=unit) (erase b)).
Proof. intros b. unfold bits_remaining_M. apply REL_ret. reflexivity. Qed.

End Bits.

#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_bits_init _) _) => (eapply REL_speex_bits_init; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_bits_destroy _ _) _) => (eapply REL_speex_bits_destroy; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_bits_read_from _ _ _ _ _ _) _) => (eapply REL_speex_bits_read_from; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_packet_to_header _ _ _ _ _) _) => (eapply REL_speex_packet_to_header; eassumption) : rel.
