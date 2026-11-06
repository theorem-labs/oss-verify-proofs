(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw X1qz X1nt X1rg X1rh X1re X1od
X1r8 X1nu X1ob X1o3 X1o0 X1ny.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.

Section PureCtl.
Context {ptr ptr' : Type} (f : ptr -> ptr').
Lemma pm_nb_ctl : forall st r,
nb_decoder_ctl (pm_nb f st) r = (fst (nb_decoder_ctl st r), pm_nb f (snd (nb_decoder_ctl st r))).
Proof. intros st r. destruct r; reflexivity. Qed.
Lemma pm_ctl : forall d r,
speex_decoder_ctl (pm_dec f d) r = (fst (speex_decoder_ctl d r), pm_dec f (snd (speex_decoder_ctl d r))).
Proof.
induction d as [st|st low IH]; intros r; cbn [speex_decoder_ctl pm_dec].
- rewrite pm_nb_ctl. destruct (nb_decoder_ctl st r). reflexivity.
- destruct r; try reflexivity; rewrite IH; match goal with |- context [speex_decoder_ctl low ?r] => destruct (speex_decoder_ctl low r) end; reflexivity.
Qed.
End PureCtl.
#[global] Hint Rewrite @pm_ctl : erw.

Section Spx.
Variable sel : option bool.
Variable X : list event -> Prop.
Context {St ptr : Type}.
Variable K : St -> Model -> Prop.
Local Notation REL := (X1o3.REL sel X K).
Local Hint Extern 0 (Erasable ptr) => exact (Er_ptr ptr) : typeclass_instances.

Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable bits_unpack_unsigned : bits_st ptr -> Z -> M St (Z * bits_st ptr).
Variable bits_peek : bits_st ptr -> M St (Z * bits_st ptr).
Variable bits_advance : bits_st ptr -> Z -> M St (bits_st ptr).
Variable bits_remaining : bits_st ptr -> M St Z.
Hypothesis Hcal : forall m n, REL erase (lib_calloc m n) (p_calloc m n).
Hypothesis Hfree : forall p p', REL erase (lib_free p) (p_free p').
Hypothesis Hnot : forall msg, REL erase (spx_notify msg) (p_notify msg).

Local Notation pu := (bits_unpack_unsigned_M (St:=pst) (ptr:=unit)).
Local Notation pp := (bits_peek_M (St:=pst) (ptr:=unit)).
Local Notation pa := (bits_advance_M (St:=pst) (ptr:=unit)).
Local Notation pr := (bits_remaining_M (St:=pst) (ptr:=unit)).
Hypothesis Hbu : forall b n, REL erase (bits_unpack_unsigned b n) (pu (erase b) n).
Hypothesis Hbp : forall b, REL erase (bits_peek b) (pp (erase b)).
Hypothesis Hba : forall b n, REL erase (bits_advance b n) (pa (erase b) n).
Hypothesis Hbr : forall b, REL erase (bits_remaining b) (pr (erase b)).

Lemma REL_speex_default_user_handler : forall b,
REL erase (speex_default_user_handler bits_unpack_unsigned bits_advance b) (speex_default_user_handler pu pa (erase b)).
Proof. intros b. unfold speex_default_user_handler. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (speex_default_user_handler _ _ _) _) => apply REL_speex_default_user_handler : rel.

Lemma REL_speex_std_stereo_request_handler : forall b,
REL erase (speex_std_stereo_request_handler bits_unpack_unsigned b) (speex_std_stereo_request_handler pu (erase b)).
Proof. intros b. unfold speex_std_stereo_request_handler. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (speex_std_stereo_request_handler _ _) _) => apply REL_speex_std_stereo_request_handler : rel.

Lemma REL_speex_inband_handler : forall b cb,
REL erase (speex_inband_handler bits_unpack_unsigned bits_advance b cb) (speex_inband_handler pu pa (erase b) cb).
Proof. intros b cb. unfold speex_inband_handler. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (speex_inband_handler _ _ _ _) _) => apply REL_speex_inband_handler : rel.

Lemma REL_lsp_unquant : forall k b, REL erase (lsp_unquant bits_unpack_unsigned k b) (lsp_unquant pu k (erase b)).
Proof. intros k b. destruct k; cbn [lsp_unquant]; unfold lsp_unquant_lbr, lsp_unquant_nb, lsp_unquant_high; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (lsp_unquant _ _ _) _) => apply REL_lsp_unquant : rel.

Lemma REL_ltp_unquant : forall k start b, REL erase (ltp_unquant bits_unpack_unsigned k start b) (ltp_unquant pu k start (erase b)).
Proof. intros k start b. destruct k; cbn [ltp_unquant]; unfold forced_pitch_unquant, pitch_unquant_3tap; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (ltp_unquant _ _ _ _) _) => apply REL_ltp_unquant : rel.

Lemma REL_split_cb_read : forall n hs sb b,
REL erase (split_cb_read bits_unpack_unsigned n hs sb b) (split_cb_read pu n hs sb (erase b)).
Proof. induction n as [|n IH]; intros hs sb b; cbn [split_cb_read]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (split_cb_read _ _ _ _ _) _) => apply REL_split_cb_read : rel.

Lemma REL_innovation_unquant : forall k b, REL erase (innovation_unquant bits_unpack_unsigned k b) (innovation_unquant pu k (erase b)).
Proof. intros k b. destruct k; cbn [innovation_unquant]; unfold noise_codebook_unquant, split_cb_shape_sign_unquant; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (innovation_unquant _ _ _) _) => apply REL_innovation_unquant : rel.

Lemma REL_nb_decoder_init : REL erase (nb_decoder_init lib_calloc) (nb_decoder_init p_calloc).
Proof. unfold nb_decoder_init, nb_init_state. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_decoder_init _) _) => apply REL_nb_decoder_init : rel.

Lemma REL_nb_decoder_init_d : REL erase (nb_decoder_init_d lib_calloc) (nb_decoder_init_d p_calloc).
Proof. unfold nb_decoder_init_d. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_decoder_init_d _) _) => apply REL_nb_decoder_init_d : rel.

Lemma REL_speex_decoder_destroy : forall d,
REL erase (speex_decoder_destroy lib_free d) (speex_decoder_destroy p_free (erase d)).
Proof. induction d as [st|st low IH]; cbn [speex_decoder_destroy]; unfold nb_decoder_destroy; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (speex_decoder_destroy _ _) _) => apply REL_speex_decoder_destroy : rel.

Lemma REL_sb_decoder_init : forall m (low_init : M St (option (dec_state ptr))) low_init',
REL erase low_init low_init' ->
REL erase (sb_decoder_init lib_calloc lib_free m low_init) (sb_decoder_init p_calloc p_free m low_init').
Proof. intros m low_init low_init' Hlow. unfold sb_decoder_init. rel. Qed.

Lemma REL_speex_decoder_init : forall m, REL erase (speex_decoder_init lib_calloc lib_free m) (speex_decoder_init p_calloc p_free m).
Proof.
intros m. destruct m; cbn [speex_decoder_init].
- apply REL_nb_decoder_init_d.
- apply REL_sb_decoder_init. apply REL_nb_decoder_init_d.
- apply REL_sb_decoder_init. apply REL_sb_decoder_init. apply REL_nb_decoder_init_d.
Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (speex_decoder_init _ _ _) _) => apply REL_speex_decoder_init : rel.

Lemma REL_nb_skip_wb_layer : forall b,
REL erase (nb_skip_wb_layer bits_unpack_unsigned bits_advance b) (nb_skip_wb_layer pu pa (erase b)).
Proof. intros b. unfold nb_skip_wb_layer. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_skip_wb_layer _ _ _) _) => apply REL_nb_skip_wb_layer : rel.

Lemma REL_nb_mode_search : forall fuel st b,
REL erase (nb_mode_search spx_notify bits_unpack_unsigned bits_advance bits_remaining fuel st b)
(nb_mode_search p_notify pu pa pr fuel (erase st) (erase b)).
Proof. induction fuel as [|fuel IH]; intros st b; cbn [nb_mode_search]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_mode_search _ _ _ _ _ _ _) _) => apply REL_nb_mode_search : rel.

Lemma REL_nb_decode_subframe : forall sm ol sub st b,
REL erase (nb_decode_subframe bits_unpack_unsigned sm ol sub st b) (nb_decode_subframe pu sm ol sub (erase st) (erase b)).
Proof. intros sm ol sub st b. unfold nb_decode_subframe. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_decode_subframe _ _ _ _ _ _) _) => apply REL_nb_decode_subframe : rel.

Lemma REL_nb_decode_subframes : forall n sub sm ol st b,
REL erase (nb_decode_subframes bits_unpack_unsigned n sub sm ol st b) (nb_decode_subframes pu n sub sm ol (erase st) (erase b)).
Proof. induction n as [|n IH]; intros sub sm ol st b; cbn [nb_decode_subframes]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_decode_subframes _ _ _ _ _ _ _) _) => apply REL_nb_decode_subframes : rel.

Lemma REL_nb_decode : forall st b,
REL erase (nb_decode spx_notify bits_unpack_unsigned bits_advance bits_remaining st b)
(nb_decode p_notify pu pa pr (erase st) (erase b)).
Proof. intros st b. unfold nb_decode. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (nb_decode _ _ _ _ _ _) _) => apply REL_nb_decode : rel.

Lemma REL_sb_decode_subframe : forall sm b,
REL erase (sb_decode_subframe bits_unpack_unsigned sm b) (sb_decode_subframe pu sm (erase b)).
Proof. intros sm b. unfold sb_decode_subframe. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (sb_decode_subframe _ _ _) _) => apply REL_sb_decode_subframe : rel.

Lemma REL_sb_decode_subframes : forall n sm b,
REL erase (sb_decode_subframes bits_unpack_unsigned n sm b) (sb_decode_subframes pu n sm (erase b)).
Proof. induction n as [|n IH]; intros sm b; cbn [sb_decode_subframes]; rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (sb_decode_subframes _ _ _ _) _) => apply REL_sb_decode_subframes : rel.

Lemma REL_sb_decode : forall st low (low_decode : dec_state ptr -> bits_st ptr -> Z -> M St (Z * dec_state ptr * bits_st ptr)) low_decode' b out,
(forall d b o, REL erase (low_decode d b o) (low_decode' (erase d) (erase b) o)) ->
REL erase (sb_decode spx_notify bits_unpack_unsigned bits_peek bits_remaining st low low_decode b out)
(sb_decode p_notify pu pp pr (erase st) (erase low) low_decode' (erase b) out).
Proof. intros st low low_decode low_decode' b out Hlow. unfold sb_decode. rel. Qed.

Lemma REL_speex_decode_n : forall n d b out,
REL erase (speex_decode_n spx_notify bits_unpack_unsigned bits_peek bits_advance bits_remaining n d b out)
(speex_decode_n p_notify pu pp pa pr n (erase d) (erase b) out).
Proof.
induction n as [|n IH]; intros d b out; cbn [speex_decode_n]; [apply REL_munr|].
destruct d as [st|st low]; rnorm.
- rel.
- rel1; [apply REL_sb_decode; exact IH|]. rel.
Qed.

Lemma REL_speex_decode : forall d b out,
REL erase (speex_decode spx_notify bits_unpack_unsigned bits_peek bits_advance bits_remaining d b out)
(speex_decode p_notify pu pp pa pr (erase d) (erase b) out).
Proof.
intros d b out. unfold speex_decode. rnorm.
replace (dec_depth (er_dec d)) with (dec_depth d); [apply REL_speex_decode_n|].
clear. induction d as [st|st low IH]; cbn; [reflexivity| f_equal; exact IH].
Qed.

End Spx.

#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_decoder_init _ _ _) _) => (eapply REL_speex_decoder_init; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_decoder_destroy _ _) _) => (eapply REL_speex_decoder_destroy; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (speex_decode _ _ _ _ _ _ _ _) _) => (eapply REL_speex_decode; eassumption) : rel.
