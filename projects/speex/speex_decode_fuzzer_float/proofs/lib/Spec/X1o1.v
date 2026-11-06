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

Ltac pm_cases :=
repeat match goal with
| |- context [if ?c then _ else _] => destruct c
| |- context [match ?x with _ => _ end] => destruct x
end.

Section PureOgg.
Context {ptr ptr' : Type} (f : ptr -> ptr').
Implicit Types (sy : sync_st ptr) (os : stream_st ptr).

Lemma pm_sync_check : forall sy, ogg_sync_check (pm_sync f sy) = ogg_sync_check sy.
Proof. reflexivity. Qed.
Lemma pm_sync_write : forall sy off bs, sync_write (pm_sync f sy) off bs = pm_sync f (sync_write sy off bs).
Proof. reflexivity. Qed.
Lemma pm_sync_wrote : forall sy n, ogg_sync_wrote (pm_sync f sy) n = pm_snd (pm_sync f) (ogg_sync_wrote sy n).
Proof. intros sy n. unfold ogg_sync_wrote, pm_snd. rewrite pm_sync_check. cbn [pm_sync sy_storage sy_fill]. pm_cases; reflexivity. Qed.
Lemma pm_sync_fail : forall sy ret bytes, sync_fail (pm_sync f sy) ret bytes = pm_snd (pm_sync f) (sync_fail sy ret bytes).
Proof. reflexivity. Qed.
Lemma pm_page_header : forall sy og, page_header (pm_sync f sy) og = page_header sy og.
Proof. reflexivity. Qed.
Lemma pm_page_body : forall sy og, page_body (pm_sync f sy) og = page_body sy og.
Proof. reflexivity. Qed.
Lemma pm_sync_pageseek : forall sy, ogg_sync_pageseek (pm_sync f sy) = pm_snd (pm_sync f) (ogg_sync_pageseek sy).
Proof.
intros sy. unfold ogg_sync_pageseek. cbv zeta. rewrite pm_sync_check.
cbn [pm_sync sy_returned sy_fill sy_buf sy_headerbytes sy_bodybytes sy_storage sy_unsynced sy_data].
destruct (ogg_sync_check sy); [reflexivity|].
destruct (sy_headerbytes sy =? 0).
- destruct (sy_fill sy - sy_returned sy <? 27); [reflexivity|].
destruct (negb _); [apply pm_sync_fail|].
destruct (sy_fill sy - sy_returned sy <? _); [reflexivity|].
cbn [sy_bodybytes sy_headerbytes sy_buf sy_data sy_storage sy_fill sy_unsynced].
destruct (_ <? _); [reflexivity|]. destruct (negb _); reflexivity.
- destruct (_ <? _); [reflexivity|]. destruct (negb _); [apply pm_sync_fail| reflexivity].
Qed.
Lemma pm_pageout_loop : forall fuel sy,
pageout_loop fuel (pm_sync f sy) = option_map (pm_snd (pm_sync f)) (pageout_loop fuel sy).
Proof.
induction fuel as [|fuel IH]; intros sy; cbn [pageout_loop]; [reflexivity|].
rewrite pm_sync_pageseek. destruct (ogg_sync_pageseek sy) as [[ret og] sy1]. cbn [pm_snd fst snd].
destruct (0 <? ret); [reflexivity|]. destruct (ret =? 0); [reflexivity|].
cbn [pm_sync sy_unsynced]. destruct (sy_unsynced sy1 =? 0); [reflexivity| apply IH].
Qed.
Lemma pm_sync_pageout : forall sy, ogg_sync_pageout (pm_sync f sy) = option_map (pm_snd (pm_sync f)) (ogg_sync_pageout sy).
Proof.
intros sy. unfold ogg_sync_pageout. rewrite pm_sync_check. destruct (ogg_sync_check sy); [reflexivity|].
apply pm_pageout_loop.
Qed.
Lemma pm_page_fuel : forall sy, page_fuel (pm_sync f sy) = page_fuel sy.
Proof. reflexivity. Qed.

Lemma pm_stream_check : forall os, ogg_stream_check (pm_stream f os) = ogg_stream_check os.
Proof. intros os. unfold ogg_stream_check. cbn [pm_stream os_body_data]. destruct (os_body_data os); reflexivity. Qed.
Lemma pm_packet_data : forall os op, packet_data (pm_stream f os) op = packet_data os op.
Proof. reflexivity. Qed.
Lemma pm_packet_fuel : forall os, packet_fuel (pm_stream f os) = packet_fuel os.
Proof. reflexivity. Qed.
Lemma pm_pagein_returned : forall os, pagein_returned (pm_stream f os) = pm_stream f (pagein_returned os).
Proof. intros os. unfold pagein_returned. cbv zeta. cbn [pm_stream os_body_returned]. destruct (negb (os_body_returned os =? 0)); cbn; destruct (negb _); reflexivity. Qed.
Lemma pm_pagein_unroll : forall os pageno, pagein_unroll (pm_stream f os) pageno = pm_stream f (pagein_unroll os pageno).
Proof. intros os pageno. unfold pagein_unroll. cbv zeta. cbn [pm_stream os_pageno]. destruct (negb (pageno =? os_pageno os)); [|reflexivity]. cbn. destruct (negb _); reflexivity. Qed.
Lemma pm_pagein_skip : forall os hdr, pagein_skip (pm_stream f os) hdr = pagein_skip os hdr.
Proof. reflexivity. Qed.
Lemma pm_pagein_body : forall os body sk bs, pagein_body (pm_stream f os) body sk bs = pm_stream f (pagein_body os body sk bs).
Proof. reflexivity. Qed.
Lemma pm_pagein_segments : forall os hdr bos segptr,
pagein_segments (pm_stream f os) hdr bos segptr = pm_stream f (pagein_segments os hdr bos segptr).
Proof.
intros os hdr bos segptr. unfold pagein_segments. cbv zeta. cbn [pm_stream os_lacing_fill os_lacing_packet].
destruct (seg_loop _ _ _ _ _) as [[[[lac gran] fill'] packet'] saved]. reflexivity.
Qed.
Lemma pm_reset_serialno : forall os s,
ogg_stream_reset_serialno (pm_stream f os) s = pm_snd (pm_stream f) (ogg_stream_reset_serialno os s).
Proof. intros os s. unfold ogg_stream_reset_serialno. rewrite pm_stream_check. destruct (ogg_stream_check os); reflexivity. Qed.
Lemma pm_packetout : forall os, packetout (pm_stream f os) = option_map (pm_snd (pm_stream f)) (packetout os).
Proof.
intros os. unfold packetout. cbv zeta. cbn [pm_stream os_lacing_returned os_lacing_packet os_lacing].
destruct (_ <=? _); [reflexivity|]. destruct (negb _); [reflexivity|].
destruct (gather255 _ _ _ _ _) as [[[n eos] bytes]|]; reflexivity.
Qed.
Lemma pm_stream_packetout : forall os,
ogg_stream_packetout (pm_stream f os) = option_map (pm_snd (pm_stream f)) (ogg_stream_packetout os).
Proof. intros os. unfold ogg_stream_packetout. rewrite pm_stream_check. destruct (ogg_stream_check os); [reflexivity| apply pm_packetout]. Qed.
End PureOgg.

#[global] Hint Rewrite @pm_sync_check @pm_sync_write @pm_sync_wrote @pm_page_header @pm_page_body @pm_sync_pageout @pm_page_fuel
@pm_stream_check @pm_packet_data @pm_packet_fuel @pm_pagein_returned @pm_pagein_unroll @pm_pagein_skip @pm_pagein_body
@pm_pagein_segments @pm_reset_serialno @pm_stream_packetout : erw.

Section Ogg.
Variable sel : option bool.
Variable X : list event -> Prop.
Context {St ptr : Type}.
Variable K : St -> Model -> Prop.
Local Notation REL := (X1o3.REL sel X K).
Local Hint Extern 0 (Erasable ptr) => exact (Er_ptr ptr) : typeclass_instances.

Variable lib_malloc : Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Hypothesis Hmal : forall n, REL erase (lib_malloc n) (p_malloc n).
Hypothesis Hrea : forall p p' n, REL erase (lib_realloc p n) (p_realloc p' n).
Hypothesis Hfree : forall p p', REL erase (lib_free p) (p_free p').

Lemma REL_ogg_sync_clear : forall sy, REL erase (ogg_sync_clear lib_free sy) (ogg_sync_clear p_free (erase sy)).
Proof. intros sy. unfold ogg_sync_clear, ogg_sync_init. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_sync_clear _ _) _) => apply REL_ogg_sync_clear : rel.

Lemma REL_ogg_sync_buffer : forall sy size,
REL erase (ogg_sync_buffer lib_malloc lib_realloc lib_free sy size) (ogg_sync_buffer p_malloc p_realloc p_free (erase sy) size).
Proof. intros sy size. unfold ogg_sync_buffer. rstep; [rel|]. destruct (negb (sy_returned sy =? 0)); rel. Qed.

Lemma REL_mfree_opt : forall o, REL erase (mfree_opt lib_free o) (mfree_opt p_free (erase o)).
Proof. intros o. unfold mfree_opt. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (mfree_opt _ _) _) => apply REL_mfree_opt : rel.

Lemma REL_ogg_stream_clear : forall os, REL erase (ogg_stream_clear lib_free os) (ogg_stream_clear p_free (erase os)).
Proof. intros os. unfold ogg_stream_clear, stream_zero. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_stream_clear _ _) _) => apply REL_ogg_stream_clear : rel.

Lemma REL_ogg_stream_init : forall serialno,
REL erase (ogg_stream_init lib_malloc lib_free serialno) (ogg_stream_init p_malloc p_free serialno).
Proof. intros serialno. unfold ogg_stream_init. rel. Qed.

Lemma REL_os_body_expand : forall os needed,
REL erase (os_body_expand lib_realloc lib_free os needed) (os_body_expand p_realloc p_free (erase os) needed).
Proof. intros os needed. unfold os_body_expand. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (os_body_expand _ _ _ _) _) => apply REL_os_body_expand : rel.

Lemma REL_os_lacing_expand : forall os needed,
REL erase (os_lacing_expand lib_realloc lib_free os needed) (os_lacing_expand p_realloc p_free (erase os) needed).
Proof. intros os needed. unfold os_lacing_expand. rel. Qed.
Local Hint Extern 0 (X1o3.REL _ _ _ _ (os_lacing_expand _ _ _ _) _) => apply REL_os_lacing_expand : rel.

Lemma REL_ogg_stream_pagein : forall os hdr body,
REL erase (ogg_stream_pagein lib_realloc lib_free os hdr body) (ogg_stream_pagein p_realloc p_free (erase os) hdr body).
Proof. intros os hdr body. unfold ogg_stream_pagein. rel. Qed.

End Ogg.

#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_sync_clear _ _) _) => (eapply REL_ogg_sync_clear; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_sync_buffer _ _ _ _ _) _) => (eapply REL_ogg_sync_buffer; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_stream_clear _ _) _) => (eapply REL_ogg_stream_clear; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_stream_init _ _ _) _) => (eapply REL_ogg_stream_init; eassumption) : rel.
#[global] Hint Extern 0 (X1o3.REL _ _ _ _ (ogg_stream_pagein _ _ _ _ _) _) => (eapply REL_ogg_stream_pagein; eassumption) : rel.
