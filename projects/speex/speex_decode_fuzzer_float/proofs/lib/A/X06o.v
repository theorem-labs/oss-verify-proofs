(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X065 X06u X07a.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0wy X0xm X0y1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation PM := (X1qy.M pst).
Definition app_only {A} (c : PM A) : Prop := forall q r q', prun c q = Some (r, q') -> exists bs, p_err q' = p_err q ++ bs.

Lemma app_ret {A} (a : A) : app_only (X1qy.mret a).
Proof. intros q r q' H. rewrite prun_ret in H. injection H as _ <-. exists []. rewrite app_nil_r. reflexivity. Qed.
Lemma app_unr {A} : app_only (X1qy.munr (A:=A)).
Proof. intros q r q' H. rewrite prun_munr in H. discriminate H. Qed.
Lemma app_bind {A B} (c : PM A) (f : A -> PM B) : app_only c -> (forall a, app_only (f a)) -> app_only (X1qy.mbind c f).
Proof.
intros Hc Hf q r q' H. rewrite prun_bind in H. destruct (prun c q) as [[a q1]|] eqn:E; [| discriminate H].
destruct (Hc q a q1 E) as (bs1 & E1). destruct (Hf a q1 r q' H) as (bs2 & E2). exists (bs1 ++ bs2). rewrite E2, E1, app_assoc. reflexivity.
Qed.
Lemma app_upd bs : app_only (X1qy.mupd (p_app bs)).
Proof. intros q r q' H. rewrite prun_upd in H. injection H as _ <-. exists bs. reflexivity. Qed.
Lemma app_notify msg : app_only (p_notify msg). Proof. apply app_upd. Qed.
Lemma app_warning msg : app_only (p_warning msg). Proof. apply app_upd. Qed.
Lemma app_malloc n : app_only (p_malloc n). Proof. apply app_ret. Qed.
Lemma app_realloc p n : app_only (p_realloc p n). Proof. apply app_ret. Qed.
Lemma app_free p : app_only (p_free p). Proof. apply app_ret. Qed.
Lemma app_calloc m n : app_only (p_calloc m n). Proof. unfold p_calloc. destruct (_ && _); [apply app_ret| apply app_malloc]. Qed.

Ltac app_step :=
match goal with
| |- app_only (X1qy.mret _) => apply app_ret
| |- app_only X1qy.munr => apply app_unr
| |- app_only (X1qy.mbind _ _) => apply app_bind; [| intros ?]
| |- app_only (p_notify _) => apply app_notify
| |- app_only (p_warning _) => apply app_warning
| |- app_only (p_malloc _) => apply app_malloc
| |- app_only (p_calloc _ _) => apply app_calloc
| |- app_only (p_realloc _ _) => apply app_realloc
| |- app_only (p_free _) => apply app_free
| |- app_only (if ?b then _ else _) => destruct b
| |- app_only (match ?x with _ => _ end) => destruct x
end.
Ltac app_solve := repeat app_step.

Lemma app_destroy : forall d, app_only (speex_decoder_destroy (St := pst) p_free d).
Proof.
induction d as [st | st low IH]; cbn [speex_decoder_destroy]; [unfold nb_decoder_destroy; app_solve|].
apply app_bind; [exact IH| intros _; app_solve].
Qed.
Lemma app_cleanup : forall h, app_only (hP_cleanup h).
Proof.
intros h. unfold hP_cleanup, cleanup, h_decoder_destroy, speex_bits_destroy, ogg_stream_clear, ogg_sync_clear, mfree_opt.
apply app_bind; [destruct (h_st h); [apply app_destroy| apply app_ret]| intros _]. app_solve.
Qed.
Lemma app_init : forall mo, app_only (speex_decoder_init (St := pst) p_calloc p_free mo).
Proof. intros mo. unfold speex_decoder_init, sb_decoder_init, nb_decoder_init_d, nb_decoder_init. destruct mo; app_solve. Qed.
Lemma app_p2h : forall pkt size, app_only (speex_packet_to_header (St := pst) p_calloc p_free p_notify pkt size).
Proof. intros pkt size. unfold speex_packet_to_header. app_solve. Qed.

Lemma app_process_header : forall h pdata bytes, app_only (hP_process_header h pdata bytes).
Proof.
intros h pdata bytes. unfold hP_process_header, process_header, h_decoder_init, h_decoder_destroy.
apply app_bind; [apply app_p2h| intros r].
repeat (first [ match goal with |- app_only (speex_decoder_init _ _ _) => apply app_init end
| match goal with |- app_only (speex_decoder_destroy _ _) => apply app_destroy end
| app_step ]).
Qed.
Lemma app_read_from : forall (b : bits_st unit) pkt len, app_only (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b pkt len).
Proof. intros b pkt len. unfold speex_bits_read_from. app_solve. Qed.
Lemma app_decode_loop : forall n (st : dec_state unit) (b : bits_st unit), app_only (hP_decode_loop n st b).
Proof. intros n st b q r q' H. unfold hP_decode_loop in H. exact (dloop_appends n st b q r q' H). Qed.

Lemma app_packet_loop : forall fuel h pno, app_only (hP_packet_loop fuel h pno).
Proof.
induction fuel as [|fuel IH]; intros h pno; unfold hP_packet_loop; cbn [packet_loop]; [apply app_unr|].
repeat (first [ match goal with |- app_only (process_header _ _ _ _ _ _) => apply app_process_header end
| match goal with |- app_only (cleanup _ _) => apply app_cleanup end
| match goal with |- app_only (speex_bits_read_from _ _ _ _ _ _) => apply app_read_from end
| match goal with |- app_only (decode_loop _ _ _ _ _ _ _ _) => apply app_decode_loop end
| match goal with |- app_only (packet_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply IH end
| app_step ]).
Qed.

Lemma app_stream_init : forall serial, app_only (ogg_stream_init (St := pst) p_malloc p_free serial).
Proof. intros serial. unfold ogg_stream_init, ogg_stream_clear, mfree_opt. app_solve. Qed.
Lemma app_pagein : forall (os : stream_st unit) hdr body, app_only (ogg_stream_pagein (St := pst) p_realloc p_free os hdr body).
Proof. intros os hdr body. unfold ogg_stream_pagein, os_lacing_expand, os_body_expand, ogg_stream_clear, mfree_opt. app_solve. Qed.
Lemma app_page_loop : forall fuel h, app_only (hP_page_loop fuel h).
Proof.
induction fuel as [|fuel IH]; intros h; unfold hP_page_loop; cbn [page_loop]; [apply app_unr|].
repeat (first [ match goal with |- app_only (ogg_stream_init _ _ _) => apply app_stream_init end
| match goal with |- app_only (ogg_stream_pagein _ _ _ _ _) => apply app_pagein end
| match goal with |- app_only (cleanup _ _) => apply app_cleanup end
| match goal with |- app_only (packet_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply app_packet_loop end
| match goal with |- app_only (page_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply IH end
| app_step ]).
Qed.
Lemma app_sync_buffer : forall (sy : sync_st unit) size, app_only (ogg_sync_buffer (St := pst) p_malloc p_realloc p_free sy size).
Proof. intros sy size. unfold ogg_sync_buffer, ogg_sync_clear. app_solve. Qed.
Lemma app_chunk_loop : forall fuel payload h, app_only (hP_chunk_loop fuel payload h).
Proof.
induction fuel as [|fuel IH]; intros payload h; unfold hP_chunk_loop; cbn [chunk_loop]; [apply app_unr|].
repeat (first [ match goal with |- app_only (ogg_sync_buffer _ _ _ _ _) => apply app_sync_buffer end
| match goal with |- app_only (page_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply app_page_loop end
| match goal with |- app_only (chunk_loop _ _ _ _ _ _ _ _ _ _ _ _ _) => apply IH end
| app_step ]).
Qed.

Lemma prun_destroy : forall d q, prun (speex_decoder_destroy (St := pst) p_free d) q = Some (tt, q).
Proof.
induction d as [st | st low IH]; intros q; cbn [speex_decoder_destroy]; [reflexivity|].
rewrite prun_bind, IH. reflexivity.
Qed.
Lemma prun_cleanup : forall (h : hstate unit) q, prun (hP_cleanup h) q = Some (tt, q).
Proof.
intros h q. unfold hP_cleanup, cleanup, h_decoder_destroy. rewrite prun_bind.
destruct (h_st h) as [d|]; [rewrite prun_destroy| rewrite prun_ret]; cbn beta iota;
unfold speex_bits_destroy, ogg_stream_clear, ogg_sync_clear, mfree_opt;
destruct (negb (sb_owner (h_bits h) =? 0)), (negb (h_stream_init h =? 0)), (os_body_data (h_os h)), (os_lacing_vals (h_os h)),
(os_granule_vals (h_os h)), (sy_data (h_oy h)); reflexivity.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation PM := (X1qy.M pst).
Definition app_only {A} (c : PM A) : Prop := forall q r q', prun c q = Some (r, q') -> exists bs, p_err q' = p_err q ++ bs.

Lemma app_ret {A} (a : A) : app_only (X1qy.mret a).
Proof. intros q r q' H. rewrite prun_ret in H. injection H as _ <-. exists []. rewrite app_nil_r. reflexivity. Qed.
Lemma app_unr {A} : app_only (X1qy.munr (A:=A)).
Proof. intros q r q' H. rewrite prun_munr in H. discriminate H. Qed.
Lemma app_bind {A B} (c : PM A) (f : A -> PM B) : app_only c -> (forall a, app_only (f a)) -> app_only (X1qy.mbind c f).
Proof.
intros Hc Hf q r q' H. rewrite prun_bind in H. destruct (prun c q) as [[a q1]|] eqn:E; [| discriminate H].
destruct (Hc q a q1 E) as (bs1 & E1). destruct (Hf a q1 r q' H) as (bs2 & E2). exists (bs1 ++ bs2). rewrite E2, E1, app_assoc. reflexivity.
Qed.
Lemma app_upd bs : app_only (X1qy.mupd (p_app bs)).
Proof. intros q r q' H. rewrite prun_upd in H. injection H as _ <-. exists bs. reflexivity. Qed.
Lemma app_notify msg : app_only (p_notify msg). Proof. apply app_upd. Qed.
Lemma app_warning msg : app_only (p_warning msg). Proof. apply app_upd. Qed.
Lemma app_malloc n : app_only (p_malloc n). Proof. apply app_ret. Qed.
Lemma app_realloc p n : app_only (p_realloc p n). Proof. apply app_ret. Qed.
Lemma app_free p : app_only (p_free p). Proof. apply app_ret. Qed.
Lemma app_calloc m n : app_only (p_calloc m n). Proof. unfold p_calloc. destruct (_ && _); [apply app_ret| apply app_malloc]. Qed.

Ltac app_step :=
match goal with
| |- app_only (X1qy.mret _) => apply app_ret
| |- app_only X1qy.munr => apply app_unr
| |- app_only (X1qy.mbind _ _) => apply app_bind; [| intros ?]
| |- app_only (p_notify _) => apply app_notify
| |- app_only (p_warning _) => apply app_warning
| |- app_only (p_malloc _) => apply app_malloc
| |- app_only (p_calloc _ _) => apply app_calloc
| |- app_only (p_realloc _ _) => apply app_realloc
| |- app_only (p_free _) => apply app_free
| |- app_only (if ?b then _ else _) => destruct b
| |- app_only (match ?x with _ => _ end) => destruct x
end.
Ltac app_solve := repeat app_step.

Lemma app_destroy : forall d, app_only (speex_decoder_destroy (St := pst) p_free d).
Proof.
induction d as [st | st low IH]; cbn [speex_decoder_destroy]; [unfold nb_decoder_destroy; app_solve|].
apply app_bind; [exact IH| intros _; app_solve].
Qed.
Lemma app_cleanup : forall h, app_only (hP_cleanup h).
Proof.
intros h. unfold hP_cleanup, cleanup, h_decoder_destroy, speex_bits_destroy, ogg_stream_clear, ogg_sync_clear, mfree_opt.
apply app_bind; [destruct (h_st h); [apply app_destroy| apply app_ret]| intros _]. app_solve.
Qed.
Lemma app_init : forall mo, app_only (speex_decoder_init (St := pst) p_calloc p_free mo).
Proof. intros mo. unfold speex_decoder_init, sb_decoder_init, nb_decoder_init_d, nb_decoder_init. destruct mo; app_solve. Qed.
Lemma app_p2h : forall pkt size, app_only (speex_packet_to_header (St := pst) p_calloc p_free p_notify pkt size).
Proof. intros pkt size. unfold speex_packet_to_header. app_solve. Qed.

Lemma app_process_header : forall h pdata bytes, app_only (hP_process_header h pdata bytes).
Proof.
intros h pdata bytes. unfold hP_process_header, process_header, h_decoder_init, h_decoder_destroy.
apply app_bind; [apply app_p2h| intros r].
repeat (first [ match goal with |- app_only (speex_decoder_init _ _ _) => apply app_init end
| match goal with |- app_only (speex_decoder_destroy _ _) => apply app_destroy end
| app_step ]).
Qed.
Lemma app_read_from : forall (b : bits_st unit) pkt len, app_only (speex_bits_read_from (St := pst) p_realloc p_notify p_warning b pkt len).
Proof. intros b pkt len. unfold speex_bits_read_from. app_solve. Qed.
Lemma app_decode_loop : forall n (st : dec_state unit) (b : bits_st unit), app_only (hP_decode_loop n st b).
Proof. intros n st b q r q' H. unfold hP_decode_loop in H. exact (dloop_appends n st b q r q' H). Qed.

Lemma app_packet_loop : forall fuel h pno, app_only (hP_packet_loop fuel h pno).
Proof.
induction fuel as [|fuel IH]; intros h pno; unfold hP_packet_loop; cbn [packet_loop]; [apply app_unr|].
repeat (first [ match goal with |- app_only (process_header _ _ _ _ _ _) => apply app_process_header end
| match goal with |- app_only (cleanup _ _) => apply app_cleanup end
| match goal with |- app_only (speex_bits_read_from _ _ _ _ _ _) => apply app_read_from end
| match goal with |- app_only (decode_loop _ _ _ _ _ _ _ _) => apply app_decode_loop end
| match goal with |- app_only (packet_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply IH end
| app_step ]).
Qed.

Lemma app_stream_init : forall serial, app_only (ogg_stream_init (St := pst) p_malloc p_free serial).
Proof. intros serial. unfold ogg_stream_init, ogg_stream_clear, mfree_opt. app_solve. Qed.
Lemma app_pagein : forall (os : stream_st unit) hdr body, app_only (ogg_stream_pagein (St := pst) p_realloc p_free os hdr body).
Proof. intros os hdr body. unfold ogg_stream_pagein, os_lacing_expand, os_body_expand, ogg_stream_clear, mfree_opt. app_solve. Qed.
Lemma app_page_loop : forall fuel h, app_only (hP_page_loop fuel h).
Proof.
induction fuel as [|fuel IH]; intros h; unfold hP_page_loop; cbn [page_loop]; [apply app_unr|].
repeat (first [ match goal with |- app_only (ogg_stream_init _ _ _) => apply app_stream_init end
| match goal with |- app_only (ogg_stream_pagein _ _ _ _ _) => apply app_pagein end
| match goal with |- app_only (cleanup _ _) => apply app_cleanup end
| match goal with |- app_only (packet_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply app_packet_loop end
| match goal with |- app_only (page_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply IH end
| app_step ]).
Qed.
Lemma app_sync_buffer : forall (sy : sync_st unit) size, app_only (ogg_sync_buffer (St := pst) p_malloc p_realloc p_free sy size).
Proof. intros sy size. unfold ogg_sync_buffer, ogg_sync_clear. app_solve. Qed.
Lemma app_chunk_loop : forall fuel payload h, app_only (hP_chunk_loop fuel payload h).
Proof.
induction fuel as [|fuel IH]; intros payload h; unfold hP_chunk_loop; cbn [chunk_loop]; [apply app_unr|].
repeat (first [ match goal with |- app_only (ogg_sync_buffer _ _ _ _ _) => apply app_sync_buffer end
| match goal with |- app_only (page_loop _ _ _ _ _ _ _ _ _ _ _ _) => apply app_page_loop end
| match goal with |- app_only (chunk_loop _ _ _ _ _ _ _ _ _ _ _ _ _) => apply IH end
| app_step ]).
Qed.

Lemma prun_destroy : forall d q, prun (speex_decoder_destroy (St := pst) p_free d) q = Some (tt, q).
Proof.
induction d as [st | st low IH]; intros q; cbn [speex_decoder_destroy]; [reflexivity|].
rewrite prun_bind, IH. reflexivity.
Qed.
Lemma prun_cleanup : forall (h : hstate unit) q, prun (hP_cleanup h) q = Some (tt, q).
Proof.
intros h q. unfold hP_cleanup, cleanup, h_decoder_destroy. rewrite prun_bind.
destruct (h_st h) as [d|]; [rewrite prun_destroy| rewrite prun_ret]; cbn beta iota;
unfold speex_bits_destroy, ogg_stream_clear, ogg_sync_clear, mfree_opt;
destruct (negb (sb_owner (h_bits h) =? 0)), (negb (h_stream_init h =? 0)), (os_body_data (h_os h)), (os_lacing_vals (h_os h)),
(os_granule_vals (h_os h)), (sy_data (h_oy h)); reflexivity.
Qed.
