(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Eg3i DA_Cells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cbn_mf := unfold mf_set_w, mf_set_rp, mf_set_mode, mf_set_flags, mf_set_buf, mf_set_write_lbf, stdout_buffered, stdout0, stderr0;
  cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
       mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148].
Ltac cbn_mf_in H := unfold mf_set_w, mf_set_rp, mf_set_mode, mf_set_flags, mf_set_buf, mf_set_write_lbf, stdout_buffered, stdout0, stderr0 in H;
  cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
       mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in H.
Ltac cbn_mf_all := unfold mf_set_w, mf_set_rp, mf_set_mode, mf_set_flags, mf_set_buf, mf_set_write_lbf, stdout_buffered, stdout0, stderr0 in *;
  cbn [mf_flags mf_rpos mf_rend mf_close mf_wend mf_wpos mf_mbz1 mf_wbase mf_read mf_write mf_seek mf_buf mf_bufsize
       mf_prev mf_next mf_fd mf_pipepid mf_lockcount mf_mode mf_lock mf_lbf mf_pad148] in *.

Lemma rw_cells_recast_pf : forall segs m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros segs m A cs cs' [[W B] WR] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact WR.
Qed.

Definition pfile5 (f : mfile) : list cell :=
  C1 (Z_to_bv 8 5) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: tl (file_cells f).

Lemma pfile5_wf : forall f, cells_wf (pfile5 f).
Proof. intros f. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit. Qed.
Lemma pfile5_bytes : forall f, mf_flags f = 5 -> cells_bytes (pfile5 f) = cells_bytes (file_cells f).
Proof. intros f FL. unfold pfile5, file_cells. rewrite FL. cbn [tl cells_bytes cbytes]. rewrite <- (le4_lit 5) by lia. reflexivity. Qed.
Lemma file_at_p5 : forall m Fa f, mf_flags f = 5 -> file_at m Fa f -> rw_cells rsegs m Fa (pfile5 f).
Proof. intros m Fa f FL H. exact (rw_cells_recast_pf rsegs m Fa _ _ H (pfile5_wf f) (pfile5_bytes f FL)). Qed.
Lemma file_p5_at : forall m Fa f, mf_flags f = 5 -> rw_cells rsegs m Fa (pfile5 f) -> file_at m Fa f.
Proof.
  intros m Fa f FL H. refine (rw_cells_recast_pf rsegs m Fa _ _ H _ (eq_sym (pfile5_bytes f FL))).
  cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit.
Qed.
