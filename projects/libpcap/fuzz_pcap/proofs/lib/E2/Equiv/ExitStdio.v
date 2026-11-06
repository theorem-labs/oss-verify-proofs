(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import HaltsAdq ExitBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Core.
Context {St : Type}.

Lemma mne_towrite f : mne (St:=St) (towrite f).
Proof. unfold towrite. mne_go. Qed.
Hint Resolve mne_towrite : mne.

Lemma mne_ensure_w f : mne (St:=St) (ensure_w f).
Proof. unfold ensure_w. mne_go. Qed.
Hint Resolve mne_ensure_w : mne.

Lemma noexit_wnode f iovs : noexit (wnode f iovs).
Proof. unfold wnode. destruct (f_chan f); exact I. Qed.

Lemma mne_writev_loop fuel : forall f iovs rem, mne (St:=St) (writev_loop fuel f iovs rem).
Proof.
  induction fuel as [|fuel IH]; intros f iovs rem; cbn [writev_loop]; [apply mne_unr|].
  apply mne_bind; [apply mne_sys; apply noexit_wnode|]. intros cnt. destruct (cnt =? rem); [apply mne_ret| apply IH].
Qed.
Hint Resolve mne_writev_loop : mne.

Lemma mne_stdio_write f s : mne (St:=St) (stdio_write f s).
Proof. unfold stdio_write. mne_go. Qed.
Hint Resolve mne_stdio_write : mne.

Lemma mne_file_writefn f s : mne (St:=St) (file_writefn f s).
Proof. unfold file_writefn. mne_go. Qed.
Hint Resolve mne_file_writefn : mne.

Lemma mne_fwritex f s : mne (St:=St) (fwritex f s).
Proof. unfold fwritex. mne_go. Qed.
Hint Resolve mne_fwritex : mne.

Lemma mne_fwrite_file f s : mne (St:=St) (fwrite_file f s).
Proof. unfold fwrite_file. mne_go. Qed.
Hint Resolve mne_fwrite_file : mne.

Lemma mne_out_pieces ps : forall f, mne (St:=St) (out_pieces f ps).
Proof. induction ps as [|p ps IH]; intros f; cbn [out_pieces]; [apply mne_ret|]. apply mne_bind; [apply mne_fwritex| intros f'; apply IH]. Qed.
Hint Resolve mne_out_pieces : mne.

Lemma mne_vfprintf f ps : mne (St:=St) (vfprintf f ps).
Proof. unfold vfprintf. mne_go. Qed.
Hint Resolve mne_vfprintf : mne.

Lemma mne_toread f : mne (St:=St) (toread f).
Proof. unfold toread. mne_go. Qed.
Hint Resolve mne_toread : mne.

Lemma mne_stdio_read f b d l : mne (St:=St) (stdio_read f b d l).
Proof. unfold stdio_read. mne_go. Qed.
Hint Resolve mne_stdio_read : mne.

Lemma mne_fread_loop fuel : forall f b d l acc, mne (St:=St) (fread_loop fuel f b d l acc).
Proof. induction fuel as [|fuel IH]; intros f b d l acc; cbn [fread_loop]; mne_go. Qed.
Hint Resolve mne_fread_loop : mne.

Lemma mne_fread_file f b d n : mne (St:=St) (fread_file f b d n).
Proof. unfold fread_file. mne_go. Qed.
Hint Resolve mne_fread_file : mne.

Lemma mne_sync_read_pos f : mne (St:=St) (sync_read_pos f).
Proof. unfold sync_read_pos. mne_go. Qed.
Hint Resolve mne_sync_read_pos : mne.

Lemma mne_fflush_file f : mne (St:=St) (fflush_file f).
Proof. unfold fflush_file. mne_go. Qed.
Hint Resolve mne_fflush_file : mne.

Lemma mne_close_file f : mne (St:=St) (close_file f).
Proof. unfold close_file. mne_go. Qed.
Hint Resolve mne_close_file : mne.

Lemma mne_fclose_file f : mne (St:=St) (fclose_file f).
Proof. unfold fclose_file. mne_go. Qed.
Hint Resolve mne_fclose_file : mne.
End Core.

#[export] Hint Resolve mne_towrite mne_ensure_w mne_writev_loop mne_stdio_write mne_file_writefn mne_fwritex mne_fwrite_file
  mne_out_pieces mne_vfprintf mne_toread mne_stdio_read mne_fread_loop mne_fread_file mne_sync_read_pos mne_fflush_file
  mne_close_file mne_fclose_file : mne.

Section Stdio.
Context {St ptr : Type}.
Context (get_lc : St -> libc_st ptr) (set_lc : libc_st ptr -> St -> St).
Variable ptr_eqb : ptr -> ptr -> bool.
Variable malloc : Z -> M St (option ptr).
Variable free : ptr -> M St unit.
Variable buf_addr : St -> ptr -> Z.
Hypothesis MALLOC : forall n, mne (malloc n).
Hypothesis FREE : forall p, mne (free p).
Hint Resolve MALLOC FREE : mne.

Lemma mne_rd_lc : mne (rd_lc get_lc).
Proof. unfold rd_lc. mne_go. Qed.
Hint Resolve mne_rd_lc : mne.
Lemma mne_upd_lc g : mne (upd_lc get_lc set_lc g).
Proof. unfold upd_lc. mne_go. Qed.
Hint Resolve mne_upd_lc : mne.
Lemma mne_set_errno e : mne (set_errno get_lc set_lc e).
Proof. unfold set_errno. mne_go. Qed.
Hint Resolve mne_set_errno : mne.
Lemma mne_get_errno : mne (get_errno get_lc).
Proof. unfold get_errno. mne_go. Qed.
Hint Resolve mne_get_errno : mne.
Lemma mne_lookup_file h : mne (lookup_file get_lc ptr_eqb h).
Proof. unfold lookup_file. mne_go. Qed.
Hint Resolve mne_lookup_file : mne.
Lemma mne_store_file h f : mne (store_file get_lc set_lc ptr_eqb h f).
Proof. unfold store_file. mne_go. Qed.
Hint Resolve mne_store_file : mne.
Lemma mne_with_file {A} h (op : file_st -> M St (A * file_st)) : (forall f, mne (op f)) -> mne (with_file get_lc set_lc ptr_eqb h op).
Proof. intros Hop. unfold with_file. mne_go. Qed.
Lemma mne_with_file_ h (op : file_st -> M St file_st) : (forall f, mne (op f)) -> mne (with_file_ get_lc set_lc ptr_eqb h op).
Proof. intros Hop. unfold with_file_. mne_go. Qed.
Ltac mne_extra ::=
  lazymatch goal with
  | |- mne (with_file _ _ _ _ _) => apply mne_with_file; intros ?
  | |- mne (with_file_ _ _ _ _ _) => apply mne_with_file_; intros ?
  end.

Lemma mne_fopen name wr : mne (fopen get_lc set_lc malloc name wr).
Proof. unfold fopen. mne_go. Qed.
Lemma mne_fclose h : mne (fclose get_lc set_lc ptr_eqb free h).
Proof. unfold fclose. mne_go. Qed.
Lemma mne_fwrite h s : mne (fwrite get_lc set_lc ptr_eqb h s).
Proof. unfold fwrite. mne_go. Qed.
Lemma mne_fread h d n : mne (fread get_lc set_lc ptr_eqb buf_addr h d n).
Proof. unfold fread. mne_go. Qed.
Lemma mne_ferror h : mne (ferror get_lc ptr_eqb h).
Proof. unfold ferror. mne_go. Qed.
Lemma mne_fileno h : mne (fileno get_lc ptr_eqb h).
Proof. unfold fileno. mne_go. Qed.
Lemma mne_feof h : mne (feof get_lc ptr_eqb h).
Proof. unfold feof. mne_go. Qed.
Lemma mne_fprintf h ps : mne (fprintf get_lc set_lc ptr_eqb h ps).
Proof. unfold fprintf. mne_go. Qed.
Lemma mne_printf ps : mne (printf get_lc set_lc ps).
Proof. unfold printf. mne_go. Qed.
Lemma mne_eprintf ps : mne (eprintf get_lc set_lc ps).
Proof. unfold eprintf. mne_go. Qed.
Lemma mne_efwrite s : mne (efwrite get_lc set_lc s).
Proof. unfold efwrite. mne_go. Qed.
Lemma mne_remove p : mne (remove get_lc set_lc p).
Proof. unfold remove. mne_go. Qed.
Lemma mne_unlink p : mne (unlink get_lc set_lc p).
Proof. unfold unlink. mne_go. Qed.
Lemma mne_mkstemp t : mne (mkstemp get_lc set_lc t).
Proof. unfold mkstemp. mne_go. Qed.
Lemma mne_close fd : mne (St:=St) (close fd).
Proof. unfold close. mne_go. Qed.
Lemma mne_close_files (fs : list (ptr * file_st)) : mne (St:=St) (close_files fs).
Proof. induction fs as [|[q f] fs IH]; cbn [close_files]; mne_go. Qed.
Hint Resolve mne_close_files : mne.
Lemma mne_stdio_exit : mne (stdio_exit get_lc).
Proof. unfold stdio_exit. mne_go. Qed.

Hint Resolve mne_eprintf mne_efwrite mne_printf : mne.
Lemma mne_diag_usage a : mne (diag_usage get_lc set_lc a).
Proof. unfold diag_usage. mne_go. Qed.
Lemma mne_diag_cannot_open p : mne (diag_cannot_open get_lc set_lc p).
Proof. unfold diag_cannot_open. mne_go. Qed.
Lemma mne_diag_read_error p : mne (diag_read_error get_lc set_lc p).
Proof. unfold diag_read_error. mne_go. Qed.
Lemma mne_diag_oom : mne (diag_oom get_lc set_lc).
Proof. unfold diag_oom. mne_go. Qed.
Lemma mne_diag_too_big : mne (diag_too_big get_lc set_lc).
Proof. unfold diag_too_big. mne_go. Qed.
Lemma mne_diag_short_hdr : mne (diag_short_hdr get_lc set_lc).
Proof. unfold diag_short_hdr. mne_go. Qed.
Lemma mne_diag_cfg_overrun : mne (diag_cfg_overrun get_lc set_lc).
Proof. unfold diag_cfg_overrun. mne_go. Qed.
Lemma mne_emit_d rc : mne (emit_d get_lc set_lc rc).
Proof. unfold emit_d. mne_go. Qed.
End Stdio.
