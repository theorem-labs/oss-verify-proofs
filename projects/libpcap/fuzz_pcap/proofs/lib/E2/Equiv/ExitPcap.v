(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import String ZArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt PcapPrelim PcapTypes PcapPure Pcap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PcapOK.
Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).
Variable OK : forall A : Type, M A -> Prop.

(* [comment removed for export] *)
Record prims_ok : Prop := mkPrimsOk {
  ok_ret : forall A (a : A), OK A (mo_ret MO a);
  ok_bind : forall A B (m : M A) (f : A -> M B), OK A m -> (forall a, OK B (f a)) -> OK B (mo_bind MO m f);
  ok_unr : forall A, OK A (mo_unr MO);
  ok_fopen_r : forall n, OK _ (e_fopen_r P n);
  ok_fopen_w : forall n, OK _ (e_fopen_w P n);
  ok_fclose : forall f, OK _ (e_fclose P f);
  ok_fread : forall f d n, OK _ (e_fread P f d n);
  ok_fwrite : forall f s, OK _ (e_fwrite P f s);
  ok_ferror : forall f, OK _ (e_ferror P f);
  ok_fileno : forall f, OK _ (e_fileno P f);
  ok_last_errno : OK _ (e_last_errno P);
  ok_fprintf : forall f ps, OK _ (e_fprintf P f ps);
  ok_printf : forall ps, OK _ (e_printf P ps);
  ok_malloc : forall n, OK _ (e_malloc P n);
  ok_calloc : forall m n, OK _ (e_calloc P m n);
  ok_realloc : forall q n, OK _ (e_realloc P q n);
  ok_free : forall q, OK _ (e_free P q);
  ok_mkstemp : forall t, OK _ (e_mkstemp P t);
  ok_close_fd : forall fd, OK _ (e_close_fd P fd);
  ok_remove : forall n, OK _ (e_remove P n);
  ok_unlink : forall n, OK _ (e_unlink P n);
  ok_get_outfile : OK _ (e_get_outfile P);
  ok_set_outfile : forall o, OK _ (e_set_outfile P o);
  ok_fenter : forall A f (m : M A), OK A m -> OK A (e_fenter P f m);
  ok_fret : forall A f (x : A), OK A (e_fret P f x)
}.

Hypothesis HOK : prims_ok.

Let K_fopen_r := ok_fopen_r HOK.
Let K_fopen_w := ok_fopen_w HOK.
Let K_fclose := ok_fclose HOK.
Let K_fread := ok_fread HOK.
Let K_fwrite := ok_fwrite HOK.
Let K_ferror := ok_ferror HOK.
Let K_fileno := ok_fileno HOK.
Let K_last_errno := ok_last_errno HOK.
Let K_fprintf := ok_fprintf HOK.
Let K_printf := ok_printf HOK.
Let K_malloc := ok_malloc HOK.
Let K_calloc := ok_calloc HOK.
Let K_realloc := ok_realloc HOK.
Let K_free := ok_free HOK.
Let K_mkstemp := ok_mkstemp HOK.
Let K_close_fd := ok_close_fd HOK.
Let K_remove := ok_remove HOK.
Let K_unlink := ok_unlink HOK.
Let K_get_outfile := ok_get_outfile HOK.
Let K_set_outfile := ok_set_outfile HOK.
Local Hint Resolve K_fopen_r K_fopen_w K_fclose K_fread K_fwrite K_ferror K_fileno K_last_errno K_fprintf K_printf K_malloc K_calloc K_realloc K_free K_mkstemp K_close_fd K_remove K_unlink K_get_outfile K_set_outfile : pcapok.

Ltac ok_step :=
  lazymatch goal with
  | |- OK _ (mo_bind _ _ _) => apply (ok_bind HOK); [| intros ?]
  | |- OK _ (mo_ret _ _) => apply (ok_ret HOK)
  | |- OK _ (mo_unr _) => apply (ok_unr HOK)
  | |- OK _ (e_fenter _ _ _) => apply (ok_fenter HOK)
  | |- OK _ (e_fret _ _ _) => apply (ok_fret HOK)
  | |- OK _ (match ?x with _ => _ end) => destruct x
  | |- OK _ (let _ := _ in _) => cbv zeta
  | |- OK _ _ => solve [auto with pcapok nocore]
  end.
Ltac ok_go := repeat (cbv beta; ok_step).

Lemma ok_free_opt q : OK _ (free_opt MO P q).
Proof. unfold free_opt. ok_go. Qed.
Local Hint Resolve ok_free_opt : pcapok.

Lemma ok_errmsg_for_errno f a : OK _ (errmsg_for_errno MO P f a).
Proof. unfold errmsg_for_errno. ok_go. Qed.
Local Hint Resolve ok_errmsg_for_errno : pcapok.

Lemma ok_read_fail_msg fp t : OK _ (read_fail_msg MO P fp t).
Proof. unfold read_fail_msg. ok_go. Qed.
Local Hint Resolve ok_read_fail_msg : pcapok.

Lemma ok_open_offline_common n : OK _ (pcapint_open_offline_common MO P n).
Proof. unfold pcapint_open_offline_common. ok_go. Qed.
Local Hint Resolve ok_open_offline_common : pcapok.

Lemma ok_pcap_check_header mg fp pr : OK _ (pcap_check_header MO P mg fp pr).
Proof. unfold pcap_check_header. ok_go. Qed.
Local Hint Resolve ok_pcap_check_header : pcapok.

Lemma ok_grow_buffer p n : OK _ (grow_buffer MO P p n).
Proof. unfold grow_buffer. ok_go. Qed.
Local Hint Resolve ok_grow_buffer : pcapok.

Lemma ok_discard_loop fuel : forall fp c b r, OK _ (discard_loop MO P fuel fp c b r).
Proof. induction fuel as [|fuel IH]; intros fp c b r; cbn [discard_loop]; ok_go. Qed.
Local Hint Resolve ok_discard_loop : pcapok.

Lemma ok_pcap_next_packet p : OK _ (pcap_next_packet MO P p).
Proof. unfold pcap_next_packet. ok_go. Qed.
Local Hint Resolve ok_pcap_next_packet : pcapok.

Lemma ok_read_bytes fp d n b : OK _ (read_bytes MO P fp d n b).
Proof. unfold read_bytes. ok_go. Qed.
Local Hint Resolve ok_read_bytes : pcapok.

Lemma ok_read_block a p : OK _ (read_block MO P a p).
Proof. unfold read_block. ok_go. Qed.
Local Hint Resolve ok_read_block : pcapok.

Lemma ok_add_interface p o c : OK _ (add_interface MO P p o c).
Proof. unfold add_interface. ok_go. Qed.
Local Hint Resolve ok_add_interface : pcapok.

Lemma ok_ng_find_idb fuel : forall p, OK _ (ng_find_idb MO P fuel p).
Proof. induction fuel as [|fuel IH]; intros p; cbn [ng_find_idb]; ok_go. Qed.
Local Hint Resolve ok_ng_find_idb : pcapok.

Lemma ok_pcap_ng_check_header fuel mg fp pr : OK _ (pcap_ng_check_header MO P fuel mg fp pr).
Proof. unfold pcap_ng_check_header. ok_go. Qed.
Local Hint Resolve ok_pcap_ng_check_header : pcapok.

Lemma ok_ng_scan_blocks fuel : forall p, OK _ (ng_scan_blocks MO P fuel p).
Proof. induction fuel as [|fuel IH]; intros p; cbn [ng_scan_blocks]; ok_go. Qed.
Local Hint Resolve ok_ng_scan_blocks : pcapok.

Lemma ok_pcap_ng_next_packet fuel p : OK _ (pcap_ng_next_packet MO P fuel p).
Proof. unfold pcap_ng_next_packet. ok_go. Qed.
Local Hint Resolve ok_pcap_ng_next_packet : pcapok.

Lemma ok_next_packet_op fuel p : OK _ (next_packet_op MO P fuel p).
Proof. unfold next_packet_op. ok_go. Qed.
Local Hint Resolve ok_next_packet_op : pcapok.

Lemma ok_offline_read_1 fuel p : OK _ (pcapint_offline_read_1 MO P fuel p).
Proof. unfold pcapint_offline_read_1. ok_go. Qed.
Local Hint Resolve ok_offline_read_1 : pcapok.

Lemma ok_pcap_next_ex fuel p : OK _ (pcap_next_ex MO P fuel p).
Proof. unfold pcap_next_ex. ok_go. Qed.
Local Hint Resolve ok_pcap_next_ex : pcapok.

Lemma ok_pcap_stats p : OK _ (pcap_stats MO (fh:=fh) (ptr:=ptr) p).
Proof. unfold pcap_stats. ok_go. Qed.
Local Hint Resolve ok_pcap_stats : pcapok.

Lemma ok_sf_cleanup p : OK _ (pcapint_sf_cleanup MO P p).
Proof. unfold pcapint_sf_cleanup. ok_go. Qed.
Local Hint Resolve ok_sf_cleanup : pcapok.

Lemma ok_ng_cleanup p : OK _ (pcap_ng_cleanup MO P p).
Proof. unfold pcap_ng_cleanup. ok_go. Qed.
Local Hint Resolve ok_ng_cleanup : pcapok.

Lemma ok_pcap_close p : OK _ (pcap_close MO P p).
Proof. unfold pcap_close. ok_go. Qed.
Local Hint Resolve ok_pcap_close : pcapok.

Lemma ok_fopen_offline fuel fp pr : OK _ (pcap_fopen_offline_with_tstamp_precision MO P fuel fp pr).
Proof. unfold pcap_fopen_offline_with_tstamp_precision. ok_go. Qed.
Local Hint Resolve ok_fopen_offline : pcapok.

Lemma ok_open_offline_prec fuel n pr : OK _ (pcap_open_offline_with_tstamp_precision MO P fuel n pr).
Proof. unfold pcap_open_offline_with_tstamp_precision. ok_go. Qed.
Local Hint Resolve ok_open_offline_prec : pcapok.

Lemma ok_open_offline fuel n : OK _ (pcap_open_offline MO P fuel n).
Proof. unfold pcap_open_offline. ok_go. Qed.
Local Hint Resolve ok_open_offline : pcapok.

Lemma ok_bufferToFile n d : OK _ (bufferToFile MO P n d).
Proof. unfold bufferToFile. ok_go. Qed.
Local Hint Resolve ok_bufferToFile : pcapok.

Lemma ok_with_outfile {A} (k : fh -> M A) : (forall f, OK _ (k f)) -> OK _ (with_outfile MO P k).
Proof. intros Hk. unfold with_outfile. ok_go. Qed.

Ltac ok_step2 :=
  lazymatch goal with
  | |- OK _ (with_outfile _ _ _) => apply ok_with_outfile; intros ?
  | _ => ok_step
  end.
Ltac ok_go2 := repeat (cbv beta; ok_step2).

Lemma ok_packet_loop fuel : forall ng p, OK _ (packet_loop MO P fuel ng p).
Proof. induction fuel as [|fuel IH]; intros ng p; cbn [packet_loop]; ok_go2. Qed.
Local Hint Resolve ok_packet_loop : pcapok.

Theorem ok_LLVMFuzzerTestOneInput data : OK _ (LLVMFuzzerTestOneInput MO P data).
Proof. unfold LLVMFuzzerTestOneInput. ok_go2. Qed.

End PcapOK.
