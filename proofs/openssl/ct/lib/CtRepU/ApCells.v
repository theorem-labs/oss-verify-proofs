(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Cells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog ApState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition c4s (l : list Z) : list cell := map (fun z => C4 (wz z)) l.
Definition c8s (l : list Z) : list cell := map (fun z => C8 (wz z)) l.
Definition optr (adr : bptr -> Z) (o : option (bptr * Z)) : Z := match o with Some (p, _) => adr p | None => 0 end.
Definition osize (o : option (bptr * Z)) : Z := match o with Some (_, n) => n | None => 0 end.
Definition zeros4 (n : nat) : list cell := repeat (C4 (wz 0)) n.

Lemma c4s_length l : length (c4s l) = length l. Proof. apply length_map. Qed.
Lemma c8s_length l : length (c8s l) = length l. Proof. apply length_map. Qed.
Lemma cells_size_app a b : cells_size (a ++ b) = (cells_size a + cells_size b)%nat.
Proof. induction a as [|c a IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma cells_size_c4s l : cells_size (c4s l) = (4 * length l)%nat.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. cbn in IH. rewrite IH. lia. Qed.
Lemma cells_size_c8s l : cells_size (c8s l) = (8 * length l)%nat.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. cbn in IH. rewrite IH. lia. Qed.
Lemma cells_size_zeros4 n : cells_size (zeros4 n) = (4 * n)%nat.
Proof. induction n as [|n IH]; cbn; [reflexivity|]. cbn in IH. rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ES_SIZE : Z := 904.
Definition ESO_FLAGS : Z := 0.     Definition ESO_MARKS : Z := 64.   Definition ESO_BUFFER : Z := 128.  Definition ESO_DATA : Z := 256.
Definition ESO_DSIZE : Z := 384.   Definition ESO_DFLAGS : Z := 512. Definition ESO_FILE : Z := 576.    Definition ESO_LINE : Z := 704.
Definition ESO_FUNC : Z := 768.    Definition ESO_TOP : Z := 896.    Definition ESO_BOTTOM : Z := 900.

Definition es_cells (st : ap_st bptr) (adr : bptr -> Z) : list cell :=
  zeros4 ERR_NUM
  ++ c4s (as_marks st)
  ++ c8s (as_buf st)
  ++ c8s (map (optr adr) (as_data st))
  ++ c8s (map osize (as_data st))
  ++ c4s (as_dflags st)
  ++ c8s (map (optr adr) (as_file st))
  ++ c4s (as_line st)
  ++ c8s (map (optr adr) (as_func st))
  ++ [C4 (wz (Z.of_nat (as_top st))); C4 (wz (Z.of_nat (as_bottom st)))].

(* [comment removed for export] *)
Definition es_shape (st : ap_st bptr) : Prop :=
  length (as_marks st) = ERR_NUM /\ length (as_buf st) = ERR_NUM /\ length (as_data st) = ERR_NUM /\ length (as_dflags st) = ERR_NUM
  /\ length (as_file st) = ERR_NUM /\ length (as_line st) = ERR_NUM /\ length (as_func st) = ERR_NUM.

Lemma es_cells_size st adr : es_shape st -> Z.of_nat (cells_size (es_cells st adr)) = ES_SIZE.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold es_cells.
  rewrite !cells_size_app, cells_size_zeros4, !cells_size_c4s, !cells_size_c8s, !length_map, H1, H2, H3, H4, H5, H6, H7. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_SIZE : Z := 128.
Definition BIOO_METHOD : Z := 8.  Definition BIOO_INIT : Z := 40.  Definition BIOO_PTR : Z := 64.  Definition BIOO_NEXT : Z := 72.
Definition BIOO_PREV : Z := 80.   Definition BIOO_REFS : Z := 88.  Definition BIOO_NWRITE : Z := 104.

Definition bio_cells (meth init ptr next prev nw : Z) : list cell :=
  [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz init); C4 (wz 1); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz ptr); C8 (wz next); C8 (wz prev);
   C4 (wz 1); C4 (wz 0);
   C8 (wz 0); C8 (wz nw); C8 (wz 0); C8 (wz 0)].

Lemma bio_cells_size meth init ptr next prev nw : Z.of_nat (cells_size (bio_cells meth init ptr next prev nw)) = BIO_SIZE.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition bio_null_cells (nullm prev nw : Z) : list cell := bio_cells nullm 1 0 0 prev nw.
(* [comment removed for export] *)
Definition bio_prefix_cells (prefm ctx next nw : Z) : list cell := bio_cells prefm 1 ctx next 0 nw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PREFIX_CTX_SIZE : Z := 16.
Definition prefix_ctx_cells (prefix indent linestart : Z) : list cell := [C8 (wz prefix); C4 (wz indent); C4 (wz linestart)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_OBJECT_SIZE : Z := 40.
Definition asn1_object_cells (sn ln nid len data flags : Z) : list cell :=
  [C8 (wz sn); C8 (wz ln); C4 (wz nid); C4 (wz len); C8 (wz data); C4 (wz flags); C4 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_STRING_SIZE : Z := 24.
Definition asn1_string_cells (len type data flags : Z) : list cell := [C4 (wz len); C4 (wz type); C8 (wz data); C8 (wz flags)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MUTEX_SIZE : Z := 40.
Definition mutex_free_cells : list cell := zeros4 10.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sa_cells (pad : list byte) (nodes : Z) : list cell := [C4 (wz 1); CB 4 pad; C8 (wz 0); C8 (wz 1); C8 (wz nodes)].
