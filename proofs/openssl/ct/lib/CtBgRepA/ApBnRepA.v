(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require BnRepDefs BnRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation ctasegs := ImageCtA.ctasegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation bn_cells := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.bn_cells.
Notation bn_arr := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.bn_arr.
Notation CRYPTO_FREE := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.CRYPTO_FREE.
Notation CRYPTO_MALLOC := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.CRYPTO_MALLOC.
Notation crypto_statics := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.crypto_statics.
Notation OSSL_BASE_INITED := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.OSSL_BASE_INITED.
Notation OSSL_DO_GLOBAL_CLEANUP := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.OSSL_DO_GLOBAL_CLEANUP.
Notation ossl_exit_cells := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepDefs.ossl_exit_cells.
Notation libw := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepA.libw.
Notation in_block_intro := OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepA.in_block_intro.

Section WithRT. Context {AR : ARun}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record err_addrs : Type := mkEA {
  ea_inv : mem -> Prop;                    (* [comment removed for export] *)
  ea_blks : list block;                    (* [comment removed for export] *)
  ea_rsv : list block;                     (* [comment removed for export] *)
  ea_law : forall m m', ea_inv m -> agree_on (fun x => libw x \/ in_block ea_blks x) m m' -> ea_inv m'
}.

(* [comment removed for export] *)
Definition ea_ids (EA : err_addrs) : list bptr := map blk_id (ea_blks EA ++ ea_rsv EA).

(* [comment removed for export] *)
Definition err_statics (m : mem) : Prop := True.
Definition err_mem (m : mem) (OW : list block) (EA : err_addrs) : Prop :=
  ea_inv EA m /\ (forall b, In b (ea_blks EA ++ ea_rsv EA) -> In b OW).
Definition err_inv (m : mem) (OW : list block) (EA : err_addrs) : Prop := err_statics m /\ err_mem m OW EA.

(* [comment removed for export] *)
Definition err_fp (OW : list block) (EA : err_addrs) (x : Z) : Prop := in_block (ea_blks EA) x.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma crypto_statics_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> crypto_statics m -> crypto_statics m'.
Proof. intros P m m' AG HP H. eapply OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepA.crypto_statics_agree; eauto. Qed.

Lemma err_statics_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> err_statics m -> err_statics m'.
Proof. intros; exact I. Qed.

Lemma err_mem_agree : forall P m m' OW OW' EA,
  agree_on P m m' -> (forall a, libw a -> P a) -> (forall x, err_fp OW EA x -> P x) ->
  (forall q A n, In q (ea_ids EA) -> In (q, A, n) OW -> In (q, A, n) OW') ->
  err_mem m OW EA -> err_mem m' OW' EA.
Proof.
  intros P m m' OW OW' EA AG HL HP HOW [HI HB]. split.
  - eapply (ea_law EA); [exact HI|]. intros a Ha Hx. apply (AG a Ha). destruct Hx as [Hx|Hx]; [apply HL; exact Hx| apply HP; exact Hx].
  - intros [[q A] n] Hin. apply HOW; [| apply HB; exact Hin]. unfold ea_ids. apply in_map_iff. exists (q, A, n). split; [reflexivity| exact Hin].
Qed.

Lemma ea_ids_blk : forall EA q A n, In (q, A, n) (ea_blks EA) -> In q (ea_ids EA).
Proof. intros EA q A n H. unfold ea_ids. apply in_map_iff. exists (q, A, n). split; [reflexivity| apply in_or_app; left; exact H]. Qed.
Lemma ea_ids_rsv : forall EA q A n, In (q, A, n) (ea_rsv EA) -> In q (ea_ids EA).
Proof. intros EA q A n H. unfold ea_ids. apply in_map_iff. exists (q, A, n). split; [reflexivity| apply in_or_app; right; exact H]. Qed.

Lemma ossl_exit_cells_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> ossl_exit_cells m -> ossl_exit_cells m'.
Proof. intros P m m' AG HP H. eapply OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA.BnRepA.ossl_exit_cells_agree; eauto. Qed.

(* [comment removed for export] *)
Lemma err_mem_blocks : forall m OW EA b, err_mem m OW EA -> In b (ea_blks EA ++ ea_rsv EA) -> In b OW.
Proof. intros m OW EA b [_ H] Hb. apply H. exact Hb. Qed.

End WithRT.
