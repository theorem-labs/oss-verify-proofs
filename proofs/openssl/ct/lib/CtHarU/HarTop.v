(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg LibOps CtSizes CtWire CtModel CtBridge ApBase ApState ApInv ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface RRealloc_iface RF_malloc_spec RF_free_spec RF_realloc_spec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts HxpLaws HxpInstAp HxpFinal HxpLinv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface W_err_clear_error.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctStmt W_d2i_sct_list.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeIfaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnTimeIface W_sct_print W_sct_list_print.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncStmt W_i2d_sct_list.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarU Require Import W_fuzz_one.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import W_get_object_walk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import W_d2i_octet.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition linvP : ap_ls bptr -> (word -> option byte) -> list MallocBlocks.block -> Prop := ct_lib_inv3.
Lemma linvP_init : forall m OW, HxpFinal.ap_init_facts m OW -> linvP ap_ls0 m OW.
Proof. intros m OW H. exact (ct_lib_inv3_init_of2 m OW (HxpLinv.linv_init m OW H)). Qed.
Lemma linvP_agree : forall ls OW m m', linvP ls m OW ->
  Lib_kit.agree_on (fun a => Lib_iface.rin_ivs HxpInit.LIBW_HX a \/ in_block OW a) m m' -> linvP ls m' OW.
Proof. intros ls OW m m' H A. exact (ct_lib_inv3_agree ls OW m m' H A). Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition HPRINT_P : SCT_LIST_print_spec TIME_STACK :=
  SCT_LIST_print_walk TIME_STACK rmalloc_spec rfree_spec_proof
    (time_adj_ok rmalloc_spec) time_adj_fail time_setstr_ok time_setstr_fail time_print.
Definition HI2D_P : i2d_sct_list_spec := i2d_sct_list_ok rmalloc_spec rfree_spec_proof.
Definition HCLR_P : ERR_clear_error_spec := ERR_clear_error_walk rfree_spec_proof.

(* [comment removed for export] *)
Definition D2IOCT_P : d2i_octet_spec := d2i_octet_walk rmalloc_spec rfree_spec_proof (ASN1_get_object_walk rmalloc_spec rfree_spec_proof).
Definition HD2I_P : d2i_sct_list_spec := d2i_sct_list_walk rmalloc_spec rfree_spec_proof rrealloc_spec D2IOCT_P.

Theorem rfuzz_one_ct_closed :
  rfuzz_one_stmt (LM := @LM_ap (ap_ls bptr) ct_ls0 ct_lib_one) (LSP := @LSP_ap (ap_ls bptr) ct_ls0 ct_lib_one linvP).
Proof.
  exact (rfuzz_one_ct rmalloc_spec rfree_spec_proof TIME_STACK ltac:(unfold TIME_STACK; lia) HD2I_P HPRINT_P HI2D_P HCLR_P).
Qed.
End WithCeiling0.
