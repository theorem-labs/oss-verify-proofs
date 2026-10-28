(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require EncStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation i2d_sct_list_cps := CtEncP.EncStmt.i2d_sct_list_cps.
Notation i2d_sct_list_cps_eq := CtEncP.EncStmt.i2d_sct_list_cps_eq.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I2D_SCT_LIST_A : Z := 0x3372c4.
Definition I2O_SCT_LIST_A : Z := 0x336b7c.
Definition I2O_SCT_A : Z := 0x3360d0.
Definition I2O_SCT_SIGNATURE_A : Z := 0x335dd8.
Definition SCT_IS_COMPLETE_A : Z := 0x337918.
Definition SCT_SIGNATURE_IS_COMPLETE_A : Z := 0x337a7c.
Definition ASN1_OCTET_STRING_NEW_A : Z := 0x246e5c.
Definition ASN1_OCTET_STRING_FREE_A : Z := 0x246e80.
Definition ASN1_STRING_SET0_A : Z := 0x224888.
Definition I2D_ASN1_OCTET_STRING_A : Z := 0x246e34.
Definition ASN1_ITEM_I2D_A : Z := 0x247478.
Definition ASN1_ITEM_FLAGS_I2D_A : Z := 0x2471bc.
Definition ASN1_ITEM_EX_I2D_A : Z := 0x24749c.
Definition ASN1_I2D_EX_PRIMITIVE_A : Z := 0x2485fc.
Definition ASN1_EX_I2C_A : Z := 0x2489c0.
Definition ASN1_PUT_OBJECT_A : Z := 0x223ee8.
Definition ASN1_OBJECT_SIZE_A : Z := 0x2241b0.
(* [comment removed for export] *)
Definition A_I2O_SCT_SIGNATURE_A : Z := 0xa7980.
Definition A_I2O_SCT_A : Z := 0xa79c0.           (* [comment removed for export] *)
Definition A_I2O_SCT_LIST_A : Z := 0xa7a00.      (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i2d_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (k : skr bptr) (DER : Z)
    (r : option bptr * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (NEW : list block),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(DER, DER + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ sk_repA m' LB adr k
    /\ match fst r with
       | None => NEW = [] /\ rw_cells ctasegs m' DER [C8 (wz 0)]
       | Some d => exists AD n, NEW = [(d, AD, n)] /\ 0 < n /\ rw_cells ctasegs m' DER [C8 (wz AD)]
       end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i2d_sct_list_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (B0 : Type) (kont : option bptr -> AM B0) (Q : B0 * ap_st bptr -> rts RT -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (k : skr bptr) (DER : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength (sk_items k))) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx I2D_SCT_LIST_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    sk_repA m LB adr k -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB DER 8 -> DER mod 8 = 0 -> (forall b, In b (sk_blocks adr k) -> DER + 8 <= blk_addr b \/ blk_addr b + blk_size b <= DER) ->
    rw_cells ctasegs m DER [C8 (wz 0)] ->
    a0 = wz (adr (sk_blk k)) -> a1 = wz DER ->
    (forall st' Σ' ms', i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength (sk_items k))) adr k DER (None, st') Σ' ms' ->
                        implAp (kont None st') Σ' Q ms') ->
    (forall d st' Σ' ms', i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength (sk_items k))) adr k DER (Some d, st') Σ' ms' ->
                          implAp (kont (Some d) st') Σ' Q ms') ->
    implAp (i2d_sct_list_cps k kont st) Σ Q
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz I2D_SCT_LIST_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
Lemma i2d_sct_list_of_specA : forall STK CST FRM, i2d_sct_list_specA STK CST FRM ->
  forall (Q : unit * ap_st bptr -> rts RT -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (k : skr bptr) (DER : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength (sk_items k))) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx I2D_SCT_LIST_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    sk_repA m LB adr k -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB DER 8 -> DER mod 8 = 0 -> (forall b, In b (sk_blocks adr k) -> DER + 8 <= blk_addr b \/ blk_addr b + blk_size b <= DER) ->
    rw_cells ctasegs m DER [C8 (wz 0)] ->
    a0 = wz (adr (sk_blk k)) -> a1 = wz DER ->
    (forall st' Σ' ms', i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength (sk_items k))) adr k DER (None, st') Σ' ms' ->
                        implAp (aret tt st') Σ' Q ms') ->
    (forall d st' Σ' ms', i2d_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength (sk_items k))) adr k DER (Some d, st') Σ' ms' ->
                          implAp (afree d st') Σ' Q ms') ->
    implAp (i2d_sct_list k st) Σ Q
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz I2D_SCT_LIST_A) fc None m (seg_rom ctasegs)).
Proof.
  intros STK CST FRM W. intros. rewrite i2d_sct_list_cps_eq. eapply (W unit afree_opt); eassumption.
Qed.

End WithRT.
