(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac ApErrKit ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sk_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I2D_SCT_LIST : Z := 0x19d410.              (* [comment removed for export] *)
Definition I2O_SCT_LIST : Z := 0x19d0f0.              (* [comment removed for export] *)
Definition I2O_SCT : Z := 0x19cb64.                   (* [comment removed for export] *)
Definition I2O_SCT_SIGNATURE : Z := 0x19c9f8.         (* [comment removed for export] *)
Definition SCT_IS_COMPLETE : Z := 0x19d70c.           (* [comment removed for export] *)
Definition SCT_SIGNATURE_IS_COMPLETE : Z := 0x19d774. (* [comment removed for export] *)
Definition ASN1_OCTET_STRING_NEW : Z := 0x1150d8.     (* [comment removed for export] *)
Definition ASN1_STRING_SET0 : Z := 0xfe16c.           (* [comment removed for export] *)
Definition I2D_ASN1_OCTET_STRING : Z := 0x1150b0.     (* [comment removed for export] *)
Definition ASN1_ITEM_EX_I2D : Z := 0x11555c.          (* [comment removed for export] *)
Definition ASN1_EX_I2C : Z := 0x1162f0.               (* [comment removed for export] *)
Definition ASN1_PUT_OBJECT : Z := 0xfdb50.            (* [comment removed for export] *)
Definition ASN1_OBJECT_SIZE : Z := 0xfdd5c.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_I2O_SCT : Z := 0x21b0e.                  (* [comment removed for export] *)
Definition A_I2O_SCT_LIST : Z := 0x1de70.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition I2D_SCT_LIST_STACK : Z := 64 + 96 + 96 + 64 + ERR_SET_ERROR_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i2d_sct_list_cps {B : Type} (k : skr bptr) (kont : option bptr -> AM B) : AM B :=
  r <- i2o_len_pass (sk_items k) 2 ;;
  match r with
  | None => kont None
  | Some len2 =>
      if MAX_SCT_LIST_SIZE <? len2 then err_raise RS_i2o_list ;;; kont None
      else
        data <- amalloc len2 ;;
        oct <- amalloc SZ_ASN1_STRING ;;
        der <- amalloc (der_hl len2 + len2) ;;
        afree data ;;; afree oct ;;; kont (Some der)
  end.

Lemma i2d_sct_list_cps_eq : forall (k : skr bptr) (st : ap_st bptr), i2d_sct_list k st = i2d_sct_list_cps k afree_opt st.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i2d_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (adr : bptr -> Z) (k : skr bptr) (DER : Z)
    (r : option bptr * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo' (NEW : list block),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall q : reg, bv_unsigned q <> 10 -> reg_get F' q = reg_get F q)
    /\ ap_pre s' (snd r) m' OW' (NEW ++ LB) E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(DER, DER + 8)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ sk_rep m' LB adr k
    /\ match fst r with
       | None => NEW = [] /\ rw_cells ctusegs m' DER [C8 (wz 0)]
       | Some d => exists AD n, NEW = [(d, AD, n)] /\ 0 < n /\ rw_cells ctusegs m' DER [C8 (wz AD)]
       end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition i2d_sct_list_spec : Prop :=
  forall (B0 : Type) (kont : option bptr -> AM B0) (Q : B0 * ap_st bptr -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (k : skr bptr) (DER : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary I2D_SCT_LIST_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    sk_rep m LB adr k ->
    bv_unsigned sp <= DER -> DER + 8 <= B -> rw_cells ctusegs m DER [C8 (wz 0)] -> DER mod 8 = 0 ->
    a0 = wz (adr (sk_blk k)) -> a1 = wz DER ->
    (forall st' s' ms', i2d_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr k DER (None, st') s' ms' ->
                        implM ctusegs (interp (ap_embed (kont None st'))) s' Q ms') ->
    (forall d st' s' ms', i2d_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr k DER (Some d, st') s' ms' ->
                          implM ctusegs (interp (ap_embed (kont (Some d) st'))) s' Q ms') ->
    implM ctusegs (interp (ap_embed (i2d_sct_list_cps k kont st))) s Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz I2D_SCT_LIST) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Lemma i2d_sct_list_of_spec : i2d_sct_list_spec ->
  forall (Q : unit * ap_st bptr -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (k : skr bptr) (DER : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary I2D_SCT_LIST_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    sk_rep m LB adr k ->
    bv_unsigned sp <= DER -> DER + 8 <= B -> rw_cells ctusegs m DER [C8 (wz 0)] -> DER mod 8 = 0 ->
    a0 = wz (adr (sk_blk k)) -> a1 = wz DER ->
    (forall st' s' ms', i2d_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr k DER (None, st') s' ms' ->
                        implM ctusegs (interp (ap_embed (aret tt st'))) s' Q ms') ->
    (forall d st' s' ms', i2d_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr k DER (Some d, st') s' ms' ->
                          implM ctusegs (interp (ap_embed (afree d st'))) s' Q ms') ->
    implM ctusegs (interp (ap_embed (i2d_sct_list k st))) s Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz I2D_SCT_LIST) fc None m (seg_rom ctusegs)).
Proof.
  intros W. intros. rewrite i2d_sct_list_cps_eq. eapply (W unit afree_opt); eassumption.
Qed.

End WithCeiling0.
