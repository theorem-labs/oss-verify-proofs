(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse ApPrim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_c2i_ibuf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

Notation acibuf := CtRepP.W_c2i_ibuf.acibuf.
Notation ibuf_val := CtRepP.W_c2i_ibuf.ibuf_val.

Definition C2I_IBUF_A : Z := 0x245c58.
Definition C2I_INT_A : Z := 0x245a28.
(* [comment removed for export] *)
Definition A_A_INT_C_A : Z := 0x72fc0.
Definition A_C2I_IBUF_A : Z := 0x730c0.
(* [comment removed for export] *)
Definition C2I_IBUF_STACK_A : Z := 32 + ERR_SET_ERROR_STACK.
(* [comment removed for export] *)
Definition C2I_RAISE_COST_A : Z := 4.
Definition C2I_RAISE_FRAMES_A : Z := 2.
Definition c2i_costA (res : ibuf_res) : Z := match res with IbOk _ => 0 | _ => C2I_RAISE_COST_A end.
(* [comment removed for export] *)
Definition C2I_INT_STACK_A : Z := 80 + C2I_IBUF_STACK_A.

(* [comment removed for export] *)
Definition c2i_int_fragA (d : list Z) (cont plen : Z) : @AM bptr (option (astr bptr)) :=
  match c2i_ibuf_len d cont plen with
  | IbZero => err_raise RS_zero_content ;;; aret None
  | IbPad => err_raise RS_ill_padding ;;; aret None
  | IbOk r => blk <- amalloc SZ_ASN1_STRING ;; dp <- amalloc r ;; aret (Some (mkStr blk (Some (dp, r))))
  end.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition ibuf_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block)
    (res : ibuf_res) (r : unit * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz (ibuf_val res)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) LIBW_A m m'
    /\ rt_credit RT Σ - c2i_costA res <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'.

(* [comment removed for export] *)
Definition c2i_ibuf_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (D : Z) (d : list Z) (cont plen : Z),
    ap_preA Σ st m OW LB E bo sp lo C2I_IBUF_STACK_A C2I_RAISE_COST_A C2I_RAISE_FRAMES_A -> tp = wz TP_A ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> 0 < zlength d -> 0 <= cont -> 0 <= plen < 2^31 -> cont + plen <= zlength d ->
    a0 = wz 0 -> a1 = wz 0 -> a2 = wz (D + cont) -> a3 = wz plen ->
    implAp (acibuf d cont plen st) Σ
           (ibuf_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K (c2i_ibuf_len d cont plen))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz C2I_IBUF_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
Definition c2i_int_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block)
    (D cont plen PV PCONT : Z) (res : ibuf_res)
    (r : option (astr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ax_pres LB (bv_unsigned sp) ([(PV, PV + 8); (PCONT, PCONT + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - (C2I_RAISE_COST_A + mcost plen) <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ match fst r with
       | None => a0 = wz 0 /\ ap_preA Σ' (snd r) m' OW' LB E bo sp lo 0 0 0
                 /\ rw_cells ctasegs m' PV [C8 (wz 0)] /\ rw_cells ctasegs m' PCONT [C8 (wz (D + cont))]
       | Some x => exists blk dp (n A DA ty : Z) (bytes : list byte),
                   x = mkStr blk (Some (dp, n)) /\ n = ibuf_val res /\ 1 <= n <= plen /\ a0 = wz A /\ (ty = 2 \/ ty = 258)
                   /\ blk <> dp /\ ~ In blk (map blk_id (OW' ++ LB)) /\ ~ In dp (map blk_id (OW' ++ LB))
                   /\ ablock_range A ASN1_STRING_SIZE /\ ablock_range DA n
                   /\ AHEAP Σ' ((dp, DA, n) :: (blk, A, ASN1_STRING_SIZE) :: OW') LB m'
                   /\ ap_state (snd r) m' OW' E bo /\ ids_ok E (snd r) /\ data_cells m' OW' (snd r)
                   /\ stk ctasegs m' lo (bv_unsigned sp) /\ mem_inv ctasegs m' /\ 0 <= rt_credit RT Σ'
                   /\ rw_cells ctasegs m' A (asn1_string_cells n ty DA 0) /\ rw_cells ctasegs m' DA [CB (Z.to_nat n) bytes]
                   /\ rw_cells ctasegs m' PV [C8 (wz A)] /\ rw_cells ctasegs m' PCONT [C8 (wz (D + cont + plen))]
       end.

(* [comment removed for export] *)
Definition c2i_int_specA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (D : Z) (d : list Z) (cont plen PV PCONT : Z),
    ap_preA Σ st m OW LB E bo sp lo C2I_INT_STACK_A (C2I_RAISE_COST_A + mcost plen) C2I_RAISE_FRAMES_A -> tp = wz TP_A ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> 0 < zlength d -> 0 <= cont -> 0 <= plen < 2^31 -> cont + plen <= zlength d ->
    cellA_in LB PV 8 -> cellA_in LB PCONT 8 -> PV mod 8 = 0 -> PCONT mod 8 = 0 -> (PV + 8 <= PCONT \/ PCONT + 8 <= PV) ->
    (PV + 8 <= D \/ D + zlength d <= PV) -> (PCONT + 8 <= D \/ D + zlength d <= PCONT) ->
    rw_cells ctasegs m PV [C8 (wz 0)] -> rw_cells ctasegs m PCONT [C8 (wz (D + cont))] ->
    a0 = wz PV -> a1 = wz PCONT -> a2 = wz plen ->
    implAp (c2i_int_fragA d cont plen st) Σ
           (c2i_int_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K D cont plen PV PCONT (c2i_ibuf_len d cont plen))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz C2I_INT_A) fc None m (seg_rom ctasegs)).

End WithRT.
