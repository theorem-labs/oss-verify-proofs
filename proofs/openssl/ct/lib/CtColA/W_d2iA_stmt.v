(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA W_check_tlenA W_item_d2i_stmtA W_item_d2i_imgA W_item_d2i_internA W_item_d2i_exA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import Fr_asn1_d2i_ex_primitive.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition d2i_exprim (d : list Z) (len : Z) : AM (option (octet bptr)) :=
  let g := get_object d 0 len in
  match go_err g with
  | Some e => tlen_fail e ;;; err_raise RS_prim_nested ;;; aret None
  | None =>
      if negb (go_tag g =? V_ASN1_OCTET_STRING) || negb (go_cls g =? 0)
      then err_raise RS_tlen_wrong_tag ;;; err_raise RS_prim_nested ;;; aret None
      else
        let p := go_p g in
        let inf := Z.testbit (go_ret g) 0 in
        let cst := negb (Z.land (go_ret g) 32 =? 0) in
        let plen := if inf then len - p else go_len g in
        if cst then
          ' (b, r) <- collect (ct_fuel d) d buf0 p plen inf 0 ;;
          match r with
          | None => afree_opt (option_map fst (bm_data b)) ;;; aret None
          | Some _ =>
              let l := bm_len b in
              b2 <- buf_grow_clean b (l + 1) ;;
              blk <- amalloc SZ_ASN1_STRING ;;
              aret (Some (mkOct blk (bm_data b2) l (firstn (Z.to_nat l) (bm_bytes b2))))
          end
        else
          blk <- amalloc SZ_ASN1_STRING ;;
          dp <- amalloc_crypto plen ;;
          aret (Some (mkOct blk (option_map (fun q => (q, plen)) dp) plen (slice d p plen)))
  end.

Lemma d2i_octet_split : forall (d : list Z) (len : Z) (st : ap_st bptr),
  d2i_octet d len st = (if len <=? 0 then (err_raise RS_td_small ;;; aret None) st else d2i_exprim d len st).
Proof. intros d len st. unfold d2i_octet, d2i_exprim. destruct (len <=? 0); reflexivity. Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exprim_oct_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (OPP PV TLC : Z)
    (r : option (octet bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block) (ov : word) (jt : list (bv 8)),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match fst r with Some _ => 1 | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (PV, PV + 8); (TLC, TLC + 32)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ rw_cells ctasegs m' OPP [C8 ov] /\ rw_cells ctasegs m' TLC [CB 32 jt]
    /\ match fst r with
       | None => NEW = [] /\ rw_cells ctasegs m' PV [C8 (wz 0)]
       | Some os => NEW = oct_blocks adr' os /\ octet_repA m' (OW' ++ NEW ++ LB) adr' os /\ rw_cells ctasegs m' PV [C8 (wz (adr' (os_blk os)))]
       end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition d2i_cells_okA (m : mem) (LB : list block) (D : Z) (d : list Z) (OPP PV TLC : Z) (j31 : list (bv 8)) : Prop :=
  payload_okA m LB D d
  /\ cellA_in LB OPP 8 /\ cellA_in LB PV 8 /\ cellA_in LB TLC 32 /\ OPP mod 8 = 0 /\ PV mod 8 = 0 /\ TLC mod 8 = 0
  /\ (OPP + 8 <= PV \/ PV + 8 <= OPP) /\ (OPP + 8 <= TLC \/ TLC + 32 <= OPP) /\ (PV + 8 <= TLC \/ TLC + 32 <= PV)
  /\ (d = [] \/ OPP + 8 <= D \/ D + zlength d <= OPP) /\ (d = [] \/ PV + 8 <= D \/ D + zlength d <= PV) /\ (d = [] \/ TLC + 32 <= D \/ D + zlength d <= TLC)
  /\ rw_cells ctasegs m OPP [C8 (wz D)] /\ rw_cells ctasegs m PV [C8 (wz 0)] /\ rw_cells ctasegs m TLC (tlc_in j31).
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exprim_oct_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z) (adr : bptr -> Z) (D : Z) (d : list Z) (OPP PV TLC : Z) (j31 : list (bv 8)),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength d)) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx ADEP_ENTRY (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    d2i_cells_okA m LB D d OPP PV TLC j31 -> 0 < zlength d ->
    a0 = wz PV -> a1 = wz OPP -> a2 = wz (zlength d) -> a3 = wz ITEM_OCTET_A -> a4 = wz (-1) -> a5 = wz 0 -> a6 = wz 0 -> a7 = wz TLC ->
    implAp (d2i_exprim d (zlength d) st) Σ
           (exprim_oct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength d)) adr OPP PV TLC)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ADEP_ENTRY) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition intern_oct_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z) (adr : bptr -> Z) (D : Z) (d : list Z) (OPP PV TLC : Z) (j31 : list (bv 8)),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength d)) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx INTERN_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    d2i_cells_okA m LB D d OPP PV TLC j31 ->
    a0 = wz PV -> a1 = wz OPP -> a2 = wz (zlength d) -> a3 = wz ITEM_OCTET_A -> a4 = wz (-1) -> a5 = wz 0 -> a6 = wz 0 -> a7 = wz TLC ->
    implAp (d2i_octet d (zlength d) st) Σ
           (exprim_oct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength d)) adr OPP PV TLC)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz INTERN_A) fc None m (seg_rom ctasegs)).

End WithRT.
