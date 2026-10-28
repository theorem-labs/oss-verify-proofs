(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA W_check_tlenA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition D2I_ASN1_OCTET_STRING_A : Z := 0x246e0c.
Definition D2I_ASN1_INTEGER_A : Z := 0x246ec8.
Definition D2I_ASN1_ENUMERATED_A : Z := 0x246f5c.
(* [comment removed for export] *)
Definition d2i_entryA (e utype : Z) : Prop :=
  e = D2I_ASN1_OCTET_STRING_A /\ utype = V_ASN1_OCTET_STRING.

(* [comment removed for export] *)
Definition D2I_PRIM_STACK_A : Z := 1024 + CHECK_TLEN_STACK_A.
(* [comment removed for export] *)
Definition D2I_PRIM_COST_A (plen : Z) : Z := 3 + GETOBJ_ERR_COST_A + mcost plen.
(* [comment removed for export] *)
Definition D2I_PRIM_SPENT_A (plen : Z) : Z := 8 + mcost plen.
(* [comment removed for export] *)
Definition D2I_PRIM_FRAMES_A : Z := 2 + CHECK_TLEN_FRAMES_A.

(* [comment removed for export] *)
Definition str_ids (x : astr bptr) : list bptr :=
  str_blk x :: match str_data x with Some (dp, _) => [dp] | None => [] end.
Definition str_blocks (OW : list block) (x : astr bptr) : list block :=
  (str_blk x, badr OW (str_blk x), ASN1_STRING_SIZE)
  :: match str_data x with Some (dp, n) => [(dp, badr OW dp, n)] | None => [] end.

(* [comment removed for export] *)
Definition str_repA (m : mem) (OW : list block) (x : astr bptr) (A ty : Z) : Prop :=
  A = badr OW (str_blk x) /\ 0 < A /\ In (str_blk x, A, ASN1_STRING_SIZE) OW /\
  match str_data x with
  | None => rw_cells ctasegs m A (asn1_string_cells 0 ty 0 0)
  | Some (dp, n) =>
      0 < n < 2^31 - 1 /\ str_blk x <> dp /\ In (dp, badr OW dp, n) OW /\ 0 < badr OW dp
      /\ rw_cells ctasegs m A (asn1_string_cells n ty (badr OW dp) 0)
      /\ exists bytes, rw_cells ctasegs m (badr OW dp) [CB (Z.to_nat n) bytes]
  end.

Definition str_ty_ok (utype ty : Z) : Prop := ty = utype \/ ty = utype + 256.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition d2i_prim_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (m : mem) (K : list block)
    (OPP utype plen : Z) (r : option (astr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (ov : word),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ((OPP, OPP + 8) :: LIBW_A) m m'
    /\ rt_credit RT Σ - D2I_PRIM_SPENT_A plen <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ rw_cells ctasegs m' OPP [C8 ov]
    /\ match fst r with
       | None => a0 = wz 0
       | Some x => exists A ty, a0 = wz A /\ str_repA m' OW' x A ty /\ str_ty_ok utype ty
                   /\ (forall q, In q (str_ids x) -> ~ In q (map blk_id K ++ es_ids (snd r) ++ env_ids E))
       end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition d2i_prim_specA (e utype : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (D : Z) (d : list Z) (op totlen OPP : Z),
    let g := get_object d op totlen in
    ap_preA Σ st m OW LB E bo sp lo D2I_PRIM_STACK_A (D2I_PRIM_COST_A (go_len g)) D2I_PRIM_FRAMES_A -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx e (bv_unsigned ra :: ras) -> ras <> nil ->   (* [comment removed for export] *)
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> 0 <= op -> 0 < totlen -> op + totlen <= zlength d ->
    go_err g = None -> go_tag g = utype -> go_cls g = 0 -> Z.land (go_ret g) 32 = 0 ->
    cellA_in LB OPP 8 -> OPP mod 8 = 0 -> (OPP + 8 <= D \/ D + zlength d <= OPP) ->
    rw_cells ctasegs m OPP [C8 (wz (D + op))] ->
    a0 = wz 0 -> a1 = wz OPP -> a2 = wz totlen ->
    implAp (d2i_prim d op totlen utype st) Σ
           (d2i_prim_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K OPP utype (go_len g))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz e) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
Lemma str_repA_blocks_in : forall m OW x A ty b, str_repA m OW x A ty -> In b (str_blocks OW x) -> In b OW.
Proof.
  intros m OW x A ty b (EA & A0 & HB & HD) Hb. unfold str_blocks in Hb.
  destruct (str_data x) as [[dp n]|].
  - destruct HD as (_ & _ & HDI & _). destruct Hb as [<-|[<-|[]]]; [rewrite <- EA; exact HB| exact HDI].
  - destruct Hb as [<-|[]]. rewrite <- EA. exact HB.
Qed.

Lemma str_blocks_ids : forall OW x, map blk_id (str_blocks OW x) = str_ids x.
Proof. intros OW x. unfold str_blocks, str_ids. destruct (str_data x) as [[dp n]|]; reflexivity. Qed.

End WithRT.
