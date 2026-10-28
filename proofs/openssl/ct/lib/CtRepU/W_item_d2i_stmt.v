(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface W_get_object.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition D2I_ASN1_OCTET_STRING : Z := 0x115088.
Definition D2I_ASN1_INTEGER : Z := 0x115144.
Definition D2I_ASN1_ENUMERATED : Z := 0x1151d8.
Definition d2i_entry (e utype : Z) : Prop :=
  (e = D2I_ASN1_OCTET_STRING /\ utype = V_ASN1_OCTET_STRING)
  \/ (e = D2I_ASN1_INTEGER /\ utype = V_ASN1_INTEGER)
  \/ (e = D2I_ASN1_ENUMERATED /\ utype = V_ASN1_ENUMERATED).

(* [comment removed for export] *)
Definition D2I_PRIM_STACK : Z := 512 + GETOBJ_STACK.

(* [comment removed for export] *)
Definition str_ids (x : astr bptr) : list bptr :=
  str_blk x :: match str_data x with Some (dp, _) => [dp] | None => [] end.
Definition str_blocks (OW : list block) (x : astr bptr) : list block :=
  (str_blk x, badr OW (str_blk x), ASN1_STRING_SIZE)
  :: match str_data x with Some (dp, n) => [(dp, badr OW dp, n)] | None => [] end.

(* [comment removed for export] *)
Definition str_rep (m : mem) (OW : list block) (x : astr bptr) (A ty : Z) : Prop :=
  A = badr OW (str_blk x) /\ 0 < A /\ In (str_blk x, A, ASN1_STRING_SIZE) OW /\
  match str_data x with
  | None => rw_cells ctusegs m A (asn1_string_cells 0 ty 0 0)
  | Some (dp, n) =>
      0 < n < 2^31 - 1 /\ str_blk x <> dp /\ In (dp, badr OW dp, n) OW /\ 0 < badr OW dp
      /\ rw_cells ctusegs m A (asn1_string_cells n ty (badr OW dp) 0)
      /\ exists bytes, rw_cells ctusegs m (badr OW dp) [CB (Z.to_nat n) bytes]
  end.

Definition str_ty_ok (utype ty : Z) : Prop := ty = utype \/ ty = utype + 256.

(* [comment removed for export] *)
Definition d2i_prim_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (OPP utype : Z) (r : option (astr bptr) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) (ov : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' LB E bo sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ((OPP, OPP + 8) :: LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ rw_cells ctusegs m' OPP [C8 ov]
    /\ match fst r with
       | None => a0 = wz 0
       | Some x => exists A ty, a0 = wz A /\ str_rep m' OW' x A ty /\ str_ty_ok utype ty
                   /\ (forall q, In q (str_ids x) -> ~ In q (map blk_id K ++ es_ids (snd r) ++ env_ids E))
       end.

(* [comment removed for export] *)
Definition d2i_prim_spec (e utype : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (D : Z) (d : list Z) (op totlen OPP : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary D2I_PRIM_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> 0 <= op -> 0 < totlen -> op + totlen <= zlength d ->
    go_err (get_object d op totlen) = None -> go_tag (get_object d op totlen) = utype -> go_cls (get_object d op totlen) = 0 ->
    Z.land (go_ret (get_object d op totlen)) 32 = 0 ->
    bv_unsigned sp <= OPP -> OPP + 8 <= B -> rw_cells ctusegs m OPP [C8 (wz (D + op))] ->
    a0 = wz 0 -> a1 = wz OPP -> a2 = wz totlen ->
    implM ctusegs (interp (ap_embed (d2i_prim d op totlen utype st))) s
          (d2i_prim_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K OPP utype)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz e) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Lemma str_rep_blocks_in : forall m OW x A ty b, str_rep m OW x A ty -> In b (str_blocks OW x) -> In b OW.
Proof.
  intros m OW x A ty b (EA & A0 & HB & HD) Hb. unfold str_blocks in Hb.
  destruct (str_data x) as [[dp n]|].
  - destruct HD as (_ & _ & HDI & _). destruct Hb as [<-|[<-|[]]]; [rewrite <- EA; exact HB| exact HDI].
  - destruct Hb as [<-|[]]. rewrite <- EA. exact HB.
Qed.

Lemma str_blocks_ids : forall OW x, map blk_id (str_blocks OW x) = str_ids x.
Proof. intros OW x. unfold str_blocks, str_ids. destruct (str_data x) as [[dp n]|]; reflexivity. Qed.

End WithCeiling0.
