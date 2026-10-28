(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac ApErrKit ApIface W_get_object W_item_d2i_stmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_set1_signature W_sk_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition O2I_SCT_SIGNATURE : Z := 0x19c4c0.
Definition O2I_SCT : Z := 0x19c674.
Definition O2I_SCT_LIST : Z := 0x19ce00.
Definition D2I_SCT_LIST : Z := 0x19d330.
(* [comment removed for export] *)
Definition A_CT_OCT_C : Z := 0x382a4.
Definition A_O2I_SCT_SIGNATURE : Z := 0x3572a.
Definition A_O2I_SCT_LIST : Z := 0x19ca5.
Definition A_O2I_SCT : Z := 0x120f3.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition O2I_SCT_SIGNATURE_STACK : Z := 64 + ERR_SET_ERROR_STACK.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition o2i_sig_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z)
    (r : (sctr bptr * Z) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo' (adr' : bptr -> Z) (NEW : list block),
    let x' := fst (fst r) in let res := snd (fst r) in
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' (NEW ++ LB) E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(PIN, PIN + 8); (adr (sc_blk x), adr (sc_blk x) + SCT_SIZE)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ rw_cells ctusegs m' (adr (sc_blk x)) (sct_cells adr' x' (-1) (if res <=? 0 then vs else 0))
    /\ sc_blk x' = sc_blk x /\ sc_logid x' = sc_logid x /\ sc_ext x' = sc_ext x /\ sc_blob x' = sc_blob x /\ sc_version x' = sc_version x
    /\ (if res <=? 0
        then res = -1 /\ NEW = [] /\ sc_sig x' = None /\ rw_cells ctusegs m' PIN [C8 (wz (D + p))]
        else res = 4 + sc_siglen x' /\ p + res <= len + p /\ rw_cells ctusegs m' PIN [C8 (wz (D + p + res))]
             /\ sc_ts x' = sc_ts x /\ sc_extlen x' = sc_extlen x /\ 0 <= sc_hash x' < 256 /\ 0 <= sc_sigalg x' < 256 /\ sct_nid x' <> NID_undef
             /\ match sc_sig x' with
                | None => NEW = []
                | Some (q, n) => NEW = [(q, adr' q, n)] /\ 0 < n /\ ~ In q (map blk_id (OW' ++ LB))
                                 /\ rw_cells ctusegs m' (adr' q) [CB (Z.to_nat n) (to_bytes (slice c (p + 4) n))]
                end).

(* [comment removed for export] *)
Definition o2i_sct_signature_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary O2I_SCT_SIGNATURE_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D c -> 0 < zlength c -> 0 <= p -> 0 <= len -> p + len <= zlength c ->
    In (sc_blk x, adr (sc_blk x), SCT_SIZE) LB -> (D + zlength c <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= D) ->
    (forall pb PA psz, In (pb, PA, psz) LB -> PA <= D -> D + zlength c <= PA + psz -> pb <> sc_blk x) ->
    rw_cells ctusegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) ->
    sc_version x = 0 -> sc_sig x = None -> (forall b, In b (sct_blocks adr x) -> In b LB) -> List.NoDup (map blk_id (sct_blocks adr x)) ->
    bv_unsigned sp <= PIN -> PIN + 8 <= B -> PIN mod 8 = 0 -> rw_cells ctusegs m PIN [C8 (wz (D + p))] ->
    a0 = wz (adr (sc_blk x)) -> a1 = wz PIN -> a2 = wz len ->
    implM ctusegs (interp (ap_embed (o2i_sct_signature x c p len st))) s
          (o2i_sig_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr x vs c D p len PIN)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz O2I_SCT_SIGNATURE) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition O2I_SCT_STACK : Z := 80 + O2I_SCT_SIGNATURE_STACK.

(* [comment removed for export] *)
Definition o2i_sct_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (adr : bptr -> Z) (c : list Z) (D p len PIN : Z)
    (r : option (sctr bptr) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo' (adr' : bptr -> Z) (NEW : list block),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz match fst r with Some x => adr' (sc_blk x) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' (NEW ++ LB) E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ match fst r with
       | None => NEW = [] /\ rw_cells ctusegs m' PIN [C8 (wz (D + p))]
       | Some x => NEW = sct_blocks adr' x /\ sct_rep m' (OW' ++ NEW ++ LB) adr' x /\ rw_cells ctusegs m' PIN [C8 (wz (D + p + len))]
                   /\ sc_version x = CtWire.byte c p
       end.

(* [comment removed for export] *)
Definition o2i_sct_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (c : list Z) (D p len PIN : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary O2I_SCT_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D c -> 0 <= p -> 1 <= len <= MAX_SCT_SIZE -> p + len <= zlength c ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    bv_unsigned sp <= PIN -> PIN + 8 <= B -> PIN mod 8 = 0 -> rw_cells ctusegs m PIN [C8 (wz (D + p))] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz len ->
    implM ctusegs (interp (ap_embed (o2i_sct c p len st))) s
          (o2i_sct_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr c D p len PIN)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz O2I_SCT) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition O2I_SCT_LIST_STACK : Z := 96 + O2I_SCT_STACK.

(* [comment removed for export] *)
Definition sk_blocks (adr : bptr -> Z) (k : skr bptr) : list block :=
  scts_blocks adr (sk_items k) ++ dblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)].

(* [comment removed for export] *)
Definition o2i_list_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (adr : bptr -> Z) (PIN : Z)
    (r : option (skr bptr) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo' (adr' : bptr -> Z) (NEW : list block) (pv : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz match fst r with Some k => adr' (sk_blk k) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' (NEW ++ LB) E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ rw_cells ctusegs m' PIN [C8 pv]
    /\ match fst r with
       | None => NEW = []
       | Some k => Permutation NEW (sk_blocks adr' k) /\ sk_rep m' (OW' ++ NEW ++ LB) adr' k
       end.

(* [comment removed for export] *)
Definition o2i_sct_list_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (c : list Z) (D len PIN : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary O2I_SCT_LIST_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    len = zlength c -> 0 <= D -> D + zlength c < 2 ^ 63 -> Forall (fun b => 0 <= b < 256) c -> bytes_at ctusegs m D (to_bytes c) ->
    (c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz) ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    bv_unsigned sp <= PIN -> PIN + 8 <= B -> PIN mod 8 = 0 -> rw_cells ctusegs m PIN [C8 (wz D)] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz len ->
    implM ctusegs (interp (ap_embed (o2i_sct_list c len st))) s
          (o2i_list_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr PIN)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz O2I_SCT_LIST) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition D2I_OCTET_STACK : Z := 1536 + GETOBJ_STACK.      (* [comment removed for export] *)

Definition oct_blocks (adr : bptr -> Z) (os : octet bptr) : list block :=
  (os_blk os, adr (os_blk os), ASN1_STRING_SIZE) :: match os_data os with Some (dp, n) => [(dp, adr dp, n)] | None => [] end.

Definition octet_rep (m : mem) (L : list block) (adr : bptr -> Z) (os : octet bptr) : Prop :=
  In (os_blk os, adr (os_blk os), ASN1_STRING_SIZE) L
  /\ rw_cells ctusegs m (adr (os_blk os)) (asn1_string_cells (os_len os) V_ASN1_OCTET_STRING (optr adr (os_data os)) 0)
  /\ os_len os = zlength (os_bytes os) /\ Forall (fun b => 0 <= b < 256) (os_bytes os) /\ os_len os < 2 ^ 31
  /\ match os_data os with
     | None => os_bytes os = []
     | Some (dp, n) => dp <> os_blk os /\ In (dp, adr dp, n) L /\ os_len os <= n /\ bytes_at ctusegs m (adr dp) (to_bytes (os_bytes os))
     end.

Definition d2i_octet_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (adr : bptr -> Z) (OPP OCT : Z)
    (r : option (octet bptr) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo' (adr' : bptr -> Z) (NEW : list block) (ov cv : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz match fst r with Some os => adr' (os_blk os) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' (snd r) m' OW' (NEW ++ LB) E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (OCT, OCT + 8)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ rw_cells ctusegs m' OPP [C8 ov] /\ rw_cells ctusegs m' OCT [C8 cv]
    /\ match fst r with
       | None => NEW = []
       | Some os => NEW = oct_blocks adr' os /\ octet_rep m' (OW' ++ NEW ++ LB) adr' os /\ cv = wz (adr' (os_blk os))
       end.

Definition d2i_octet_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (d : list Z) (D OPP OCT : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary D2I_OCTET_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    bv_unsigned sp <= OPP -> OPP + 8 <= B -> rw_cells ctusegs m OPP [C8 (wz D)] -> OPP mod 8 = 0 ->
    bv_unsigned sp <= OCT -> OCT + 8 <= B -> rw_cells ctusegs m OCT [C8 (wz 0)] -> OCT mod 8 = 0 -> (OPP + 8 <= OCT \/ OCT + 8 <= OPP) ->
    a0 = wz OCT -> a1 = wz OPP -> a2 = wz (zlength d) ->
    implM ctusegs (interp (ap_embed (d2i_octet d (zlength d) st))) s
          (d2i_octet_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr OPP OCT)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz D2I_ASN1_OCTET_STRING) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition D2I_SCT_LIST_STACK : Z := 64 + Z.max D2I_OCTET_STACK O2I_SCT_LIST_STACK.

Definition d2i_list_tree {A} (d : list Z) (KK : option (skr bptr) -> AM A) : AM A :=
  abind (d2i_octet d (zlength d)) (fun r =>
    match r with
    | None => KK None
    | Some os => abind (o2i_sct_list (os_bytes os) (os_len os)) (fun k => abind (octet_free os) (fun _ => KK k))
    end).

Definition d2i_list_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s : PState) (OW LB : list block) (E : ap_env) (lo B : Z) (canary : word) (m : mem) (K : list block)
    (adr : bptr -> Z) (D len PIN : Z)
    (ok : option (skr bptr)) (st' : ap_st bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word) bo' (adr' : bptr -> Z) (NEW : list block),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz match ok with Some k => adr' (sk_blk k) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
    /\ ap_pre s' st' m' OW' (NEW ++ LB) E bo' sp lo B errv' canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_AP) m m'
    /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
    /\ blocks_kept K st' OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ match ok with
       | None => NEW = [] /\ exists pv, rw_cells ctusegs m' PIN [C8 pv]
       | Some k => Permutation NEW (sk_blocks adr' k) /\ sk_rep m' (OW' ++ NEW ++ LB) adr' k /\ rw_cells ctusegs m' PIN [C8 (wz (D + len))]
       end.

Definition d2i_sct_list_spec : Prop :=
  forall (X : Type) (KK : option (skr bptr) -> AM X) (Q : X * ap_st bptr -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (d : list Z) (D PIN : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary D2I_SCT_LIST_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    bv_unsigned sp <= PIN -> PIN + 8 <= B -> PIN mod 8 = 0 -> rw_cells ctusegs m PIN [C8 (wz D)] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz (zlength d) ->
    (forall ok st' s' ms', d2i_list_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E lo B canary m K adr D (zlength d) PIN ok st' s' ms' ->
                          implM ctusegs (interp (ap_embed (KK ok st'))) s' Q ms') ->
    implM ctusegs (interp (ap_embed (d2i_list_tree d KK st))) s Q
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz D2I_SCT_LIST) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
End WithCeiling0.
