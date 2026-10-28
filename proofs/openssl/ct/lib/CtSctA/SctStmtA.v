(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApParse ApBridge.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA W_item_d2i_stmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation d2i_list_tree := CtSctP.SctStmt.d2i_list_tree.
Notation oct_blocks := CtSctP.SctStmt.oct_blocks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition O2I_SCT_SIGNATURE_A : Z := 0x335420.
Definition O2I_SCT_A : Z := 0x335704.            (* [comment removed for export] *)
Definition O2I_SCT_LIST_A : Z := 0x336764.       (* [comment removed for export] *)
Definition D2I_SCT_LIST_A : Z := 0x337020.       (* [comment removed for export] *)
Definition SCT_FREE_A : Z := 0x337578.
Definition SCT_LIST_FREE_A : Z := 0x3376b8.      (* [comment removed for export] *)
Definition SCT_NEW_A : Z := 0x3374cc.
Definition SCT_SET1_SIGNATURE_A : Z := 0x3376e4.
(* [comment removed for export] *)
Definition A_CT_OCT_C_A : Z := 0xa78e0.
Definition A_O2I_SCT_SIGNATURE_A : Z := 0xa7920.
Definition A_O2I_SCT_A : Z := 0xa7960.
Definition A_O2I_SCT_LIST_A : Z := 0xa79e0.

(* [comment removed for export] *)
Definition octet_repA (m : mem) (L : list block) (adr : bptr -> Z) (os : octet bptr) : Prop :=
  In (os_blk os, adr (os_blk os), ASN1_STRING_SIZE) L /\ adr (os_blk os) mod 16 = 0      (* [comment removed for export] *)
  /\ rw_cells ctasegs m (adr (os_blk os)) (asn1_string_cells (os_len os) V_ASN1_OCTET_STRING (optr adr (os_data os)) 0)
  /\ os_len os = zlength (os_bytes os) /\ Forall (fun b => 0 <= b < 256) (os_bytes os) /\ os_len os < 2 ^ 31
  /\ match os_data os with
     | None => os_bytes os = []
     | Some (dp, n) => dp <> os_blk os /\ In (dp, adr dp, n) L /\ os_len os <= n /\ bytes_at ctasegs m (adr dp) (to_bytes (os_bytes os))
     end.

(* [comment removed for export] *)
Definition remove_sk (adr : bptr -> Z) (k : skr bptr) (L : list block) : list block :=
  lb_remove (sk_blk k) (lremove (sk_data k) (remove_scts (sk_items k) L)).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition o2i_sig_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z)
    (r : (sctr bptr * Z) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block),
    let x' := fst (fst r) in let res := snd (fst r) in
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8); (adr (sc_blk x), adr (sc_blk x) + SCT_SIZE)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ Forall lbokA NEW
    /\ rw_cells ctasegs m' (adr (sc_blk x)) (sct_cells adr' x' (-1) (if res <=? 0 then vs else 0))
    /\ sc_blk x' = sc_blk x /\ sc_logid x' = sc_logid x /\ sc_ext x' = sc_ext x /\ sc_blob x' = sc_blob x /\ sc_version x' = sc_version x
    /\ (if res <=? 0
        then res = -1 /\ NEW = [] /\ sc_sig x' = None /\ rw_cells ctasegs m' PIN [C8 (wz (D + p))]
        else res = 4 + sc_siglen x' /\ p + res <= len + p /\ rw_cells ctasegs m' PIN [C8 (wz (D + p + res))]
             /\ sc_ts x' = sc_ts x /\ sc_extlen x' = sc_extlen x /\ 0 <= sc_hash x' < 256 /\ 0 <= sc_sigalg x' < 256 /\ sct_nid x' <> NID_undef
             /\ match sc_sig x' with
                | None => NEW = []
                | Some (q, n) => NEW = [(q, adr' q, n)] /\ 0 < n /\ ~ In q (map blk_id (OW' ++ LB))
                                 /\ rw_cells ctasegs m' (adr' q) [CB (Z.to_nat n) (to_bytes (slice c (p + 4) n))]
                end).

Definition o2i_sct_signature_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (x : sctr bptr) (vs : Z) (c : list Z) (D p len PIN : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx O2I_SCT_SIGNATURE_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D c -> 0 < zlength c -> 0 <= p -> 0 <= len -> p + len <= zlength c ->
    In (sc_blk x, adr (sc_blk x), SCT_SIZE) LB -> (D + zlength c <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= D) ->
    (forall pb PA psz, In (pb, PA, psz) LB -> PA <= D -> D + zlength c <= PA + psz -> pb <> sc_blk x) ->
    rw_cells ctasegs m (adr (sc_blk x)) (sct_cells adr x (-1) vs) ->
    sc_version x = 0 -> sc_sig x = None -> (forall b, In b (sct_blocks adr x) -> In b LB) -> List.NoDup (map blk_id (sct_blocks adr x)) ->
    cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (PIN + 8 <= D \/ D + zlength c <= PIN) -> (PIN + 8 <= adr (sc_blk x) \/ adr (sc_blk x) + SCT_SIZE <= PIN) ->
    rw_cells ctasegs m PIN [C8 (wz (D + p))] ->
    a0 = wz (adr (sc_blk x)) -> a1 = wz PIN -> a2 = wz len ->
    implAp (o2i_sct_signature x c p len st) Σ
           (o2i_sig_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr x vs c D p len PIN)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz O2I_SCT_SIGNATURE_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition o2i_sct_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (c : list Z) (D p len PIN : Z)
    (r : option (sctr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match fst r with Some x => adr' (sc_blk x) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ match fst r with
       | None => NEW = [] /\ rw_cells ctasegs m' PIN [C8 (wz (D + p))]
       | Some x => NEW = sct_blocks adr' x /\ sct_repA m' (OW' ++ NEW ++ LB) adr' x /\ rw_cells ctasegs m' PIN [C8 (wz (D + p + len))]
                   /\ sc_version x = CtWire.byte c p
       end.

Definition o2i_sct_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (c : list Z) (D p len PIN : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx O2I_SCT_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D c -> 0 <= p -> 1 <= len <= MAX_SCT_SIZE -> p + len <= zlength c ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (PIN + 8 <= D \/ D + zlength c <= PIN) -> rw_cells ctasegs m PIN [C8 (wz (D + p))] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz len ->
    implAp (o2i_sct c p len st) Σ
           (o2i_sct_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr c D p len PIN)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz O2I_SCT_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition o2i_list_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (PIN : Z)
    (r : option (skr bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block) (pv : word),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match fst r with Some k => adr' (sk_blk k) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ rw_cells ctasegs m' PIN [C8 pv]
    /\ match fst r with
       | None => NEW = []
       | Some k => Permutation NEW (sk_blocks adr' k) /\ sk_repA m' (OW' ++ NEW ++ LB) adr' k
       end.

Definition o2i_sct_list_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (c : list Z) (D len PIN : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST len) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx O2I_SCT_LIST_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    len = zlength c -> 0 < D -> D + zlength c < 2 ^ 63 -> Forall (fun b => 0 <= b < 256) c -> bytes_at ctasegs m D (to_bytes c) ->
    (c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz) ->
    (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (PIN + 8 <= D \/ D + zlength c <= PIN) -> rw_cells ctasegs m PIN [C8 (wz D)] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz len ->
    implAp (o2i_sct_list c len st) Σ
           (o2i_list_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST len) adr PIN)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz O2I_SCT_LIST_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition d2i_octet_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (OPP OCT : Z)
    (r : option (octet bptr) * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block) (ov cv : word),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match fst r with Some os => adr' (os_blk os) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' (snd r) m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(OPP, OPP + 8); (OCT, OCT + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K (snd r) OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ rw_cells ctasegs m' OPP [C8 ov] /\ rw_cells ctasegs m' OCT [C8 cv]
    /\ match fst r with
       | None => NEW = []
       | Some os => NEW = oct_blocks adr' os /\ octet_repA m' (OW' ++ NEW ++ LB) adr' os /\ cv = wz (adr' (os_blk os))
       end.

Definition d2i_octet_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (d : list Z) (D OPP OCT : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength d)) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx D2I_ASN1_OCTET_STRING_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB OPP 8 -> OPP mod 8 = 0 -> (d = [] \/ OPP + 8 <= D \/ D + zlength d <= OPP) -> rw_cells ctasegs m OPP [C8 (wz D)] ->
    cellA_in LB OCT 8 -> OCT mod 8 = 0 -> (d = [] \/ OCT + 8 <= D \/ D + zlength d <= OCT) -> rw_cells ctasegs m OCT [C8 (wz 0)] ->
    (OPP + 8 <= OCT \/ OCT + 8 <= OPP) ->
    a0 = wz OCT -> a1 = wz OPP -> a2 = wz (zlength d) ->
    implAp (d2i_octet d (zlength d) st) Σ
           (d2i_octet_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength d)) adr OPP OCT)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz D2I_ASN1_OCTET_STRING_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition d2i_list_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (K : list block) (CST : Z)
    (adr : bptr -> Z) (D len PIN : Z)
    (ok : option (skr bptr)) (st' : ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' OW' bo' (adr' : bptr -> Z) (NEW : list block),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz match ok with Some k => adr' (sk_blk k) | None => 0 end) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ ap_preA Σ' st' m' OW' (NEW ++ LB) E bo' sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PIN, PIN + 8)] ++ LIBW_A) m m'
    /\ rt_credit RT Σ - CST <= rt_credit RT Σ'
    /\ blocks_kept K st' OW' m m'
    /\ (forall b, In b LB -> adr' (blk_id b) = adr (blk_id b))
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OW' ++ LB)))
    /\ Forall lbokA NEW
    /\ match ok with
       | None => NEW = [] /\ exists pv, rw_cells ctasegs m' PIN [C8 pv]
       | Some k => Permutation NEW (sk_blocks adr' k) /\ sk_repA m' (OW' ++ NEW ++ LB) adr' k /\ rw_cells ctasegs m' PIN [C8 (wz (D + len))]
                   /\ 3 * zlength (sk_items k) + 2 <= len      (* [comment removed for export] *)
       end.
  (* [comment removed for export] *)

Definition d2i_sct_list_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (X : Type) (KK : option (skr bptr) -> AM X) (Q : X * ap_st bptr -> rts RT -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (d : list Z) (D PIN : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength d)) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx D2I_SCT_LIST_A (bv_unsigned ra :: ras) -> ras <> nil ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_okA m LB D d -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    cellA_in LB PIN 8 -> PIN mod 8 = 0 -> (d = [] \/ PIN + 8 <= D \/ D + zlength d <= PIN) -> rw_cells ctasegs m PIN [C8 (wz D)] ->
    a0 = wz 0 -> a1 = wz PIN -> a2 = wz (zlength d) ->
    (forall ok st' Σ' ms', d2i_list_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength d)) adr D (zlength d) PIN ok st' Σ' ms' ->
                          implAp (KK ok st') Σ' Q ms') ->
    implAp (d2i_list_tree d KK st) Σ Q
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz D2I_SCT_LIST_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sct_list_free_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem) (adr : bptr -> Z) (k : skr bptr) (st : ap_st bptr)
    (r : unit * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ r = (tt, st)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (remove_sk adr k OW ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ' = rt_credit RT Σ
    /\ AHEAP Σ' (remove_sk adr k OW) LB m'.

Definition sct_list_free_specA (STK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (lo : Z) (ras : list Z)
         (adr : bptr -> Z) (k : skr bptr),
    AHEAP Σ OW LB m ->
    stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - STK ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
    mem_inv ctasegs m -> tp = wz TP_A -> crypto_statics m ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_LIST_FREE_A (bv_unsigned ra :: ras) -> ras <> nil ->
    sk_repA m OW adr k -> zlength (sk_items k) < 2 ^ 31 ->
    a0 = wz (adr (sk_blk k)) ->
    implAp (sk_free_all k st) Σ
           (sct_list_free_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m adr k st)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz SCT_LIST_FREE_A) fc None m (seg_rom ctasegs)).

End WithRT.
