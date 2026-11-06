(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface CXXRep XRep XPRep XP_verb_stmt.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record hdrv := mkHV { hv_mp : Z ; hv_ml : Z ; hv_tp : Z ; hv_tl : Z ; hv_ver : Z ; hv_vb : Z }.

Definition HdrCells (h : hdrv) : list cell :=
  [C8 (wz (hv_mp h)); C8 (wz (hv_ml h)); C8 (wz (hv_tp h)); C8 (wz (hv_tl h)); C4 (wz (hv_ver h)); C4 (wz (hv_vb h))].

(* [comment removed for export] *)
Definition hdr_empty (h : hdrv) : Prop :=
  hv_mp h = 0 /\ hv_ml h = 0 /\ hv_tp h = 0 /\ hv_tl h = 0 /\ 0 <= hv_ver h < 2^32 /\ 0 <= hv_vb h < 2^32.

Definition O_PR_HDR  : Z := 128.   (* [comment removed for export] *)
Definition O_PR_USED : Z := 241.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ONREQ_STACK : Z := 128 + ROPNEW_STACK.

(* [comment removed for export] *)
Definition onreq_X (P : Z) : list (Z * Z) := [(P + O_PR_HDR, P + O_PR_HDR + 40); (P + O_PR_USED, P + O_PR_USED + 1)]%Z.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition req_res (LB : list block) (mbs tbs : list byte) (verb ver : Z) (h' : hdrv) (LB' : list block) (m' : mem) : Prop :=
  exists (pt : bptr) (At : Z),
    hv_tp h' = At /\ hv_tl h' = Z.of_nat (length tbs) + 1 /\ hv_ver h' = ver /\ 0 <= hv_vb h' < 2^32
    /\ rblock_range At (Z.of_nat (length tbs) + 1)
    /\ rw_cells usegs m' At [CB (S (length tbs)) (b8 32 :: tbs)]
    /\ ( (verb <> 0 /\ hv_mp h' = 0 /\ hv_ml h' = 0 /\ hv_vb h' = verb
          /\ LB' = (pt, At, Z.of_nat (length tbs) + 1) :: LB)
       \/ (verb = 0 /\ exists (pm : bptr) (Am : Z),
             hv_mp h' = Am /\ hv_ml h' = Z.of_nat (length mbs) /\ rblock_range Am (Z.of_nat (length mbs))
             /\ rw_cells usegs m' Am [CB (length mbs) mbs]
             /\ LB' = (pm, Am, Z.of_nat (length mbs)) :: (pt, At, Z.of_nat (length tbs) + 1) :: LB) ).

Lemma req_res_LB_mono : forall LB mbs tbs verb ver h' LB' m', req_res LB mbs tbs verb ver h' LB' m' ->
  forall b, In b LB -> In b LB'.
Proof.
  intros LB mbs tbs verb ver h' LB' m' (pt & At & _ & _ & _ & _ & _ & _ & [(_ & _ & _ & _ & ->)|(_ & pm & Am & _ & _ & _ & _ & ->)]) b Hb;
    cbn; tauto.
Qed.

Section Iface.
  Variable H : hsr.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition onreq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (mo : Model) (LB : list block) (P MP TP verb ver lo B : Z) (mbs tbs : list byte) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LB' : list block) (h' : hdrv),
    cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
    /\ hs_RHEAP H s' LB' m'
    /\ xpres LB (bv_unsigned sp) (onreq_X P) m m'
    /\ rw_cells usegs m' (P + O_PR_USED) [C1 (b8 1)]
    /\ rw_cells usegs m' (P + O_PR_HDR) (HdrCells h')
    /\ req_res LB mbs tbs verb ver h' LB' m'
    /\ bytes_at usegs m' MP mbs /\ bytes_at usegs m' TP tbs.

Definition onreq_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
         (P verb MP TP ver lo B : Z) (mbs tbs : list byte) (h : hdrv) (errv : word),
  rw_cells usegs m (P + O_PR_USED) [C1 (b8 0)] ->
  rw_cells usegs m (P + O_PR_HDR) (HdrCells h) -> hdr_empty h ->
  bytes_at usegs m MP mbs -> bytes_at usegs m TP tbs ->
  1 <= Z.of_nat (length mbs) < 2^26 -> 1 <= Z.of_nat (length tbs) < 2^26 ->
  MP + Z.of_nat (length mbs) <= hceil -> TP + Z.of_nat (length tbs) <= hceil ->
  rclient_range LB (bv_unsigned sp) MP (Z.of_nat (length mbs)) -> rclient_range LB (bv_unsigned sp) TP (Z.of_nat (length tbs)) ->
  0 <= verb < 2^32 -> verb = verb_of (zbytes mbs) -> (ver = 10 \/ ver = 11) ->
  bv_unsigned sp <= P -> P + 256 <= 2^64 ->
  hs_RHEAP H s LB m -> hs_KREL H s mo ->
  lb_bytes LB + (Z.of_nat (length tbs) + 1) + Z.of_nat (length mbs) <= hs_LIVE_MAX H ->
  Z.of_nat (length LB) + 2 <= hs_LIVE_CNT_MAX H ->
  hs_rauxv_ok H m B -> bv_unsigned sp <= B -> P + 256 <= B ->
  stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - ONREQ_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  0 < MP ->                                                                  (* [comment removed for export] *)
  mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
  hs_SR H (onreq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo LB P MP TP verb ver lo B mbs tbs)
    (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz verb) (wz MP) (wz (Z.of_nat (length mbs))) (wz TP) (wz (Z.of_nat (length tbs)))
                     (wz ver) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 P_ON_REQUEST_IMPL) fc None m (seg_rom usegs)) mo).

End Iface.
End HCW.
