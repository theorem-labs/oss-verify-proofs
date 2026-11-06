(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HApxF HttpRepA AWKit HObjA HCount HObjK HObjF HPrepA H_phdr_seg H_phdr H_pent_seg H_pent_kit H_pparse_stmt.
Import ListNotations.
Open Scope Z_scope.

Definition parser_append_entryA : Z := 0x8b9ac.

Section W.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation pstA := (pstA FI AI).
Local Notation nsec1 := HttpAllocA.nsec1.

Definition pa_set_msg (t : pstA) (A' len' cap' : Z) (ok' : option K) (bs' : list byte) : pstA :=
  mkPSA FI AI (pa_cur FI AI t) A' len' cap' ok' bs' (pa_meth FI AI t) (pa_uc FI AI t) (pa_rm FI AI t) (pa_sc FI AI t)
        (pa_SA FI AI t) (pa_slen FI AI t) (pa_scap FI AI t) (pa_sok FI AI t) (pa_sbs FI AI t) (pa_isreq FI AI t) (pa_maj FI AI t) (pa_min FI AI t)
        (pa_ns FI AI t) (pa_hs FI AI t) (pa_X FI AI t) (pa_ebw FI AI t) (pa_elw FI AI t)
        (pa_err FI AI t) (pa_hack FI AI t) (pa_pos FI AI t) (pa_entp FI AI t) (pa_clen FI AI t) (pa_csz FI AI t) (pa_esp FI AI t)
        (pa_ub FI AI t) (pa_UB FI AI t).

Definition pappended (s : PS) (LB : BL) (t : pstA) (n : Z) (src : list byte) (s1 : PS) (LB1 : BL) (t1 : pstA) : Prop :=
  exists (A' cap' : Z) (ok' : option K) (bs' : list byte),
    t1 = pa_set_msg t A' (pa_len FI AI t + n) cap' ok' bs'
    /\ ((ok' = pa_okm FI AI t /\ LB1 = LB /\ A' = pa_A FI AI t /\ cap' = pa_cap FI AI t /\ am_nsec FI AI s1 = am_nsec FI AI s)
        \/ (exists k', ok' = Some k' /\ LB1 = (k', A', cap' + 1) :: lb_keepA FI AI (pa_okm FI AI t) LB
                       /\ am_nsec FI AI s1 = am_nsec FI AI s + nsec1 (cap' + 1)
                       /\ pa_cap FI AI t < pa_len FI AI t + n /\ pa_cap FI AI t + 5 <= cap' <= pa_cap FI AI t + Z.max 5 n))
    /\ pa_len FI AI t + n <= cap' <= pa_cap FI AI t + n + 5
    /\ firstn (Z.to_nat (pa_len FI AI t)) bs' = firstn (Z.to_nat (pa_len FI AI t)) (pa_bs FI AI t)
    /\ (n >= 1 -> firstn (Z.to_nat (pa_len FI AI t + n + 1)) bs' = firstn (Z.to_nat (pa_len FI AI t)) (pa_bs FI AI t) ++ src ++ [Z_to_bv 8 0]).

Definition pappend_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LB LBK : BL) (P lo gmax : Z) (canary : word) (ws mws : list word) (cslack : list byte) (GL : list (Z * Z))
    (t : pstA) (n : Z) (src : list byte) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists (sa : PS) (LBa : BL) (ta : pstA) (ma : mem),
    pappended s LB t n src sa LBa ta
    /\ apxF FI AI (pparse_WA P) LBK q st m ma
    /\ pparse_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st sa LBa LBK P lo gmax canary ws mws cslack GL ta ma s' LB' ms'.

Definition pappend_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB LBK : BL) (st : fsstate FI)
         (P lo gmax : Z) (canary : word) (ws mws : list word) (cslack : list byte) (GL : list (Z * Z)) (t : pstA) (ras : list Z)
         (SRC n : Z) (src : list byte),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st (wz A0_TP) 5 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - PPARSE_DEPTH_A -> q mod 16 = 0 -> q + 64 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  lb (fs_live FI st) P 504 -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  p_parserA FI AI m LB P t ->

  pp_sideA FI AI (pa_set_msg t (pa_A FI AI t) (pa_len FI AI t + n) (pa_cap FI AI t) (pa_okm FI AI t) (pa_bs FI AI t)) ->
  pa_cap FI AI t + n + 6 <= LMAX_A -> am_budget_le FI AI s LB (pa_cap FI AI t + n + 6) ->
  (forall sa LBa ta, pappended s LB t n src sa LBa ta -> pbud FI AI (pa_len FI AI t + n - pa_cur FI AI t) (2 * gmax + 5) (HCount.cgG FI AI (pa_hs FI AI t)) sa LBa) ->
  bsub FI AI (pa_blocks FI AI t ++ LBK) LB -> NoDup (map blk_id (pa_blocks FI AI t ++ LBK)) ->
  length ws = 66%nat -> (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64) ->
  meth_tab_okA mws -> 0 < gmax < 2^31 ->
  Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL ->
  H_pent_kit.germ_stmt_A FI AI (H_pent_kit.gstA GL) ->
  pp_statA m gmax canary ws mws cslack GL -> am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32) ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras ->
  In (PC0_MALLOC :: 0x887a0 :: 0x8b164 :: bv_unsigned ra :: ras) A0_TRACES ->
  In (PC0_MALLOC :: 0x887a0 :: 0x8a5f4 :: 0x8b1b8 :: bv_unsigned ra :: ras) A0_TRACES ->

  bytes_at asegs m SRC src -> Z.of_nat (length src) = n -> (1 <= n \/ pa_okm FI AI t = None) -> 0 < SRC ->
  msrcA FI AI LBK q st SRC n -> shw m SRC n -> SRC + n < 2^47 -> (SRC + n <= P + 400 \/ P + 432 <= SRC) ->
  a0 = wz P -> a1 = wz SRC -> a2 = wz n ->
  AJ FI AI J (pappend_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB LBK P lo gmax canary ws mws cslack GL t n src m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz parser_append_entryA) fc None m (seg_rom asegs))
    s LB.
End W.
