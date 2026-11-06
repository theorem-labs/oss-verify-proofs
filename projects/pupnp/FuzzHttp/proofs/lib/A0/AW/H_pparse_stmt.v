(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require ScanInt Prelim.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HApxF HttpRepA AWKit HObjA HCount HObjK HObjF HPrepA H_map_str_to_int H_parse_uric H_match_A H_match_X H_httpmsg_destroy H_presp_seg H_presp H_phdr_seg H_phdr H_pent_seg H_pent_kit H_puri.
Import ListNotations.
Open Scope Z_scope.

Definition parser_parse_entryA : Z := 0x8a904.
Notation PPARSE_DEPTH_A := 65536%Z.
Notation METHOD_TAB_A := 0xae960%Z.
Notation FMT_REQ09_A := 0x21a80%Z.
Notation FMT_REQ_A := 0x21aa0%Z.

Section W.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation PS := (aps FI AI).
Local Notation hdr := (HObjA.hdr FI AI).
Local Notation nsec1 := HttpAllocA.nsec1.

Record pstA := mkPSA {
  pa_cur : Z;
  pa_A : Z; pa_len : Z; pa_cap : Z; pa_okm : option K; pa_bs : list byte;
  pa_meth : Z;
  pa_uc : list cell;
  pa_rm : Z; pa_sc : Z;
  pa_SA : Z; pa_slen : Z; pa_scap : Z; pa_sok : option K; pa_sbs : list byte;
  pa_isreq : Z; pa_maj : Z; pa_min : Z;
  pa_ns : list (BLK * Z); pa_hs : list hdr; pa_X : Z;
  pa_ebw : word; pa_elw : word;
  pa_err : Z; pa_hack : Z; pa_pos : Z; pa_entp : Z; pa_clen : Z; pa_csz : Z; pa_esp : Z;
  pa_ub : Z; pa_UB : BL
}.
Definition pa_blocks (t : pstA) : BL :=
  hl_blocks FI AI (pa_ns t) (pa_hs t) ++ okbA FI AI (pa_okm t) (pa_A t) (pa_cap t) ++ okbA FI AI (pa_sok t) (pa_SA t) (pa_scap t) ++ pa_UB t.

Definition p_methwA (m : mem) (P meth : Z) : Prop := rw_cells asegs m P [C4 (wz 1); C4 (wz meth)] /\ 0 <= meth <= 12.

Definition p_parserA (m : mem) (LB : BL) (P : Z) (t : pstA) : Prop :=
  p_scan m P (pa_cur t)
  /\ p_msg FI AI m LB P (pa_A t) (pa_len t) (pa_cap t) (pa_okm t) (pa_bs t) /\ 0 <= pa_cur t <= pa_len t
  /\ p_methwA m P (pa_meth t) /\ p_uri m P (pa_uc t) /\ p_rs m P (pa_rm t) (pa_sc t)
  /\ p_smsgWA FI AI m LB P (pa_SA t) (pa_slen t) (pa_scap t) (pa_sok t) (pa_sbs t)
  /\ p_ver m P (pa_isreq t) (pa_maj t) (pa_min t)
  /\ p_hlist FI AI m P (pa_ns t) (pa_hs t) (pa_X t)
  /\ p_ent m P (pa_ebw t) (pa_elw t)
  /\ p_ctl m P (pa_err t) (pa_hack t) (pa_pos t) (pa_entp t) (pa_clen t) (pa_csz t) (pa_esp t)
  /\ p_url m P (pa_ub t) /\ ubo FI AI (pa_ub t) (pa_UB t).

Definition pp_sideA (t : pstA) : Prop :=
  (pa_pos t = POS_REQUEST_LINE_A \/ pa_pos t = POS_RESPONSE_LINE_A) /\ pa_entp t = 1 /\ pa_ub t = 0 /\ pa_UB t = []
  /\ pa_meth t <= 11
  /\ pa_scap t + 1 <= LMAX_A /\ (pa_sok t <> None -> nth_error (pa_sbs t) (Z.to_nat (pa_slen t)) = Some (Z_to_bv 8 0))
  /\ pa_X t + 2 * (pa_len t - pa_cur t) <= 2^27 + 64
  /\ pa_len t <= 2^26
  /\ pa_scap t = 0 /\ pa_cur t = 0.

Definition pp_statA (m : mem) (gmax : Z) (canary : word) (ws mws : list word) (cslack : list byte) (GL : list (Z * Z)) : Prop :=
  H_phdr.phdr_statics ws m cslack /\ H_pent_kit.gstA GL m
  /\ shw m FMT_CHUNK_A 7 /\ shw m FMT_CRLF_A 3 /\ H_pent_seg.pstatE gmax m
  /\ shw m FMT_RESP_A 16 /\ shw m FMT_SSCANF_A 11
  /\ shw m FMT_REQ09_A 10 /\ shw m FMT_REQ_A 22 /\ shw m A0_FMT_SSCANF_VER 8
  /\ u64arr asegs m METHOD_TAB_A mws /\ shw m METHOD_TAB_A 176 /\ table_strings_A m mws 11
  /\ shw m 0x21ca0 6 /\ shw m 0xaea40 4 /\ shw m MARKTAB_A 10 /\ shw m RESVTAB_A 13
  /\ rw_cells asegs m 0xaad48 [C8 (wz 0xaea40)] /\ (exists gv, rw_cells asegs m 0xaea40 [C4 gv])
  /\ (exists ev, rw_cells asegs m A0_ERRNO [C4 ev]) /\ shw m A0_ERRNO 4
  /\ rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m A0_ssp_guard [C8 canary].
Definition meth_tab_okA (mws : list word) : Prop :=
  length mws = 22%nat /\ (forall i, 0 <= i < 11 -> exists id, nth_error mws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id <= 11).

Inductive pfirst : Z -> BL -> Z -> BL -> Prop :=
| pf_none : forall N LB, pfirst N LB N LB
| pf_new : forall N (LB : BL) (k : K) A n, 1 <= n <= 2^26 + 6 -> pfirst N LB (N + nsec1 n) ((k, A, n) :: LB)
| pf_repl : forall N (LB : BL) (k k' : K) A n, 1 <= n <= 2^26 + 6 -> pfirst N LB (N + nsec1 n) ((k', A, n) :: lb_remove (am_K_eqb FI AI) k LB).

Definition pbud (c M G : Z) (s : PS) (LB : BL) : Prop :=
  am_budget_le FI AI s LB (c + 6)
  /\ forall N1 LB1 (s1 : PS), pfirst (am_nsec FI AI s) LB N1 LB1 -> am_nsec FI AI s1 = N1 ->
       H_phdr.hbud FI AI c G s1 LB1
       /\ forall d N2 LB2 (s2 : PS) G2, H_phdr.hlines FI AI d N1 LB1 N2 LB2 -> 0 <= d <= c -> am_nsec FI AI s2 = N2 ->
            0 <= G2 -> CG_A * (N2 - N1) + G2 <= G + CG_B * d + CG_SL -> H_pent_kit.ebud FI AI M (c - d) G2 s2 LB2.

Definition pparse_WA (P : Z) : list ivl := [(P, P + 500); (ERRNO_A, ERRNO_A + 4)]%Z.

Definition pparse_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : PS) (LB LBK : BL) (P lo gmax : Z) (canary : word) (ws mws : list word) (cslack : list byte) (GL : list (Z * Z))
    (t : pstA) (m : mem) : PS -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI) (r : Z) (t' : pstA),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st' m' /\ fs_live FI st' = fs_live FI st
    /\ apxF FI AI (pparse_WA P) LBK q st m m'
    /\ RHEAP_A FI AI s' LB' m'
    /\ p_parserA m' LB' P t' /\ pa_isreq t' = pa_isreq t
    /\ bsub FI AI (pa_blocks t' ++ LBK) LB' /\ NoDup (map blk_id (pa_blocks t' ++ LBK))

    /\ (exists N1 LB1 N2 LB2 d k d2, pfirst (am_nsec FI AI s) LB N1 LB1 /\ H_phdr.hlines FI AI d N1 LB1 N2 LB2
          /\ H_pent_kit.esteps FI AI k d2 N2 LB2 (am_nsec FI AI s') LB'
          /\ 0 <= k <= 2 * gmax + 5 /\ 0 <= d /\ 0 <= d2 /\ d + d2 <= pa_len t - pa_cur t
          /\ 5 * (am_nsec FI AI s' - (k + 1)) <= 5 * am_nsec FI AI s - phiH FI AI (pa_hs t) + phiH FI AI (pa_hs t'))
    /\ H_phdr.hsumA FI AI (pa_hs t') <= H_phdr.hsumA FI AI (pa_hs t) + (pa_len t - pa_cur t)

    /\ (length LB' + length (pa_blocks t) <= length LB + length (pa_blocks t'))%nat
    /\ pp_statA m' gmax canary ws mws cslack GL
    /\ shw m' P 504 /\ shz m' (sh lo) (sh q) /\ shr m' (sh lo - sh lo mod 8) (sh q + 8)
    /\ 0 <= r <= 5.

Definition pparse_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB LBK : BL) (st : fsstate FI)
         (P lo gmax : Z) (canary : word) (ws mws : list word) (cslack : list byte) (GL : list (Z * Z)) (t : pstA) (ras : list Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st (wz A0_TP) 5 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - PPARSE_DEPTH_A -> q mod 16 = 0 -> q + 64 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  lb (fs_live FI st) P 504 -> P + 504 <= alloc_ceiling -> P mod 8 = 0 -> shw m P 504 ->
  p_parserA m LB P t -> pp_sideA t ->
  bsub FI AI (pa_blocks t ++ LBK) LB -> NoDup (map blk_id (pa_blocks t ++ LBK)) ->
  pbud (pa_len t - pa_cur t) (2 * gmax + 5) (HCount.cgG FI AI (pa_hs t)) s LB ->
  length ws = 66%nat -> (forall i, 0 <= i < 33 -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ 0 <= id < 64) ->
  meth_tab_okA mws -> 0 < gmax < 2^31 ->
  Forall (fun xn : Z * Z => 0x10000 <= fst xn /\ fst xn + snd xn <= 0x609000) GL ->
  H_pent_kit.germ_stmt_A FI AI (H_pent_kit.gstA GL) ->
  pp_statA m gmax canary ws mws cslack GL -> am_static FI AI ZERO_ADDR_A (ZERO_ADDR_A + 32) ->
  shz m (sh lo) (sh q) -> shr m (sh lo - sh lo mod 8) (sh q + 8) ->
  fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras ->

  In (PC0_MALLOC :: 0x8847c :: 0x8aad4 :: bv_unsigned ra :: ras) A0_TRACES ->
  In (PC0_MALLOC :: 0x8847c :: 0x8a000 :: 0x8ab28 :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz P ->
  AJ FI AI J (pparse_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB LBK P lo gmax canary ws mws cslack GL t m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz parser_parse_entryA) fc None m (seg_rom asegs))
    s LB.
End W.
