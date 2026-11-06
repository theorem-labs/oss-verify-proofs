(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 79 of its 118 lines of code are new or changed and 541 lines of the source are left out. *)
(* Three pieces of seg_D3 (the REAC-version case of LLVMFuzzerTestOneInput's build-B walk, +0x888 .. +0xe24,
   LLVMFuzzerTestOneInput_inv.v seg_D3_stmt) stated for other hands: the three program/runtime calls of the case
   from the caller's journal (:67, :86, :108). Each is a closed Prop over the
   contract's Section variables; every hypothesis it needs is an explicit premise with the contract's text
   (LLVMFuzzerTestOneInput.v). Prove `Lemma d3_X : d3_X_stmt B MT ...` in your own file inside the same Sections.

   Measured on the neutral listing of fuzz_identity.asan-ubsan: the calls are made with sp = mf (s1), ra = BASE + the
   slot after the jal: put_dec at 0x81144 / 0x81190 / 0x811a4 (a0 = ev = SF+288 from mf+72, a1 = mf+208, a2 =
   major / minor / patch, a3 = 1 / 1 / 2; the counter at mf+208 is 0, d1 + 1, d1 + 1 + d2), reac_identity_reac_ver_str
   at 0x811e8 (a0..a2 = major, minor, patch, a3 = v = SF+224 from mf+48, a4 = 20), and the bcmp wrapper at
   0x8101c (x = id+28 = SF+380, y = pl, n = 8) and 0x81208 (x = v, y = ev, n = n3 + 1 <= 17). Before put_dec the
   case clears the shadow of v (cells 28, 29 = 0, 30 = 4) and ev (cells 36..38 = 0) at 0x81110 .. 0x8112c. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel put_dec_c.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation AJ g pos lyc Sc W mem md k := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem md k).

(* put_dec at 0x81144 / 0x81190 / 0x811a4: b = ev (SF+288), p = mf+208 holding n, v < 2^16, the 24 bytes of ev
   addressable (the case cleared their shadow at 0x81124..0x8112c). *)
Definition d3_pd_stmt : Prop :=
  AR_laws SEGS B -> identb_prog_sig_ok (PI := PI) -> put_dec.tput_dec_spec B ->
  STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB ->
  forall (g : ectx) (pos mf : Z) (W : world SEGS) (regs : bvmap 5 word) mem md lyc Sc k n v mn retk,
  EPRE g -> AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] -> 0 <= k <= EV_LLVMF ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (SFa g pos + V_ev) -> getr regs 11 = w64 (mf + M_n1) ->
  getr regs 12 = w64 v -> getr regs 13 = w64 mn -> 0 <= v < 65536 -> 0 <= mn <= 10 ->
  0 <= n -> n + put_dec_c.dec_len v mn <= N_ev ->
  val_mem SEGS (rd W mem) (mf + M_n1) 8 n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (SFa g pos + V_ev) N_ev ->
  SRr SEGS W (cfg_at SEGS (SIGMA IB_put_dec) regs mem md)
    (put_dec.tput_dec_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
       lyc Sc W mem k regs (SFa g pos + V_ev) (mf + M_n1) n v mn).

(* reac_identity_reac_ver_str at 0x811e8: o = v (SF+224), c = 20, the 20 bytes of v addressable (shadow cleared at
   0x81114..0x81120). *)
Definition d3_vs_stmt : Prop :=
  AR_laws SEGS B -> identb_prog_sig_ok (PI := PI) -> reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B ->
  STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) (pos mf : Z) (W : world SEGS) (regs : bvmap 5 word) mem md lyc Sc k ma mi pa retk,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 ma -> getr regs 11 = w64 mi -> getr regs 12 = w64 pa ->
  getr regs 13 = w64 (SFa g pos + V_v) -> getr regs 14 = w64 20 ->
  0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (SFa g pos + V_v) N_v ->
  SRr SEGS W (cfg_at SEGS (SIGMA IB_reac_identity_reac_ver_str) regs mem md)
    (reac_identity_reac_ver_str.treac_identity_reac_ver_str_post B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
       (e_mem g) (e_md g) [(4, pos)] lyc Sc W mem k regs ma mi pa (SFa g pos + V_v) 20).

(* Where a compared range lies: in the entry's side-stack frame or in a heap block of the state. *)
Definition d3_inobj (g : ectx) (pos : Z) (lyc : alayout) (Sc : astate) (x n : Z) : Prop :=
  (SFa g pos <= x /\ x + n <= SFa g pos + 1024) \/
  (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= x /\ x + n <= b + req_size m).
(* The bcmp wrapper at 0x8101c (id+28 vs pl, 8) and 0x81208 (v vs ev, n3 + 1): the journal is kept at k, nothing
   outside the wrapper's 2 * ESTACK window below mf changes, a0 = 0 exactly when the ranges are equal. *)
Definition d3_bc_stmt : Prop :=
  AR_laws SEGS B -> abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp) -> STK_LLVMF <= LLVMF_STK ->
  forall (g : ectx) (pos mf : Z) (W : world SEGS) (regs : bvmap 5 word) mem md lyc Sc k x y n retk,
  AJ g pos lyc Sc W mem md k -> frames Sc = [(4, pos)] ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 < n <= 64 ->
  d3_inobj g pos lyc Sc x n -> d3_inobj g pos lyc Sc y n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF y n ->
  SRr SEGS W (cfg_at SEGS (SIGMA IB___interceptor_trampoline_bcmp) regs mem md)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
      c2 = cfg_at SEGS (BASE + retk) regs2 mem2 md2 /\ AJ g pos lyc Sc W mem2 md2 k /\
      aregs_preserved regs regs2 /\ getr regs2 10 = v /\
      (v = w64 0 <-> forall j, 0 <= j < n -> aview SEGS (w_H W) mem (x + j) = aview SEGS (w_H W) mem (y + j)) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)).

(* What the case may change, relative to its start, and the zones the end state's facts live in: the machine frame
   up to sp0, the side-stack frame and its shadow, the payload copy and the input block. *)
Definition d3_wr (g : ectx) (pos mf : Z) (a : Z) : Prop :=
  (mf + 24 <= a < mf + 32) \/ (mf + M_n1 <= a < mf + M_n1 + 8) \/
  (SFa g pos + V_v <= a < SFa g pos + V_v + N_v) \/ (SFa g pos + V_ev <= a < SFa g pos + V_ev + N_ev) \/
  (SFa g pos + V_hw + 4 <= a < SFa g pos + V_hw + 12) \/
  (shadow_addr (SFa g pos) + 28 <= a < shadow_addr (SFa g pos) + 31) \/
  (shadow_addr (SFa g pos) + 36 <= a < shadow_addr (SFa g pos) + 39).
Definition d3_zone (g : ectx) (pos mf : Z) (i : nat) (pl : Z) (a : Z) : Prop :=
  (mf <= a < e_sp0 g) \/ (SFa g pos <= a < SFa g pos + 1024) \/
  (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) \/
  (pl <= a < pl + SlotModel.rec_k (e_pl g) i) \/ (e_p g <= a < e_p g + e_n g).
Definition d3_keep (g : ectx) (pos mf : Z) (i : nat) (pl : Z) (W0 : world SEGS) (m0 : word -> option byte)
  (W : world SEGS) (m : word -> option byte) : Prop :=
  forall a, d3_zone g pos mf i pl a -> ~ d3_wr g pos mf a -> aview SEGS (w_H W) m a = aview SEGS (w_H W0) m0 a.
(* d3_tl_stmt was removed (2026-10-29): it was FALSE as written (its premise
   `aregs_preserved regs2 regsE` cannot hold, since the REAC-version case changes s2..s5) and unused;
   seg_D3 packages its end state with d3tl_core (LLVMFuzzerTestOneInput_seg_D3_tl.v) instead. *)

End c.
End b.
End a.
