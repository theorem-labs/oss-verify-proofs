(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v; 2146 of its 2207 lines of code are new or changed and 166 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_G.v, with its module paths and module names changed; 44 of its 80 lines of code are new or changed and 2171 lines of the source are left out. *)
(* Statements of three pieces of segment H of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), for a
   hand to prove on its own. Each is closed: every premise is explicit, the callee contracts and the
   allocator laws are premises of the statement itself, and `B` is the only parameter (the Section's).

   The segment is +0x11c4 .. +0x128c (0x81938 .. 0x81a00), the "any firmware value" block: two put_dec
   calls build SlotModel.t_EF in the frame variable `ef` (SF + 496, 16 bytes), reac_identity_fw_str writes
   its own string in `f` (SF + 464, 8 bytes) and the bcmp at 0x819f8 compares them. SF is the entry's
   class-4 side-stack frame (1024 bytes), mf the machine frame, sp0 the entry's stack pointer.

   - h_fw_call_stmt    the reac_identity_fw_str call at 0x819dc (a0 = v, a1 = f, a2 = 8): from the frame
                       and register facts, the callee's post. The work is fw_dest_ok: tdst_ok and twr_ok of
                       [f, f + fw_n v) (the bytes lie in the caller's own frame, which `own` holds) and
                       range_addressable from the cleared shadow of f.
   - h_bcmp_call_stmt  the bcmp wrapper call at 0x819f8 (a0 = f, a1 = ef, a2 = n <= 8): YCbq.aj_bcmp_at at
                       o = mf - sp0, with src_ok / amem_range / range_addressable / shadow_hull_vis of both
                       ranges from the frame facts (IdentBFrame.shadow_hull_vis_of_frame, YG0v's
                       zero_shadow_range and range_addressable_sub).
   - h_anyfw_range_stmt  the plain model's 16-bit tail value is a 16-bit number. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_identity_fw_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
Variable B : asyms.

(* 0x819dc: reac_identity_fw_str (v, f, 8), f = SF + 464, the entry's frame variable. *)
Definition h_fw_call_stmt : Prop :=
  AR_laws SEGS B ->
  PALib B ->
  reac_identity_fw_str.treac_identity_fw_str_spec B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) pos mf SF v,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  frames Sc = [(4, pos)] -> own = [(4, pos)] -> frame_addr lyc 4 pos = SF ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 v -> getr regs 11 = w64 (SF + 464) -> getr regs 12 = w64 8 ->
  0 <= v < 65536 ->
  mf mod 32 = 0 -> sp0 - 336 <= mf -> mf <= sp0 - 320 -> sp0 - STK <= mf - 2 * ESTACK ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 464) 8 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_identity_fw_str) regs memc mdc)
    (reac_identity_fw_str.treac_identity_fw_str_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k
       regs v (SF + 464) 8).

(* 0x819f8: the bcmp wrapper on the n bytes of f and of ef (n <= 8). *)
Definition h_bcmp_call_stmt : Prop :=
  AR_laws SEGS B ->
  abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp) ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) pos mf SF n raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SF ->
  getr regs 1 = raw -> YK0s.ret_ok raw ->
  getr regs 2 = w64 mf -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (SF + 464) -> getr regs 11 = w64 (SF + 496) -> getr regs 12 = w64 n ->
  1 <= n <= 8 ->
  mf mod 32 = 0 -> sp0 - 336 <= mf -> mf <= sp0 - 320 -> sp0 - STK <= mf - 2 * ESTACK ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 464) 8 ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) 16 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_bcmp)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (res : word),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
       aregs_preserved regs regs2 /\ getr regs2 10 = res /\
       (res = w64 0 <-> forall i, 0 <= i < n ->
          aview SEGS (w_H W) memc (SF + 464 + i) = aview SEGS (w_H W) memc (SF + 496 + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W2) mem2 a)).

(* The plain model's 16-bit tail value (SlotModel.v:79: tb inp 9 + 256 * tb inp 10). *)
Definition h_anyfw_range_stmt : Prop := forall inp, 0 <= SlotModel.t_any_fw inp < 65536.

End c.
End b.
End a.
