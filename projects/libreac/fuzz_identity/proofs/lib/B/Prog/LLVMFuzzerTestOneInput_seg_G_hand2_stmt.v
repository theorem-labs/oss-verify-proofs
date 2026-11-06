(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v; 28 of its 78 lines of code are new or changed and 6015 lines of the source are left out. *)
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
PaRun PaShadow PaJournal IdentBase IdentRo IdentBlkTail YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
buf_of check_str reac_identity_fw_str reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c reac_identity_reac_ver_str_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* seg_G's last piece, for an outside hand: the three shadow stores and the counter store of 0x81928..0x81934
   (+0x11b4 .. +0x11c4): `sb zero,58(s7)` (f's shadow cell), `sb zero,62(s7)`, `sb zero,63(s7)` (ef's two),
   `sd zero,208(s1)` (put_dec's counter slot mf+208), s7 = x23 = shadow_addr (SFa g pos) (sh_reg), s1 = x9 = mf.
   g_pre_stores is the state seg_G reaches at +0x11b4 (after the second free, both heap buffers released);
   the end is the boundary file's inv_G_end. The premises are the contract Section hypotheses the piece uses. *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Local Notation ACUT := (@acut fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Local Notation INV_G := (@inv_G_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Definition g_pre_stores (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x11b4)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       id_at g pos (m_nrec g) W2 mem2 /\ hblocks B g ly2 S2 [] /\ sh_reg g pos regs2 /\
       mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\
       getr regs2 24 = w64 (SlotModel.t_any_fw (e_pl g)) /\
       getr regs2 25 = w64 (SFa g pos + V_ef) /\
       getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) /\
       getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
       getr regs2 27 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
       val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
       val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
       val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
       val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g))).
Definition g_stores_stmt : Prop :=
  AR_laws SEGS B -> PALib B -> STK_LLVMF <= LLVMF_STK ->
  (forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
     ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
     m_fds md' = m_fds md /\ m_fs md' = m_fs md) ->
  forall g pos mf W2 c2, g_pre_stores g pos mf W2 c2 -> SRr SEGS W2 c2 (INV_G g pos mf).
End c.
End b.
End a.
