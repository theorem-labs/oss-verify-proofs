(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v; 87 of its 136 lines of code are new or changed and 6016 lines of the source are left out. *)
(* The pieces of seg_E (LLVMFuzzerTestOneInput_seg_E.v) that are proved on their own: the post-condition the walk
   produces at BASE + 0x1080 (e_post), and three closed statements over it.
   - e_fin_stmt: e_post, with the facts of inv_exit at the start, gives inv_E_end (bookkeeping, no run).
   - e_tail_stmt: from the compare at BASE + 0x107c (0x817f0 bne x18, a0 to the abort 0x82614) with x18 = a0 = fam,
     the run reaches BASE + 0x1080 and e_post holds.
   - e_loop_stmt: from the loop head BASE + 0x1024 (0x81798) at row j of HW_TABLE, with rows < j not equal, the run
     reaches e_post (bcmp at 0x817a4; row equal: the shadow test of HW_TABLE + 12 j and its family field, 0x817d0
     .. 0x817e8; no row equal: 0x817b8 .. 0x817c0; both through 0x817ec to the compare), given e_tail_stmt. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_box_family_of_c.
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
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
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
#[local] Notation ECOM := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation INV_E_END := (inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

(* ---- the state at the end ------------------------------------------------------------------------------- *)
(* What the walk gives at 0x817f4: the same layout, state and world, the bytes outside the calls' stack windows
   and hw.have kept, hw.have written, the registers the next segments read. *)
Definition e_post (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) : world SEGS -> config -> Prop :=
fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
  c3 = cfg_at SEGS (BASE + 0x1080) regs3 mem3 md3 /\
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem3 md3
    (4 * Z.of_nat (m_nrec g)) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SFa g pos + 432 <= a < SFa g pos + 436) ->
    aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) /\
  val_mem SEGS (rd W2 mem3) (SFa g pos + V_hw) 4 (m_have g (m_nrec g)) /\
  getr regs3 2 = getr regs2 2 /\ getr regs3 3 = getr regs2 3 /\ getr regs3 4 = getr regs2 4 /\
  getr regs3 8 = getr regs2 8 /\ getr regs3 9 = getr regs2 9 /\ getr regs3 25 = getr regs2 25 /\
  getr regs3 24 = getr regs2 24 /\
  getr regs3 23 = w64 (shadow_addr (SFa g pos)) /\ getr regs3 14 = w64 SHADOW_OFF.

(* e_post with the start facts of inv_exit gives inv_E_end. *)
Definition e_fin_stmt : Prop :=
  STK_LLVMF <= LLVMF_STK -> AR_laws SEGS B ->
  (forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
    ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
    m_fds md' = m_fds md /\ m_fs md' = m_fs md) ->
  forall g pos mf ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 (W3 : world SEGS) (c3 : config),
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) <= EV_LLVMF ->
  mo_le MT (e_S g) S2 (4 * Z.of_nat (m_nrec g) * MEV MT) ->
  mo_ok MT S2 ((EV_LLVMF - 4 * Z.of_nat (m_nrec g)) * MEV MT) ->
  ECOM g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  id_at g pos (m_nrec g) W2 mem2 -> hw_live g pos mf (m_nrec g) W2 mem2 -> hblocks B g ly2 S2 [] ->
  mf_id3 g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 ->
  cur_at g (m_nrec g) regs2 -> getr regs2 24 = w64 (e_n g - m_cur g (m_nrec g)) ->
  e_post g pos mf ly2 S2 W2 regs2 mem2 W3 c3 ->
  INV_E_END g pos mf W3 c3.

(* The compare at 0x817f0 with x18 = a0 = fam, and the step to 0x817f4. *)
Definition e_tail_stmt : Prop :=
  AR_laws SEGS B ->
  forall g pos mf ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 (regs : bvmap 5 word) mem md (fam : Z),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem md
    (4 * Z.of_nat (m_nrec g)) ->
  0 <= fam <= 3 -> getr regs 18 = w64 fam -> getr regs 10 = w64 fam ->
  getr regs 2 = getr regs2 2 -> getr regs 3 = getr regs2 3 -> getr regs 4 = getr regs2 4 ->
  getr regs 8 = getr regs2 8 -> getr regs 9 = getr regs2 9 -> getr regs 25 = getr regs2 25 ->
  getr regs 24 = getr regs2 24 ->
  getr regs 23 = w64 (shadow_addr (SFa g pos)) -> getr regs 14 = w64 SHADOW_OFF ->
  val_mem SEGS (rd W2 mem) (SFa g pos + V_hw) 4 (m_have g (m_nrec g)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SFa g pos + 432 <= a < SFa g pos + 436) ->
    aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x107c) regs mem md) (e_post g pos mf ly2 S2 W2 regs2 mem2).

(* The loop head 0x81798 at row j (x19 = -12 j, x20 = HW_TABLE + 4 + 12 j, x21 = HW_TABLE, x22 = &hw + 4,
   x23 = -36, x18 = the library's family = fam_cmp hw), rows < j not equal, to e_post. *)
Definition e_loop_stmt : Prop :=
  STK_LLVMF <= LLVMF_STK -> AR_laws SEGS B ->
  forall (RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi),
  (forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr) ->
  forall G : list (Z * Z), globs_marked SEGS B G -> img_shadow_vis SEGS B -> In (VAL (A_OBJ 6), 36) G ->
  (forall (W : world SEGS) mem,
    arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem) ->
  abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp) ->
  e_tail_stmt ->
  forall g pos mf ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 (j : nat) (regs : bvmap 5 word) mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem md
    (4 * Z.of_nat (m_nrec g)) ->
  frames S2 = [(4, pos)] -> EPRE g ->
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
  (j < 3)%nat -> m_have g (m_nrec g) <> 0 ->
  (forall j', (j' < j)%nat -> map (fun b : byte => bv_unsigned b) (m_hwb g (m_nrec g)) <> SlotModel.HWT j') ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf -> getr regs2 8 = w64 (e_sp0 g) ->
  getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs 2 = getr regs2 2 -> getr regs 3 = getr regs2 3 -> getr regs 4 = getr regs2 4 ->
  getr regs 8 = getr regs2 8 -> getr regs 9 = getr regs2 9 -> getr regs 25 = getr regs2 25 ->
  getr regs 24 = getr regs2 24 ->
  getr regs 18 = w64 (SlotModel.fam_cmp (m_hwb g (m_nrec g))) ->
  getr regs 19 = w64 (- (12 * Z.of_nat j)) ->
  getr regs 20 = w64 (VAL (A_OBJ 6) + 4 + 12 * Z.of_nat j) ->
  getr regs 21 = w64 (VAL (A_OBJ 6)) ->
  getr regs 22 = w64 (SFa g pos + 436) ->
  getr regs 23 = w64 (-36) ->
  val_mem SEGS (rd W2 mem) (mf + 160) 8 (shadow_addr (SFa g pos)) ->
  val_mem SEGS (rd W2 mem) (mf + 168) 8 SHADOW_OFF ->
  bytes_at8 W2 mem (SFa g pos + V_hw + 4) (m_hwb g (m_nrec g)) ->
  sh_blk W2 mem (SFa g pos + V_hw) N_hw ->
  val_mem SEGS (rd W2 mem) (SFa g pos + V_hw) 4 (m_have g (m_nrec g)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 8256 <= a < mf) -> ~ (SFa g pos + 432 <= a < SFa g pos + 436) ->
    aview SEGS (w_H W2) mem a = aview SEGS (w_H W2) mem2 a) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1024) regs mem md) (e_post g pos mf ly2 S2 W2 regs2 mem2).

End c.
End b.
End a.
