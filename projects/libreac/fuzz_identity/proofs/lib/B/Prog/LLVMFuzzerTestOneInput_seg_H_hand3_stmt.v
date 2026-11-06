(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* The third hand statement of segment H of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): the glue
   between the block's walk and the boundary layer. Closed: `B` and the contract's Section parameters are
   the only parameters, every hypothesis is a premise of the statement.

   h_core_stmt is the walk of the block itself, +0x11c4 (0x81938) to +0x128c (0x81a00), on raw facts:
   from the journal, the entry's class-4 frame SF (own = [(4, pos)]), the machine frame mf, v = the 16-bit
   firmware value in x24, ef = SF + 496 in x25, the counter slot mf + 208 at zero, the frame-pointer slot
   mf + 64 = SF, the capacity slot mf + 120 = cd, and the cleared shadow of f (SF + 464, 8) and of ef
   (SF + 496, 16), it reaches +0x128c with ef holding DEC (v / 1000) 1 ++ [dot] ++ DEC (v mod 1000) 3,
   x22 = cd, the callee-saved registers kept, and everything else outside [mf - 2 * ESTACK, mf) and the
   written bytes unchanged (rvs_k, lib/B/Prog/reac_identity_reac_ver_str.v).  a Theorem Labs lane proves it.

   h_glue_stmt is what is left: inv_G_end -> (the premises of h_core_stmt) and h_core_stmt's post ->
   inv_H_end, i.e. seg_H_stmt from h_core_stmt. The work: read inv_G_end's acut (journal, frames = [(4,pos)],
   the meter, ecommon's registers and machine-frame slots, e_pre), produce h_core_stmt's premises (the
   bounds on mf come from ecommon and astk_ok, st_nev S + k <= EV_MAX from e_pre and k <= EV_LLVMF <= EV_LIB,
   the value facts from inv_G_end), and rebuild inv_H_end at +0x128c: the journal with the same k (no
   allocator event), the meter through HMT0 and ameter_laws (mo_le_trans, mo_ok_step), frames and hblocks
   from the post's Permutation, and id_at / sh_reg / mf_id3 / mf_id / mf+112 / mf+120 / mf+160 / mf+176 /
   ecommon's own slots carried through rvs_k (the frame-zone clause for the frame's bytes and shadow, the
   first clause for the machine-frame slots, the block clause for the input bytes), and
   bytes_at8 ef (SlotModel.t_EF) from the post's garr8 (t_EF is that very list, SlotModel.v:94). *)
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
reac_identity_reac_ver_str LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the two decimal pieces of the block, as the plain model has them (SlotModel.v:94) *)
Definition hg_d1 (v : Z) : Z := Z.of_nat (length (IdentSpec.DEC (v / 1000) 1)).
Definition hg_n2 (v : Z) : Z := hg_d1 v + 4.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
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

(* what the block writes: ef with its NUL, f = ef - 32 with its NUL, and the counter slot *)
Definition hg_wrote (ef mf v : Z) (a : Z) : Prop :=
  ef <= a < ef + hg_n2 v + 1 \/ ef - 32 <= a < ef - 32 + hg_n2 v + 1 \/ mf + 208 <= a < mf + 216.
Definition hg_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (mf ef v cd : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = cfg_at SEGS (BASE + 0x128c) regs2 mem2 md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
  frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr regs2 r = getr regs r) /\
  getr regs2 22 = w64 cd /\
  garr8 SEGS (mrestrict (w_H W2) mem2) ef
    (map (fun b : byte => bv_unsigned b)
       (IdentSpec.DEC (v / 1000) 1 ++ [SlotModel.dot] ++ IdentSpec.DEC (v mod 1000) 3)) /\
  rvs_k B lyc Sc W memc W2 mem2 (mf - 2 * ESTACK) mf (hg_wrote ef mf v).

(* the walk of the block, +0x11c4 .. +0x128c (a Theorem Labs lane proves this) *)
Definition h_core_stmt : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) pos mf SF v cd,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  frames Sc = [(4, pos)] -> own = [(4, pos)] -> frame_addr lyc 4 pos = SF ->
  st_nev S + k <= EV_MAX ->
  getr regs 2 = w64 mf -> getr regs 9 = w64 mf ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  mf mod 32 = 0 -> sp0 - 336 <= mf -> mf <= sp0 - 320 -> sp0 - STK <= mf - 2 * ESTACK ->
  getr regs 24 = w64 v -> 0 <= v < 65536 -> getr regs 25 = w64 (SF + 496) ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 208) 8 0 ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 64) 8 SF ->
  val_mem SEGS (mrestrict (w_H W) memc) (mf + 120) 8 cd -> 0 <= cd < 2 ^ 64 ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 464) 8 ->
  zero_shadow (aview SEGS (w_H W) memc) SHADOW_OFF (SF + 496) 16 ->
  SRr SEGS W (cfg_at SEGS (BASE + 0x11c4) regs memc mdc)
    (hg_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs mf (SF + 496) v cd).

(* the glue: the boundary layer's seg_H from the block's walk *)
Definition h_glue_stmt : Prop :=
  AR_laws SEGS B ->
  ameter_laws MT ->
  (forall s s' : astate, mo_le MT s s' 0) ->
  STK_LLVMF <= LLVMF_STK ->
  EV_LLVMF <= EV_LIB ->
  (forall inp, 0 <= SlotModel.t_any_fw inp < 65536) ->
  h_core_stmt ->
  seg_H_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
    asink_syms_T KS asink_none ameta_inv arodata_okS.

End c.
End b.
End a.
