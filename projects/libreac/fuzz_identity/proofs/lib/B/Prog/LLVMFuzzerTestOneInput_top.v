(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v, with its module paths and module names changed; 72 of its 114 lines of code are new or changed and 538 lines of the source are left out. *)
(* The composition of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B, fuzz_identity.asan-ubsan 0x80774):
   the segment statements of the boundary layer (LLVMFuzzerTestOneInput_inv.v) chained from the entry to the
   return give the contract (LLVMFuzzerTestOneInput.v tLLVMFuzzerTestOneInput_spec). No segment is proved here
   and no cut is taken (no rz_cut): each step is SRr_bind of the next segment, the record loop is SRr_loop on
   nrec - i (inv_rec carries i < nrec, so the rotated loop's test is S i < nrec or S i = nrec), the four cases
   of the switch join at inv_tail, and the contract's continuation is applied at the return with SRr_srealizes,
   where the leaf is LL 0 (m_fs md) [] (identity's library shape, HLIBK).
   The proof is the B twin of the A composition (lib/A/Prog/LLVMFuzzerTestOneInput_inv.v pb_LLVMFuzzerTestOneInput,
   line 709). B differs in two places: the ignored-record path is its own segment
   (seg_D3r, inv_ignored -> inv_tail), and the statement also takes seg_early, which the chain does not need:
   the contract's pre-condition gives n = 0 or 0 < n < 2 ^ 26, so the run never takes the size >= 2 ^ 26 exit. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
Section c.
(* The contract's Section, in its order (LLVMFuzzerTestOneInput.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

(* The contract's library-shape hypothesis (LLVMFuzzerTestOneInput.v HLIBK), the only one the chain uses. *)
Hypothesis HLIBK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).

(* The boundary layer's names at this Section's parameters. *)
#[local] Notation acut := (@B.Prog.LLVMFuzzerTestOneInput_inv.acut fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF
A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation inv_rec := (@B.Prog.LLVMFuzzerTestOneInput_inv.inv_rec fx rc SK PI B MT XM_LIB RLO RHI
RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation inv_exit := (@B.Prog.LLVMFuzzerTestOneInput_inv.inv_exit fx rc SK PI B MT XM_LIB RLO RHI
RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation inv_tail := (@B.Prog.LLVMFuzzerTestOneInput_inv.inv_tail fx rc SK PI B MT XM_LIB RLO RHI
RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation inv_ret := (@B.Prog.LLVMFuzzerTestOneInput_inv.inv_ret fx rc SK PI B MT XN_LIB RA_LLVMF
LLVMF_STK EV_LIB asink_syms_T KS asink_none ameta_inv).
#[local] Notation pb_stmt := (@pb_LLVMFuzzerTestOneInput_stmt fx rc SK PI B MT XM_LIB XN_LIB RLO RHI LS RA_LLVMF
A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).

(* The boundary P of a cut, without the cut's common part. *)
Lemma top_acut_P : forall g pos mf k pc P W2 c2, acut g pos mf k pc P W2 c2 ->
exists ly2 S2 regs2 mem2 md2, P ly2 S2 W2 regs2 mem2 md2.
Proof.
intros g pos mf k pc P W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & _ & _ & _ & _ & _ & _ & _ & HP).
exists ly2, S2, regs2, mem2, md2. exact HP.
Qed.

Theorem pb_from_segs : pb_stmt.
Proof.
intros hA hB hC hD1 hD2 hD3r hD3 hD4 hD5 hD6 hLP hRX hE hF hG hH hI hJ hK hL _.
intros ly S0 W regs mem md p n pl M K HAI Hpre Hk.
rewrite HLIBK.
set (g := mkEctx ly S0 W mem md regs p n pl M).
assert (HW : SRr SEGS W (cfg_at SEGS (@A_LLVMFuzzerTestOneInputP rc PI) regs mem md)
  (inv_ret g (LL 0 (m_fs md) []))).
{ eapply SRr_bind; [exact (hA g W _ (conj eq_refl eq_refl) Hpre)|].
  intros W1 c1 _ (pos & mf & H1).
  eapply SRr_bind; [exact (hB g pos mf W1 c1 H1)|]. intros W2 c2 _ H2.
  (* from the loop's exit to the return *)
  assert (EXIT : forall W3 c3, inv_exit g pos mf W3 c3 -> SRr SEGS W3 c3 (inv_ret g (LL 0 (m_fs md) []))).
  { intros W3 c3 H3.
    eapply SRr_bind; [exact (hE g pos mf W3 c3 H3)|]. intros W4 c4 _ H4.
    eapply SRr_bind; [exact (hF g pos mf W4 c4 H4)|]. intros W5 c5 _ H5.
    eapply SRr_bind; [exact (hG g pos mf W5 c5 H5)|]. intros W6 c6 _ H6.
    eapply SRr_bind; [exact (hH g pos mf W6 c6 H6)|]. intros W7 c7 _ H7.
    eapply SRr_bind; [exact (hI g pos mf W7 c7 H7)|]. intros W8 c8 _ (nm & tk & dp & H8).
    eapply SRr_bind; [exact (hJ g pos mf nm tk dp W8 c8 H8)|]. intros W9 c9 _ H9.
    (* B's bad-widths run (0x81bb0 to 0x820fc, inv_J_end's slot) passes through seg_K too: no split here. *)
    eapply SRr_bind; [exact (hK g pos mf nm tk dp W9 c9 H9)|]. intros W10 c10 _ H10.
    exact (hL g pos mf nm tk dp W10 c10 H10). }
  (* the record loop, on nrec - i *)
  assert (LOOP : forall i W3 c3, inv_rec g pos mf i W3 c3 -> SRr SEGS W3 c3 (inv_exit g pos mf)).
  { apply (SRr_loop SEGS nat (fun i => (m_nrec g - i)%nat) (fun i => inv_rec g pos mf i) (inv_exit g pos mf)).
    intros i W3 c3 H3.
    eapply SRr_bind; [exact (hD1 g pos mf i W3 c3 H3)|]. intros W4 c4 _ (pl0 & H4).
    eapply SRr_bind; [exact (hD2 g pos mf i pl0 W4 c4 H4)|]. intros W5 c5 _ H5.
    eapply SRr_bind with (R := inv_tail g pos mf i pl0).
    { destruct H5 as [H5 | [H5 | [H5 | H5]]].
      - exact (hD3 g pos mf i pl0 W5 c5 H5).
      - exact (hD4 g pos mf i pl0 W5 c5 H5).
      - exact (hD5 g pos mf i pl0 W5 c5 H5).
      - exact (hD3r g pos mf i pl0 W5 c5 H5). }
    intros W6 c6 _ H6.
    eapply SRr_bind; [exact (hD6 g pos mf i pl0 W6 c6 H6)|]. intros W7 c7 _ H7.
    destruct (top_acut_P _ _ _ _ _ _ _ _ H7) as (ly7 & S7 & regs7 & mem7 & md7 & Hlt & _).
    destruct (Nat.lt_ge_cases (S i) (m_nrec g)) as [Hs | Hs].
    - eapply SRr_mono; [exact (hLP g pos mf i W7 c7 H7 Hs)|].
      intros W8 c8 _ H8. right. exists (S i). split; [clear - Hs; lia | exact H8].
    - eapply SRr_mono; [exact (hRX g pos mf i W7 c7 H7 ltac:(clear - Hlt Hs; lia))|].
      intros W8 c8 _ H8. left. exact H8. }
  eapply SRr_bind; [exact (hC g pos mf W2 c2 H2)|]. intros W3 c3 _ [H3 | [_ H3]].
  - eapply SRr_bind; [exact (LOOP 0%nat W3 c3 H3)|]. intros W4 c4 _ H4. exact (EXIT W4 c4 H4).
  - exact (EXIT W3 c3 H3). }
apply (SRr_srealizes SEGS W _ _ _ HW HAI).
intros W' c' Hle HAI' Hret. exact (Hk _ W' c' Hle HAI' Hret).
Qed.

Check (pb_from_segs : pb_stmt).

End c.
End b.
End a.

Print Assumptions pb_from_segs.
