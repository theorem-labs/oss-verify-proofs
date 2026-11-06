(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v; 24 of its 67 lines of code are new or changed and 184 lines of the source are left out. *)
(* The early-return path of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): seg_early of
   lib/B/Prog/LLVMFuzzerTestOneInput_inv.v, from the entry slot 0x80774 with `2 ^ 26 <= size` to inv_ret
   (the branch at 0x80870 / 0x809e4, the landing at +0x1c5c (0x823d0), the frame release and the return).

   The start is contradictory: the contract's pre-condition (LLVMFuzzerTestOneInput.v,
   tLLVMFuzzerTestOneInput_pre, its fifth conjunct) says `(n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ ...)`,
   so under e_pre no entry state has `2 ^ 26 <= e_n g` and the path is never run. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
Section c.
(* The boundary file's Section c, in the same order. *)
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

(* The contract's size bound at the entry state: every input the pre-condition admits is below 2 ^ 26. *)
Lemma early_n_lt : forall g,
e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g -> e_n g < 2 ^ 26.
Proof.
intros g HPRE.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & HNP & _).
destruct HNP as [[Hn _] | [Hn _]]; lia.
Qed.

Lemma seg_early :
seg_early_stmt B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
intros g W2 c2 _ HPRE HN.
exfalso.
pose proof (early_n_lt g HPRE) as Hlt.
clear - HN Hlt; lia.
Qed.

Check (seg_early :
seg_early_stmt B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).
End c.
End b.
End a.

Print Assumptions seg_early.
