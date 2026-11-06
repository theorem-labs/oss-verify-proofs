(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: written for libreac/fuzz_decode's ASan+UBSan build (image B): the program walk
   of LLVMFuzzerTestOneInput, the statement dec_llvmf_holds_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v, closed by
   the composition dec_llvmf_holds_of_segs (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v) applied to the nine segment
   theorems of lib/B/Prog/LLVMFuzzerTestOneInput_seg{A,B,C,D,E,F,G,H}.v. Composition in the shape of cgif's
   lib/A/ACfj.v:230-259 (origin/ossv/recipes c8557374ad2e). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YI04 YG0v YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segA LLVMFuzzerTestOneInput_segB LLVMFuzzerTestOneInput_segC
  LLVMFuzzerTestOneInput_segD LLVMFuzzerTestOneInput_segE LLVMFuzzerTestOneInput_segF LLVMFuzzerTestOneInput_segG
  LLVMFuzzerTestOneInput_segH.

Section walk. Context {rc : YM05.RunCeil}.
(* The Section of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v, variable for variable. *)
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem dec_llvmf_holds :
  dec_llvmf_holds_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS asink_img_laws ro_below_ofl
    RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
  apply dec_llvmf_holds_of_segs.
  - apply llvm_b_entry_ok.
  - apply llvm_b_early.
  - apply llvm_b_early_ret.
  - apply llvm_b_copy_ok.
  - apply llvm_b_inspect_ok.
  - apply llvm_b_crt1.
  - apply llvm_b_cmp_ok.
  - apply llvm_b_up_ok.
  - apply llvm_b_exit_ok.
Qed.
End walk.
