(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 22 of its 40 lines of code are new or changed and 563 lines of the source are left out. *)
(* The closing step of fuzz_decode.asan's LLVMFuzzerTestOneInput walk (image A), in the shape of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v:258-259 (tfib_lib_x from its stage lemmas). *)
(* dec_llvmf_holds: the image-A walk of LLVMFuzzerTestOneInput meets its slot contract.
   It is the composition dec_llvmf_holds_of_segs (LLVMFuzzerTestOneInput_segs.v) applied to the nine segment
   theorems, one per segment file:
     entry, early_ret  LLVMFuzzerTestOneInput_seg_entry.v
     early             LLVMFuzzerTestOneInput_seg_early.v
     copy              LLVMFuzzerTestOneInput_seg_copy.v
     inspect           LLVMFuzzerTestOneInput_seg_inspect.v
     crt1              LLVMFuzzerTestOneInput_seg_crt1.v
     cmp               LLVMFuzzerTestOneInput_seg_cmp.v
     up                LLVMFuzzerTestOneInput_seg_up.v
     exit              LLVMFuzzerTestOneInput_seg_exit.v
   Every callee is a premise of dec_llvmf_holds_stmt (LLVMFuzzerTestOneInput_cg.v); nothing else is assumed. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YG0d YG0f YG0n YCbq YC5d YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require
  LLVMFuzzerTestOneInput_seg_entry LLVMFuzzerTestOneInput_seg_early LLVMFuzzerTestOneInput_seg_copy
  LLVMFuzzerTestOneInput_seg_inspect LLVMFuzzerTestOneInput_seg_crt1 LLVMFuzzerTestOneInput_seg_cmp
  LLVMFuzzerTestOneInput_seg_up LLVMFuzzerTestOneInput_seg_exit.
Open Scope Z_scope.

Section w. Context {rc : YM05.RunCeil}.
(* LLVMFuzzerTestOneInput_cg.v's Section h, variable for variable. *)
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
  @dec_llvmf_holds_stmt rc asink_syms tfib_K asink_none ameta_inv arodata_okS asink_img_laws ro_below_ofl
    RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
  (* Each segment theorem is applied by name and unified against its premise of dec_llvmf_holds_of_segs, so the
     proof does not depend on which Section variables each segment file happened to abstract. *)
  apply dec_llvmf_holds_of_segs.
  - apply LLVMFuzzerTestOneInput_seg_entry.llvm_a_entry_ok.
  - apply LLVMFuzzerTestOneInput_seg_early.llvm_a_early_ok.
  - apply LLVMFuzzerTestOneInput_seg_entry.llvm_a_early_ret_ok.
  - apply LLVMFuzzerTestOneInput_seg_copy.llvm_a_copy_ok.
  - apply LLVMFuzzerTestOneInput_seg_inspect.llvm_a_inspect_ok.
  - apply LLVMFuzzerTestOneInput_seg_crt1.llvm_a_crt1_ok.
  - apply LLVMFuzzerTestOneInput_seg_cmp.llvm_a_cmp_ok.
  - apply LLVMFuzzerTestOneInput_seg_up.llvm_a_up_ok.
  - apply LLVMFuzzerTestOneInput_seg_exit.llvm_a_exit_ok.
Qed.
End w.
