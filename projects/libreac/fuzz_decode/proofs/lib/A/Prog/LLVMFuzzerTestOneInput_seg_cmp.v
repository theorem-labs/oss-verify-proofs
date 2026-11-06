(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* LLVMFuzzerTestOneInput_seg_cmp: proves no function (kind: segment lemma).
   llvm_a_cmp_ok, the premise llvm_a_cmp_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v's dec_llvmf_holds_of_segs:
   the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput over +0x5fc .. +0x744, from the return of
   reac_decode_plain_le (llvm_a_st_5fc) to the return of reac_upstream_channels (llvm_a_st_748).

   The segment is cut at three inner points (all in LLVMFuzzerTestOneInput_seg_cmp_defs.v): +0x624 (cmp_q624, the
   scan loop's head, reached when the plain check refused), +0x66c (cmp_q66c, reached when it passed) and +0x734
   (cmp_q734, the call site of free #1, reached from both).  The pieces:
     LLVMFuzzerTestOneInput_seg_cmp_head.v   cmp_head   st_5fc  -> q624 \/ q66c  (+0x5fc..+0x620; the
                                                        +0x604 and +0x614 edges into the abort block refuted)
     LLVMFuzzerTestOneInput_seg_cmp_scan.v   cmp_scan   q624 -> q734  (the scan loop L2; its inline report and the
                                                        +0x668 abort edge refuted)
     LLVMFuzzerTestOneInput_seg_cmp_loop.v   cmp_cmp    q66c -> q734  (the stores and the register setup, then the
                                                        bcmp double loop L3/L4 by SRr_loopZ with the measure
                                                        nch*ns - (c*ns + k), each turn cmp_l34_body of
                                                        LLVMFuzzerTestOneInput_seg_cmp_after.v, the exit carried by
                                                        LLVMFuzzerTestOneInput_seg_cmp_x734.v)
     LLVMFuzzerTestOneInput_seg_cmp_tail.v   cmp_tail   q734 -> st_748  (free #1 and reac_upstream_channels)
   Every branch into +0xa4c..+0xb60 is refuted in those files, never stepped. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YI00 YO09 YM05 YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaRun PaShadow PaJournal PaStep DecodeSyms DecodeList DecodeAddr DecodePa DecodeImg DecodePaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import YC1g YC1h YC1i YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_seg_cmp_defs LLVMFuzzerTestOneInput_seg_cmp_head LLVMFuzzerTestOneInput_seg_cmp_scan
LLVMFuzzerTestOneInput_seg_cmp_loop LLVMFuzzerTestOneInput_seg_cmp_tail.
Open Scope Z_scope.

Section cmp.
Context {rc : YM05.RunCeil}.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Theorem llvm_a_cmp_ok :
  @llvm_a_cmp_stmt rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_cmp_stmt.
intros HPCF HUTR HCELLS HROR HRONE LAWS ML MTL ABCMP AFREE LUC cx W5 c5 HB HR H5fc.
assert (HPREM : @cmp_prem rc RA_LLVMF B MT)
  by exact (conj HPCF (conj HUTR (conj HCELLS (conj HROR (conj HRONE (conj LAWS (conj ML (conj MTL
              (conj ABCMP (conj AFREE LUC)))))))))).
apply (SRr_bind _ W5 c5 _ _ (cmp_head asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL
  RLO RHI HPREM cx W5 c5 HB HR H5fc)).
intros W6 c6 _ [H624 | H66c].
- apply (SRr_bind _ W6 c6 _ _ (cmp_scan asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL
    RLO RHI HPREM cx W6 c6 HB HR H624)).
  intros W7 c7 _ H734.
  exact (cmp_tail asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI HPREM
    cx W7 c7 HB HR H734).
- apply (SRr_bind _ W6 c6 _ _ (cmp_cmp asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL
    RLO RHI HPREM cx W6 c6 HB HR H66c)).
  intros W7 c7 _ H734.
  exact (cmp_tail asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI HPREM
    cx W7 c7 HB HR H734).
Qed.

End cmp.
