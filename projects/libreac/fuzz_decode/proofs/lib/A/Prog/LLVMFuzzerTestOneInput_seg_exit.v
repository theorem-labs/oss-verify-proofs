(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, with its module names changed; 42 of its 66 lines of code are new or changed and 535 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit: the exit segment of the image-A walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, llvm_a_exit_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v (proves no function, kind:
   segment lemma), composed from the six pieces of lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v (cgif
   lib/A/ACfj.v's SRr_bind form), each proved in its own file LLVMFuzzerTestOneInput_seg_exit_<piece>.v. *)
From Stdlib Require Import ZArith NArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YI00 YI04 YG0v YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_exit_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LLVMFuzzerTestOneInput_seg_exit_check
  LLVMFuzzerTestOneInput_seg_exit_scan LLVMFuzzerTestOneInput_seg_exit_crt LLVMFuzzerTestOneInput_seg_exit_braid
  LLVMFuzzerTestOneInput_seg_exit_free LLVMFuzzerTestOneInput_seg_exit_tail.
Import ListNotations.
Open Scope Z_scope.

Section seg_exit. Context {rc : YM05.RunCeil}.
(* The Variables of LLVMFuzzerTestOneInput_segs.v's Section seg; llvm_a_exit_stmt uses no Section hypothesis. *)
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

(* The six pieces give the segment: +0x86c runs the header checks to +0x960 (accepted) or +0x908 (refused), the
   refused case scans to +0x98c, the accepted case calls check_round_trip and check_braid to +0x98c, both free to the
   join +0x9a8, and the tail returns; the early return enters the tail at +0x9a8 directly. *)
Theorem llvm_a_exit_of_pieces :
  ex_check_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI ->
  ex_scan_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI ->
  ex_crt_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI ->
  ex_braid_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI ->
  ex_free_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI ->
  ex_tail_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI ->
  llvm_a_exit_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
intros CHECK SCAN CRT BRAID FREE TAIL.
unfold llvm_a_exit_stmt.
intros HPCF HUTR HCELLS HRZ HNE LAWS ML MTL MTF HXL ASF FFL AFREE ACRT LCB HSK HMK cx W c HB HR [H86c | H9a8].
- eapply SRr_bind; [exact (CHECK LAWS ML MTL cx W c HB HR H86c) |].
  intros W1 c1 _ [H960 | H908].
  + eapply SRr_bind; [exact (CRT HUTR HCELLS HRZ HNE LAWS ML MTL MTF ACRT cx W1 c1 HB HR H960) |].
    intros W2 c2 _ H978.
    eapply SRr_bind; [exact (BRAID HCELLS LAWS ML MTL LCB cx W2 c2 HB HR H978) |].
    intros W3 c3 _ H98c.
    eapply SRr_bind; [exact (FREE HPCF HUTR LAWS ML MTL AFREE cx W3 c3 HB HR H98c) |].
    intros W4 c4 _ H9a8.
    exact (TAIL LAWS ML MTL MTF HXL ASF FFL HSK HMK cx W4 c4 HB HR H9a8).
  + eapply SRr_bind; [exact (SCAN LAWS ML MTL cx W1 c1 HB HR H908) |].
    intros W3 c3 _ H98c.
    eapply SRr_bind; [exact (FREE HPCF HUTR LAWS ML MTL AFREE cx W3 c3 HB HR H98c) |].
    intros W4 c4 _ H9a8.
    exact (TAIL LAWS ML MTL MTF HXL ASF FFL HSK HMK cx W4 c4 HB HR H9a8).
- exact (TAIL LAWS ML MTL MTF HXL ASF FFL HSK HMK cx W c HB HR H9a8).
Qed.

(* The exit segment: the six pieces, each Qed in its own file. *)
Theorem llvm_a_exit_ok :
  llvm_a_exit_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
apply llvm_a_exit_of_pieces.
- apply LLVMFuzzerTestOneInput_seg_exit_check.ex_check_ok.
- apply LLVMFuzzerTestOneInput_seg_exit_scan.ex_scan_ok.
- apply LLVMFuzzerTestOneInput_seg_exit_crt.ex_crt_ok.
- apply LLVMFuzzerTestOneInput_seg_exit_braid.ex_braid_ok.
- apply LLVMFuzzerTestOneInput_seg_exit_free.ex_free_ok.
- apply LLVMFuzzerTestOneInput_seg_exit_tail.ex_tail_ok.
Qed.

End seg_exit.
