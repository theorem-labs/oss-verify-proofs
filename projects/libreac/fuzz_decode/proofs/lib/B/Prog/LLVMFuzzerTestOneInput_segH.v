(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segH: segment group 8 (exit) of the image-B walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput: llvm_b_exit_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_segs.v, from llvm_b_st_96c (the return
   of reac_upstream_decode #3) and from the early-return join llvm_b_st_ae0, to the slot post at the return (+0xb80).
   The walk, in code order (each piece in its own file):
     +0x96c .. +0xab8  the upstream header checks, the result check, check_round_trip #2 and check_braid #2 or the
                       scan loop L6                              segX_exit_hd.v ex_96c_ab8 (loop: segX_exit_loop.v)
     +0xab8 .. +0xac8  free #2 (s7) and free #3 (s11)           segX_exit_fr.v fr_free_at
     +0xac8 .. +0xae0  the local re-poisoned, t0 / a6 / a7 reloaded   segX_exit_rp.v rp_ae0
                       (the two together: segX_exit_ab.v ex_ab8_ae0)
     +0xae0 .. +0xb80  the teardown and the return              segX_exit_td.v llvm_b_exit_td
   The cut points between the files are segX_exit_defs.v's ex_ab8 / ex_fr and the interface's llvm_b_st_ae0; the
   composition is cgif's lib/A/ACfj.v:230-259 stage chain (SRr_bind from cut to cut). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LeafCgKit LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segX_exit_defs
  LLVMFuzzerTestOneInput_segX_exit_td LLVMFuzzerTestOneInput_segX_exit_ab LLVMFuzzerTestOneInput_segX_exit_hd.
Import ListNotations.
Open Scope Z_scope.

Section sh. Context {rc : YM05.RunCeil}.
(* lib/B/Prog/LLVMFuzzerTestOneInput_segs.v Section seg, variable for variable. *)
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

Theorem llvm_b_exit_ok :
  llvm_b_exit_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_exit_stmt.
intros HPCF HUTR HCELLS HROWN HNOERR LAWS ML MTL MTF HXL ASF FFL AFREE ACRT LCB HSK HMK cx W' c' HBASE HROM
  [H96c | Hae0].
- eapply SRr_bind.
  { exact (ex_96c_ab8 asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
      HCELLS HROWN HNOERR LAWS MTL ACRT LCB cx W' c' HBASE HROM H96c). }
  intros W2 c2 _ Hab.
  eapply SRr_bind.
  { exact (ex_ab8_ae0 asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
      HPCF HUTR LAWS MTL AFREE cx W2 c2 HBASE Hab). }
  intros W3 c3 _ Hae.
  exact (llvm_b_exit_td asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    LAWS ML MTL MTF ASF FFL HSK HMK HXL cx W3 c3 HBASE Hae).
- exact (llvm_b_exit_td asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI
    LAWS ML MTL MTF ASF FFL HSK HMK HXL cx W' c' HBASE Hae0).
Qed.
End sh.
