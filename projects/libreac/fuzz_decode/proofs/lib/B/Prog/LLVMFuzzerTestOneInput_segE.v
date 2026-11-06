(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segE: segment crt1 of image B's LLVMFuzzerTestOneInput (+0x5cc .. +0x6ec), i.e.
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v llvm_b_crt1_stmt: from llvm_b_st_5cc to llvm_b_st_6f0.

   The segment is the decode-result check (+0x5ec), the 0xa5 scan loop L1 (+0x5f4 .. +0x650), the spill of
   copy + 50 (+0x658), the two dispatch tests (+0x65c, +0x668) and the four calls check_round_trip (+0x68c),
   check_braid (+0x6bc), __asan_memset (+0x6d4) and reac_decode_plain_le (+0x6ec).  It is assembled here from
   the five parts the lane proved apart (the cut points are lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_defs.v):
     c1h_head  (LLVMFuzzerTestOneInput_segX_crt1_head.v)  +0x5cc to the first call,
     c1k_crt   (LLVMFuzzerTestOneInput_segX_crt1_kcrt.v)   the check_round_trip call and the run +0x690 .. +0x6bc,
     c1k_braid (LLVMFuzzerTestOneInput_segX_crt1_stage.v)  the check_braid call and the run +0x6c0 .. +0x6d4,
     c1k_memset(LLVMFuzzerTestOneInput_segX_crt1_stage.v)  the __asan_memset call and the run +0x6d8 .. +0x6ec,
     c1s_plain (LLVMFuzzerTestOneInput_segX_crt1_stage.v)  the reac_decode_plain_le call to the end state.
   c1e_base here is what the slot pre (dec_b_base, dec_b_rom) gives them all (c1_pre).
   Rule 24: no called function is proved here; each stays a premise of the statement. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_defs
  LLVMFuzzerTestOneInput_segX_crt1_head LLVMFuzzerTestOneInput_segX_crt1_stage
  LLVMFuzzerTestOneInput_segX_crt1_kcrt.
Import ListNotations.
Open Scope Z_scope.

Section SegE. Context {rc : YM05.RunCeil}.
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
Local Abbreviation segs := decodesegsB0.

(* The slot pre gives the segment its frame, its chain and its budgets: lib/B/Prog/LLVMFuzzerTestOneInput_cg.v
   dec_lib_pre_x and its afn_pre (lib/Reusable/YCbq.v:336). *)
Lemma c1e_base : forall cx : dctx,
  @dec_b_base rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  dec_b_rom cx -> @c1_pre rc B RA_LLVMF cx.
Proof.
  intros cx HBASE HROM.
  destruct HBASE as ((HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & Hqt) & Hra & _ & _ & Hblk & Hlen & _ &
                     _ & Hnev & Hlive & _).
  split; [exact Hret|]. split; [exact Hra|]. split; [rewrite Hra in Hra4; exact Hra4|].
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact Hstk|]. split; [exact Hch|].
  split; [destruct Hblk as [[H0 _] | [_ Hin]]; [left; exact H0 | right; exact Hin]|].
  split; [destruct Hblk as [[H0 _] | [Hb _]]; [lia | lia]|].
  split; [exact Hlen|]. split; [exact Hnev|]. split; [exact Hlive | exact HROM].
Qed.

(* ---- the segment ---- *)
Theorem llvm_b_crt1 :
  @llvm_b_crt1_stmt rc asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
  intros HCELLS HOWN HERR LAWS MLAWS MTL MTF AMS ACRT LCB LPL cx W' c' HBASE HROM H5cc.
  apply (c1h_head rc B MT RA_LLVMF LAWS MTL HCELLS HOWN HERR).
  - exact (c1k_crt rc B MT RA_LLVMF HCELLS HOWN HERR LAWS MTL ACRT
             (c1k_braid B MT RA_LLVMF HCELLS HOWN HERR LAWS AMS LPL LCB)).
  - exact (c1k_braid B MT RA_LLVMF HCELLS HOWN HERR LAWS AMS LPL LCB).
  - exact (c1k_memset B MT RA_LLVMF HCELLS HOWN HERR LAWS AMS LPL).
  - exact (c1e_base cx HBASE HROM).
  - exact H5cc.
Qed.
End SegE.
