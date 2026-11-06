(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece A1 (the kid fetch, B 0x83a60 = exv_pc 0x534
   to LK, B 0x83b1c = exv_pc 0x5f0): the SYMBOLIC STATES the piece runs the table engine from (one per arm of the
   fetch: vv = 0; vv <> 0 with i >= count; vv <> 0 with i < count). Definitions only.
   Atoms: registers 0-31 (sr_atoms), 32 vv (the node 152(s1)), 33 i (136(s1)), 34 count (the node's +40), 35 kids (the
   node's +24), 36 56 i (112(s1)). The arm of the bgeu at B 0x83a84 is fixed by a condition fact on atoms 33 / 34.
   Rule 24: proves no function (kind: segment lemma helper).
   Numerals: 9, 19, 25 (WORD: register numbers s1, s3, s9); 8, 24, 40, 56, 72, 80, 88, 112, 136, 152, 160 (LENGTH:
   B's spill slots, ExvB_Stmt.v CUT_CL, and the pj node's fields / size); 32, 36 (LENGTH: in->differs at q + 32, its
   4 bytes); 3 (WORD: the shadow shift / alignment exponent); 4096, 2 ^ 47 (LENGTH: address-space bounds);
   140735332483072 (DERIVED: YM05's CEIL_MIN, the floor of alloc_ceiling); 3145728 = 3 * 2 ^ 20 (LENGTH: EXV_PRE's
   text bound); 0x534, 0x5f0 (DERIVED: cut offsets, B address minus B's ex_value entry). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Open Scope Z_scope.

Definition A1_PC : Z := exv_pc 0x534.
Definition A1_LK : Z := exv_pc 0x5f0.
Definition A1_TBL : ctable := B_prog_tbl.
(* the shadow base s9, and shadow_addr (q + 32) as B 0x83a50 spills it at 72(s1) *)
Definition a1_Bx : sv := SOff 25 0.
Definition a1_shq : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 32) (SLit 3)) (SOff 25 0).
(* CEIL_MIN (YM05: alloc_ceiling's floor) as a literal: the engine's static check computes over the facts, so no
   fact may carry the RunCeil field *)
Definition a1_fq : afact := mkAF 140735332483072 (2 ^ 47 - 40) 3.
Definition a1_fsb : afact := mkAF SHADOW_OFF SHADOW_OFF 0.
Definition a1_fv : afact := mkAF 4096 (2 ^ 47 - 56) 3.
(* the kids array and the item index of the K arm (i <= len <= 3 * 2 ^ 20) *)
Definition a1_fk : afact := mkAF 4096 (2 ^ 47) 0.
Definition a1_fi : afact := mkAF 0 3145728 0.

(* vv = 0: only 152(s1) is read *)
Definition a1_rs0 : smem := [YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SLit 0))]].
Definition ss_a10 : sstate := mkSS A1_PC sr_atoms a1_rs0 None (mkFacts [] [] []).
Definition a1_SH0 : list shent := [].

(* vv <> 0, i >= count: the node's count, the q + 32 shadow, the store of in->differs *)
Definition a1_rsL : smem :=
[ YP09.mkRegion (Some 9%nat) 72 160 0 0
    [YP09.mkChunk 152 (CVal 8 (SOff 32 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 40));
     YP09.mkChunk 136 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 a1_shq); YP09.mkChunk 80 (CVal 8 (SOff 19 32))];
  YP09.mkRegion (Some 32%nat) 40 48 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 34 0))];
  YP09.mkRegion (Some 19%nat) 32 36 32 36 [] ].
Definition a1_GL : facts :=
mkFacts [(19%nat, a1_fq); (25%nat, a1_fsb); (32%nat, a1_fv)] [mkAC BC_GEU (SOff 33 0) (SOff 34 0)] [].
Definition ss_a1L : sstate := mkSS A1_PC sr_atoms a1_rsL None a1_GL.
Definition a1_SHL : list shent := [mkSHE 32 0 56; mkSHE 19 0 40].

(* vv <> 0, i < count: the node's count and kids, the kid's address *)
Definition a1_rsK : smem :=
[ YP09.mkRegion (Some 9%nat) 56 160 0 0
    [YP09.mkChunk 152 (CVal 8 (SOff 32 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 40));
     YP09.mkChunk 136 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 32 24));
     YP09.mkChunk 112 (CVal 8 (SOff 36 0))];
  YP09.mkRegion (Some 32%nat) 24 48 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0))] ].
Definition a1_GK : facts :=
mkFacts [(25%nat, a1_fsb); (32%nat, a1_fv); (33%nat, a1_fi); (35%nat, a1_fk)]
  [mkAC BC_LTU (SOff 33 0) (SOff 34 0)] [].
Definition ss_a1K : sstate := mkSS A1_PC sr_atoms a1_rsK None a1_GK.
Definition a1_SHK : list shent := [mkSHE 32 0 56].
