(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 7 of its 47 lines of code are new or changed and 1232 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsfinal.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   RULE-24: proves function put_string (omx-clap-core/fuzz_state, image B = asan-ubsan, entry 0x85fc8). *)
(* put_string's walk on image B, CLOSED: put_string_spec (image B, fs.asan-ubsan, A_put_string 0x85fc8) from the four
   segments of ZZpsclose.ps_close: SEG1 ZZpsg1.psg1 (entry, fake-frame grant, the opening-quote put), SEG2 ZZpsg2.psg2
   (the scan loop or the empty arm, the run put), SEG3 ZZpsg3.psg3 (the closing-quote put), SEG4 ZZpstail.psg4 (the
   epilogue to the post). The image-A twin is lib/A/ZZpsfinal.v ps_put_string_spec (a working branch
   ca67007c8c2).
   The Section hypotheses are the walk's OPEN hypotheses, each with its owner: the SAME set as image A's (put_spec,
   FsShadowSyms, api_env, model_laws, stack_malloc_progressP, astack_malloc_realizesU at class 0, B's class-0 code map,
   astack_free_law, frame_flag_lawP, the use-after-return cell pair, fs_img_facts), each stated over image B's
   tfibsegs and lib/B's names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame FSW_frame3 FSW_put_string ZZpsclose ZZpsg1 ZZpsg2 ZZpsg3 ZZpstail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
Open Scope Z_scope.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* put's S0 contract: the callee, discharged at composition by the put lane's walk (FSW_put.v) *)
Hypothesis HPUT : FSH_Fn_writer.put_spec B tfibsegs.
(* the shadow-base cell pair (S0's FsShadowSyms; owner RELOC, discharged by S0's FSrtcellsS0 when it lands) *)
Hypothesis HSS : FsShadowSyms B.
(* the unit's runtime laws (owner RUNTIME: the donor's TfibLib) *)
Hypothesis HENV : api_env tfibsegs B.
Hypothesis HML : model_laws (as_universe B).
Hypothesis HSMP : stack_malloc_progressP B.
(* __asan_stack_malloc_0's statement (owner a Theorem Labs lane, walk open) *)
Hypothesis HSM0 : astack_malloc_realizesU tfibsegs B 0.
(* B's code map at class 0 (owner RELOC: TfibLib's tl_code) *)
Hypothesis HSMPC : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0.
(* the fake frame's release laws (owner RUNTIME) *)
Hypothesis HASF : astack_free_law tfibsegs B.
Hypothesis HFFL : frame_flag_lawP tfibsegs B.
(* the use-after-return cell pair (owner RELOC: TfibLib's tl_got_uar / tl_uar_cell) *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* fs's image facts (owner RELOC / RUNTIME) *)
Hypothesis HIMG : fs_img_facts tfibsegs B.

Theorem ps_put_string_spec : FSH_Fn_writer.put_string_spec B tfibsegs.
Proof.
  apply (ps_close B); [apply (psg1 B) | apply (psg2 B) | apply (psg3 B) | apply (psg4 B)]; assumption.
Qed.

End F.
