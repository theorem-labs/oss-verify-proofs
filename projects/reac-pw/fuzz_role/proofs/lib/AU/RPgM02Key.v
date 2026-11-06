(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Key.v at 48d3cf0d8e40 (its closing
   theorem rt_m02_key_A and m2k_near) for image B (fuzz_rate.asan-ubsan): the four pieces are image B's files
   lib/AU/RtPgM02KeyCB.v, RtPgM02KeyVB.v, RtPgM02KeyFB.v chained by lib/AU/RtPgM02KitB.v m2kb_chain, and pod_nearest's
   contract comes from lib/AU/RtPgNearB.v rt_pod_nearest_B (its Section hypotheses are this file's). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgM02KeyB.v at f07713e8e823 and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02Key.v at 887bee7c56d for reac-pw/fuzz_role image B (fuzz_role.asan-ubsan):
   the four pieces are image B's files lib/AU/RPgM02KeyC.v, RPgM02KeyI.v, RPgM02KeyF.v and RPgM02KeyV.v chained by
   lib/AU/RPgM02KeyBase.v m2k_chain; pod_nearest's contract is the theorem lib/AU/RPgNearA.v rl_pod_nearest_B,
   called inside lib/AU/RPgM02KeyF.v, and check_role's lib/AU/RPgCheck.v rl_check_role_B, called inside
   lib/AU/RPgM02KeyV.v; the Section hypotheses are role A's (MTL, LAWS, ASTRCMP, HGOT, HSC) at image B's
   addresses. *)
(* reac-pw/fuzz_role, image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes): THE KEY MATCH of
   segment M02's match half. It proves lib/AU/RPgSeg.v's rs_piece_W11b_key_stmt: from the cut rs_cut_KM at
   RS_KM 0x82370 (entry m of the record is a String key and entry m + 1 exists) the walk reaches the piece's end
   cuts: rs_cut_O at 0x82278 with at = m + 2 when the key is not "reac.cfg.role", and otherwise rs_cut_MAL or
   rs_cut_T through the value the record holds at entry m + 1 (ABS 0x8245c is not reached: the `bltz a2` 0x82378 is
   dead). Proves no function (kind: segment lemma).

   THE WALK, IN FOUR PIECES, EACH ITS OWN FILE OVER THE ONE SHARED LAYER lib/AU/RPgM02KeyBase.v:
     lib/AU/RPgM02KeyC.v  rl_m02_key_cmp_B   0x82370 -> the strcmp wrapper 0x41b68 -> 0x823b8: the trap 0x82374, the
                                             dead `bltz`, the five spills, the compare of the key's text with
                                             .str.3 0x20f20, and the two arms: the mismatch to O 0x82278 (the scan
                                             goes on at m + 2) and the match (the flag cell, the traps 0x823c8 and
                                             0x823d0, the code into s9) to the value's address at 0x823d8.
     lib/AU/RPgM02KeyI.v  rl_m02_key_val_B   0x823d8: the entry's type, the dispatch `beq 6` / `bne 4`, and the Int arm
                                             (the size test and the body word) to the join or to MAL.
     lib/AU/RPgM02KeyF.v  rl_m02_key_float_B 0x8247c: the Float arm, its size test, the one `flw` of this half and
                                             pod_nearest 0x82eb4, to the join or to MAL.
     lib/AU/RPgM02KeyV.v  rl_m02_key_tail_B  0x824dc: the role's range test to MAL, check_role 0x82aac, and the jump
                                             to T 0x82504.
   This file is only the assembly: m2k_chain hands each piece the continuations of the pieces after it, so no piece
   ever sees another's proof. The one float state of the walk up to the `flw` is the cut's own fx2, which is why the
   strcmp wrapper's contract is held at EVERY float state (ASTRCMP below) and not only at the harness's.

   WHAT IS A SECTION HYPOTHESIS. MTL and LAWS (the two runtime laws), the strcmp wrapper's contract at every
   float state at its 4-byte jump 0x41b68, and the two symbol-record cells the pod_nearest lift reads (the GOT cell
   0x9aad0 of the shadow offset and the shadow-offset cell 0xa3678). Every other callee of this half is a theorem on
   the branch: RPgCheck.rl_check_role_B and RPgNearA.rl_pod_nearest_B. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgM02Base RPgM02KeyBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgM02KeyC RPgM02KeyI RPgM02KeyF RPgM02KeyV.
Local Open Scope Z_scope.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the strcmp wrapper's contract, at every float state: rs_from_KM quantifies over the cut's own float state *)
Hypothesis ASTRCMP : forall fy : YK11.FPState, @astrcmp_realizes fy rc rsegs B M2_STRCMP.
(* the two symbol-record cells the pod_nearest lift reads *)
Hypothesis HGOT : as_got_shadow B = 0x9aad0.
Hypothesis HSC : as_shadow_cell B = 0xa3678.

(* KM -> O (mismatch, at = m + 2) | KV -> FLT / MAL / JN -> MAL / T, by m2k_chain *)
Theorem rl_m02_key_B : rs_piece_W11b_key_stmt rsegs B MT.
Proof using MTL LAWS ASTRCMP HGOT HSC.
exact (m2k_chain B MT (rl_m02_key_tail_B B MT MTL LAWS) (rl_m02_key_float_B B MT MTL LAWS HGOT HSC)
  (rl_m02_key_val_B B MT MTL LAWS) (rl_m02_key_cmp_B B MT MTL LAWS ASTRCMP)).
Qed.

End k.
