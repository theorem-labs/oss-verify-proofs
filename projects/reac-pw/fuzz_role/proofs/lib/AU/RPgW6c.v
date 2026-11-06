(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6cB.v at 05426fac6916 for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): its closing theorem only (the bridges are lib/AU/RPgW6cGlue.v,
   the helpers lib/AU/RPgW6cKit.v); the statement is lib/AU/RPgSeg.v's rs_piece_W6c_stmt; the intrinsics are
   __asan_memcpy 0x5116c and __asan_memset 0x51608; the allocator meter's laws are a premise, as ebb_J_of asks. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the walk piece "ent_build C"
   of LLVMFuzzerTestOneInput (0x80020), ent_build's cases 6, 7 and 8 from their switch entries 0x811d8 / 0x81050 /
   0x8122c to the join J 0x818d8, as lib/AU/RPgSeg.v states it (rs_piece_W6c_stmt). Proves no function (kind:
   segment lemma). The two callees are the kernel's contracts of __asan_memcpy (0x5116c) and __asan_memset
   (0x51608), YG0d.aintrin_realizes, and the allocator meter's laws YC5d.ameter_laws: the Section hypotheses of the
   theorem. The three heads are lib/AU/RPgW6c6.v, RPgW6c7.v, RPgW6c8.v, the two tails lib/AU/RPgW6cTail.v, the bridge
   to the cuts lib/AU/RPgW6cGlue.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgSeg RPgW6cBase RPgW6cTail RPgW6cGlue.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgW6c6 RPgW6c7 RPgW6c8.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6CB_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6CB_SET.

Theorem w6cb_piece : rs_piece_W6c_stmt rsegs B MT.
Proof using MTL AMEMCPY AMEMSET.
exact (w6cb_piece_of B MT MTL (RPgW6c6.w6cb_h6 B) (RPgW6c7.w6cb_h7 B) (RPgW6c8.w6cb_h8 B)
  (w6cb_tail_cpy B AMEMCPY) (w6cb_tail_set B AMEMSET)).
Qed.
End b.
