(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements
   are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for reac-pw/fuzz_qdisc image A from
   proofs/libreac/fuzz_knock/lib/A/APgMainL.v (the loop closure) at origin/ossv/recipes 6ebe35ba632, with
   its module paths changed. rule 24 (reuse): no function is proved here; this file is the
   loop's induction and nothing else -- it adds no walk and no arithmetic.

   WHY THE INDUCTION IS ON THE BUDGET, NOT ON THE INPUT. knock's loop is input-driven: its body eats one,
   two or three bytes and the closure is an induction on a nat `fuel` with Z.to_nat rem <= fuel
   (APgMainL.v). fuzz_qdisc's loop is COUNTED: `budgets` is data[0] & 7, so 1 <= budgets <= 7 at the head
   (APgLoop0.qd_land7), and the body's `addiw s4,s4,-1` decreases it by one on every pass. So the fuel here
   is the budget, the entry needs fuel = 7, and the loop cannot run more than seven times whatever the
   input says -- the input's byte count is NOT the loop's measure (when the input runs out the body still
   runs, reading lead = 0 and selector = 0, which is what the C does through fuzz_u16 / fuzz_u8 on an
   exhausted cursor).

   AT fuel = 0 THE HEAD IS UNREACHABLE: INV_L 0 asks for 1 <= bud and (Z.to_nat bud <= 0)%nat at once, so
   the goal follows by exfalso -- the released plain proof's `{ exfalso. lia. }`. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/QPgMainL.v of this library, for fuzz_qdisc's
   ASan-UBSan image (fuzz_qdisc.asan-ubsan, sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062),
   LLVMFuzzerTestOneInput at 0x7e694. Only the module paths change (the lib/AU twins AWalkFw0 YCeh YCfm, the
   walk's context lib/AU/APgRt.v and its states lib/AU/APgLoop0.v, YCeh.ro_tfa_below_ofl); the statements and the
   proof are the A file's text over the lib/AU names.

   THE LOOP in this image. The head is ss_L 0x7e728 (`beqz s10`) and the body is
     S1 (the input bytes, 0x7e728 .. the join ss_J 0x7e78c, lib/AU/APgMain1.v)
     S2 (the frame-rate read, 0x7e78c-0x7e79c, to ss_C 0x7e7a0, lib/AU/APgMain2.v)
     S3 (the two calls, the decrement and the back edge, 0x7e7a0-0x7e7c0, lib/AU/APgMain3.v),
   with the decrement `addiw s4,s4,-1` at 0x7e7b8, the back edge `bnez s4` at 0x7e7bc and the exit
   `j 0x7e848` at 0x7e7c0. S1, S2, S3 and the exit S7 are the Section hypotheses below. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YK11 YK15 YK18 YK0s YP09 YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0 YCeh YCfm APgRt APgLoop0.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
Hypothesis S1 : forall fuel : nat,
  rt_from B MT FP POST ss_J (INV_J B MT fuel) -> rt_from B MT FP POST ss_L (INV_L B MT fuel).
Hypothesis S2 : forall fuel : nat,
  rt_from B MT FP POST ss_C (INV_C B MT fuel) -> rt_from B MT FP POST ss_J (INV_J B MT fuel).
Hypothesis S3 : forall fuel : nat,
  rt_from B MT FP POST ss_L (INV_L B MT fuel) ->
  rt_from B MT FP POST ss_X (INV_X B MT) ->
  rt_from B MT FP POST ss_C (INV_C B MT (S fuel)).
Hypothesis SX : rt_from B MT FP POST ss_X (INV_X B MT).
Lemma rt_L : forall fuel : nat, rt_from B MT FP POST ss_L (INV_L B MT fuel).
Proof.
induction fuel as [|f IH].
- intros cx E k acc ly3 S3' W3 ms3 md3 HB HE HJ Hfr HM HINV HS. exfalso.
  destruct HINV as (_ & _ & _ & _ & _ & cur & rem & bud & c & _ & _ & _ & _ & Hb & Hf).
  assert (Hle : (1 <= Z.to_nat bud)%nat) by lia. clear - Hle Hf. lia.
- exact (S1 (S f) (S2 (S f) (S3 f IH SX))).
Qed.
(* the loop as lib/AU/APgMain0.v's entry segment needs it: the budget is at most 7 *)
Lemma rt_loop : rt_from B MT FP POST ss_L (INV_L B MT 7).
Proof. exact (rt_L 7). Qed.
End d.
End b.
