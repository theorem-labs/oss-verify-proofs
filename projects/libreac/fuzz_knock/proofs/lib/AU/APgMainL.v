(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/APgMainL.v of this library: THE LOOP CLOSURE of
   libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput in fuzz_knock.asan-ubsan (sha256
   f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82).  The module paths are the lib/AU twins; the states
   are lib/AU/APgStates.v's and the invariants lib/AU/APgLoop0.v's. *)

(* The loop head is ss_L at 0x7f154 (after the head test `beqz s9,0x7f2c4` at 0x7f150) and the body is S3 LOOP ->
   S4 TAIL -> S5 MID -> S6 CHECKS; the back edge is `bnez s10,0x7f150` at 0x7f298, which re-enters through the head
   test.  This file closes the loop.

   WHY AN INDUCTION ON FUEL (as lib/A/APgMainL.v:10-16)
   The loop runs while the input has bytes left, the body eats one, two or three of them, and it also leaves when the
   countdown s10 = 4096 - i reaches 0.  The closure is the released PLAIN proof's induction on a nat `fuel` with
   `Z.to_nat rem <= fuel` (lib/Prog/LLVMFuzzerTestOneInput.v:83-101 loop_ok and :303-307 knock_loop).

   THE SHAPE
     INV_L fuel carries 1 <= rem and Z.to_nat rem <= fuel; the three body states carry only the second.
     S3 : rt_from ss_T (INV_T fuel)  ->  rt_from ss_L (INV_L (S fuel))   (rem drops by 1, 2 or 3)
     S4 : rt_from ss_M (INV_M fuel)  ->  rt_from ss_T (INV_T fuel)
     S5 : rt_from ss_C (INV_C fuel)  ->  rt_from ss_M (INV_M fuel)
     S6 : rt_from ss_L (INV_L fuel)  ->  rt_from ss_C (INV_C fuel)       (the back edge re-establishes 1 <= rem
                                                                          at the head test 0x7f150; the two exits to
                                                                          0x7f2c4 are discharged inside S6 against
                                                                          ss_X)
   At fuel = 0 the loop head is unreachable: INV_L 0 asks for 1 <= rem and Z.to_nat rem <= 0 at once, so the
   goal follows by exfalso (the plain proof's `{ exfalso. lia. }` at :307).
   At fuel = S f the body is one pass and the induction hypothesis is the next pass.

   rt_L below takes the four segment lemmas as Section hypotheses, as in lib/A/APgMainL.v, so it is the induction
   alone.  rt_loop then discharges them with the four proved segments (lib/AU/APgMain3.v .. APgMain6.v) and S6's exit
   with S7 (a Theorem Labs lane's AU rt_X, lib/AU/APgMain7.v, stated over lib/AU/APgRt.v's context record), at knock's real
   post rt_post: what is left as premises are the two callee contracts the loop calls (a Theorem Labs lane's
   tknock_heard_specX / tknock_step_specX at the asan-ubsan entries, lib/A/APgCSpec.v) and the laws the segments and
   S7 use (lib/A/APgMainL.v rt_loop is the template).  This file adds no
   walk and no arithmetic of its own.  rule 24: no function proved. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep AWalkFw1 AWalkFw2 YCfm APgRt APgStates APgLoop0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgCSpec.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import APgMain7 APgMain3 APgMain4 APgMain5 APgMain6.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.

(* INV_L at fuel 0 is empty: 1 <= rem and Z.to_nat rem <= 0 cannot both hold. *)
Lemma INV_L_fuel_pos : forall (B : asyms) (MT : ameter_ops) (fuel : nat) cx E k acc ly3 S3 W3 ms3 md3,
INV_L B MT fuel cx E k acc ly3 S3 W3 ms3 md3 -> (1 <= fuel)%nat.
Proof.
intros B MT fuel cx E k acc ly3 S3 W3 ms3 md3 H. red in H.
destruct H as (_ & _ & _ & H).
repeat match goal with Hx : ex _ |- _ => destruct Hx as (? & Hx) end.
repeat match goal with Hx : _ /\ _ |- _ => destruct Hx as (? & Hx) end.
lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Variable POST : rtcx -> world tfibsegs -> config -> Prop.
(* S3 LOOP, 0x7f154-0x7f1e8 + 0x7f2a0-0x7f2c0 + 0x7f43c-0x7f444 -> ss_T  [lib/AU/APgMain3.v] *)
Hypothesis RS3 : forall fuel : nat,
rt_from B MT FP POST ss_T (INV_T B MT fuel) -> rt_from B MT FP POST ss_L (INV_L B MT (S fuel)).
(* S4 TAIL, 0x7f1ec-0x7f218 -> ss_M  [lib/AU/APgMain4.v] *)
Hypothesis RS4 : forall fuel : nat,
rt_from B MT FP POST ss_M (INV_M B MT fuel) -> rt_from B MT FP POST ss_T (INV_T B MT fuel).
(* S5 MID, 0x7f21c-0x7f26c -> ss_C  [lib/AU/APgMain5.v] *)
Hypothesis RS5 : forall fuel : nat,
rt_from B MT FP POST ss_C (INV_C B MT fuel) -> rt_from B MT FP POST ss_M (INV_M B MT fuel).
(* S6 CHECKS, 0x7f270-0x7f29c + the head test 0x7f150 -> ss_L (the back edge) or ss_X (the two exits)
   [lib/AU/APgMain6.v] *)
Hypothesis RS6 : forall fuel : nat,
rt_from B MT FP POST ss_L (INV_L B MT fuel) -> rt_from B MT FP POST ss_C (INV_C B MT fuel).

(* the loop, closed.  This is what S2 (the asan-ubsan twin of lib/A/APgMain2.v) consumes at 0x7f154, with
   fuel := Z.to_nat rem at the entry of the first pass. *)
Theorem rt_L : forall fuel : nat, rt_from B MT FP POST ss_L (INV_L B MT fuel).
Proof.
induction fuel as [|f IH].
- intros cx E k acc ly3 S3 W3 ms3 md3 HBASE HEE HJ3 Hfrs3 HMLE HINV HS.
  exfalso. pose proof (INV_L_fuel_pos B MT 0%nat cx E k acc ly3 S3 W3 ms3 md3 HINV) as Hf. lia.
- exact (RS3 f (RS4 f (RS5 f (RS6 f IH)))).
Qed.

End d.

Section w.
Variable B : asyms.
Variable MT : ameter_ops.
Variable FP : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis MTF : ameter_fs_laws MT.
(* the harness's footprint is empty, so the input bytes S3 reads are the entry's (PB_at_now) *)
Hypothesis FP0 : FP = [].
(* the two callees the loop calls, at the asan-ubsan entries (lib/AU/APgLoop0.v: heard 0x7f520, step 0x7f5b0) *)
Hypothesis TKHEARD : tknock_heard_specX (SK := SK) tfibsegs B MT A_reac_knock_heard.
Hypothesis TKSTEP : tknock_step_specX (SK := SK) tfibsegs B MT A_reac_knock_step.

(* the loop, closed and instantiated: every pass from 0x7f154, for any fuel, reaches knock's return *)
Theorem rt_loop : forall fuel : nat, rt_from B MT FP (rt_post B MT FP) ss_L (INV_L B MT fuel).
Proof.
(* rt_L is in this file's Section b, so its fx / rc / SK are still this section's variables, not arguments *)
apply (rt_L B MT FP (rt_post B MT FP)); intros f Hn.
- eapply (rt_S3 (SK := SK)); eassumption.
- eapply (rt_S4 (SK := SK)); eassumption.
- eapply (rt_S5 (SK := SK)); eassumption.
- eapply (rt_S6 (SK := SK)).
  all: first [ exact Hn | exact (rt_X (SK := SK) B MT FP MTL TL LAWS ML ASF FFL MTF) | eassumption ].
Qed.

End w.
End b.
