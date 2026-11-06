(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput
   (fuzz_knock.asan, sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118): THE LOOP CLOSURE.

   The loop head is 0x7f10c and the body is S3 LOOP -> S4 TAIL -> S5 MID -> S6 CHECKS, with the back edge
   `bnez s9, 0x7f10c` at 0x7f248.  This file closes it.

   WHY AN INDUCTION ON FUEL, AND NOT THE DONOR'S COUNTER
   The donor's harness loop is counted: the trip count sits in env slot 400 and the closure is an induction on
   that counter, which the body decrements by one (proofs/cgif/cgif_file_fuzzer/lib/A/ACfj.v:157-179 at
   c8557374ad2e, with A/ACfk.v:266 and A/ACfe.v:67 as its two users).  knock's loop has no counter: it runs while
   the input has bytes left, the body eats one, two or three of them, and it also leaves through `i > 4094`.  So
   this file REPLACES the donor's slot-400 induction by the released PLAIN proof's induction on a nat `fuel` with
   `Z.to_nat rem <= fuel` (lib/Prog/LLVMFuzzerTestOneInput.v:83-101 loop_ok and :303-307 knock_loop).

   THE SHAPE
     INV_L fuel carries 1 <= rem and Z.to_nat rem <= fuel; the three body states carry only the second.
     S3 : rt_from ss_T (INV_T fuel)  ->  rt_from ss_L (INV_L (S fuel))   (rem drops by 1, 2 or 3)
     S4 : rt_from ss_M (INV_M fuel)  ->  rt_from ss_T (INV_T fuel)
     S5 : rt_from ss_C (INV_C fuel)  ->  rt_from ss_M (INV_M fuel)
     S6 : rt_from ss_L (INV_L fuel)  ->  rt_from ss_C (INV_C fuel)       (the back edge re-establishes 1 <= rem
                                                                          from `bnez s9`; the two exits to 0x7f274
                                                                          are discharged inside S6 against ss_X)
   At fuel = 0 the loop head is unreachable: INV_L 0 asks for 1 <= rem and Z.to_nat rem <= 0 at once, so the
   goal follows by exfalso --- exactly the plain proof's `{ exfalso. lia. }` at :307.
   At fuel = S f the body is one pass and the induction hypothesis is the next pass.

   rt_L below takes the four segment lemmas as Section hypotheses, so it is the induction alone.  rt_loop then
   discharges them with the four proved segments (lib/A/APgMain3.v .. APgMain6.v) and S6's exit with S7
   (a Theorem Labs lane's rt_X, lib/A/APgMain7.v), at knock's real post rt_post: what is left as premises are the two callee
   contracts the loop calls (a Theorem Labs lane's tknock_heard_specX / tknock_step_specX at knock's entries, lib/A/APgCSpec.v)
   and the laws the segments and S7 use.  S2 (lib/A/APgMain2.v rt_H) consumes rt_loop.  This file adds no walk
   and no arithmetic of its own.  rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm APgRt APgLoop0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import APgCSpec APgMain7 APgMain3 APgMain4 APgMain5 APgMain6.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.

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
(* S3 LOOP, 0x7f10c-0x7f190 + 0x7f250-0x7f270 + 0x7f408-0x7f410 -> ss_T  [lib/A/APgMain3.v] *)
Hypothesis RS3 : forall fuel : nat,
rt_from B MT FP POST ss_T (INV_T B MT fuel) -> rt_from B MT FP POST ss_L (INV_L B MT (S fuel)).
(* S4 TAIL, 0x7f194-0x7f1c0 -> ss_M  [lib/A/APgMain4.v] *)
Hypothesis RS4 : forall fuel : nat,
rt_from B MT FP POST ss_M (INV_M B MT fuel) -> rt_from B MT FP POST ss_T (INV_T B MT fuel).
(* S5 MID, 0x7f1c4-0x7f218 -> ss_C  [lib/A/APgMain5.v] *)
Hypothesis RS5 : forall fuel : nat,
rt_from B MT FP POST ss_C (INV_C B MT fuel) -> rt_from B MT FP POST ss_M (INV_M B MT fuel).
(* S6 CHECKS, 0x7f21c-0x7f24c -> ss_L (the back edge) or ss_X (the two exits)  [lib/A/APgMain6.v] *)
Hypothesis RS6 : forall fuel : nat,
rt_from B MT FP POST ss_L (INV_L B MT fuel) -> rt_from B MT FP POST ss_C (INV_C B MT fuel).

(* the loop, closed.  This is what S2 (lib/A/APgMain2.v) consumes at 0x7f10c, with
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
(* the two callees the loop calls, at knock's concrete entries; APgLib discharges them with a Theorem Labs lane's walks *)
Hypothesis TKHEARD : tknock_heard_specX (SK := SK) tfibsegs B MT A_reac_knock_heard.
Hypothesis TKSTEP : tknock_step_specX (SK := SK) tfibsegs B MT A_reac_knock_step.

(* the loop, closed and instantiated: every pass from 0x7f10c, for any fuel, reaches knock's return *)
Theorem rt_loop : forall fuel : nat, rt_from B MT FP (rt_post B MT FP) ss_L (INV_L B MT fuel).
Proof.
(* rt_L is in this file's Section b, so its fx / rc / SK / ROB are still this section's variables, not arguments *)
apply (rt_L B MT FP (rt_post B MT FP)); intros f Hn.
- eapply (rt_S3 (SK := SK)); eassumption.
- eapply (rt_S4 (SK := SK)); eassumption.
- eapply (rt_S5 (SK := SK)); eassumption.
- eapply (rt_S6 (SK := SK)).
  all: first [ exact Hn | exact (rt_X (SK := SK) B MT FP MTL TL LAWS ML ASF FFL MTF) | eassumption ].
Qed.

End w.
End b.
