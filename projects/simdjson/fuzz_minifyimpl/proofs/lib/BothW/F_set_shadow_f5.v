(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AProto ABase F_memset.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition set_shadow_f5_entry : Z := 0x84a50.
Definition ASHF5 : Z := 245.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shf5_cells (m : amem) : Prop :=
     rw_cells bsegs m 0x173cf8 [C8 (Z_to_bv 64 0x175d20)]
  /\ rw_cells bsegs m 0x175d18 [C8 (Z_to_bv 64 0x165dd8); C8 (Z_to_bv 64 0x1661dc)].

Lemma shf5_cells_frame : forall m m' W,
  shf5_cells m -> munch W m m' -> wmono bsegs m m' -> Forall (fun iv => AIMG_HI <= fst iv) W -> shf5_cells m'.
Proof.
  intros m m' W [P1 P2] MU WM HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold AIMG_HI in *.
  split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition set_shadow_f5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) (repeat (Z_to_bv 8 ASHF5) (Z.to_nat (bv_unsigned a1)))].

Lemma set_shadow_f5_spec : forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (junk : list byte),
  shf5_cells m ->
  rw_cells bsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk] ->
  mem_inv bsegs m ->
  rng_aimg RNG -> rng RNG (bv_unsigned a0) (bv_unsigned a1) ->
  evtF bsegs RNG (set_shadow_f5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 set_shadow_f5_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros [GOTMS REAL] DST MI RIMG RD.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  unfold set_shadow_f5_entry.
  do 3 step.                                           (* [comment removed for export] *)
  do 2 zstep.                                          (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (memset_spec RNG ra sp gp tp _ _ _ s0 s1 a0 (Z_to_bv 64 ASHF5) a1); [exact DST | exact MI | exact RD]. }
  cbv beta. intros ms' PO. unfold memset_post in PO. unfold set_shadow_f5_post.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & DST').
  rewrite unsigned_lit in DST' by (unfold ASHF5; lia). change (ASHF5 mod 256) with ASHF5 in DST'.
  do 15 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact DST'].
Qed.
End CANSEC1.
