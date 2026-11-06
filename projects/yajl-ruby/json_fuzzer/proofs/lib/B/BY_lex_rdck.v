(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rdck_tac :=
  intros;
  lazymatch goal with
  | BS : u8arr _ _ _ ?shb, E : ?shb = blk_shadow ?On, PL : pol _ _ _, HE : ?A + 1 <= _ + ?On' |- evtA _ _ _ (MS _ _ _ _ _ ?m _) =>
      unfold pol in PL;
      let L := fresh "BSlen" in pose proof (blk_shadow_length On ltac:(lia)) as L; rewrite <- E in L;
      pose proof (munch_refl ([] : list (Z * Z)) m) as MU; pose proof (wmono_refl bsegs m) as WM;
      shadow_cases BS A 1;
      [ apply evtA_done; eexists _, _; reflexivity
      | shadow_slow; apply evtA_done; eexists _, _; reflexivity ]
  end.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rdck_109c88 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 537196) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 537180) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_109dc4 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 537584) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 537568) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_109eb0 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 537888) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 537872) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_109fe4 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 538264) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 538248) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10a0c4 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 538556) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 538540) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10a430 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 539512) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 539496) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10a798 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 540556) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 540540) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10aa38 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 541364) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 541348) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10abb4 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 541812) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 541796) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10abe4 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a2v a3v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 x' y' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 541876) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2v a3v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 541860) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10ad9c : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542432) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542416) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10ae80 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542728) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542712) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10ae9c : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542752) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542736) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10af28 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542904) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 542888) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b038 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 543240) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 543224) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b138 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 543564) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 543548) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b224 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 543868) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 543852) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b30c : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 544164) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 544148) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b354 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 544256) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 544240) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b43c : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 544552) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 544536) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10b7e8 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 545540) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 545524) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10bbb4 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 546644) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 546628) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10bdb0 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 546948) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 546932) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_b858f0 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 547104) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 547088) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_b85e10 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 548416) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 548400) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

Lemma rdck_10c078 : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a1v a2v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (E SB OA On : Z) (shb : list byte),
  u8arr bsegs m (SB + OA / 8) shb -> shb = blk_shadow On -> OA mod 8 = 0 -> 0 <= OA -> OA <= E -> E + 1 <= OA + On -> 0 <= SB -> SB + (OA + On) / 8 + 1 < 2^64 -> E < 2^64 ->
  pol P (SB + OA / 8) (SB + OA / 8 + (On + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (x' y' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x' y' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 548700) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1v a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 SB) s11 t3 t4 t5 t6) F (Z_to_bv 64 548684) fc None m (seg_rom bsegs)).
Proof. aceil. rdck_tac. Qed.

End RC__1.
