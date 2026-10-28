(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0HarnStmt U.S0TRDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnStmt OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0TRDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface.GlueEqv.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFix.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0GrowWalk.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
   (* [comment removed for export] *)
 Unset Lia Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac if_decide b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b; [cbv iota|
        symmetry; unfold bv_eqb, bv_ltu, bv_lts; cbn [negb]; rewrite ?unsigned_lit by lia;
        first [ reflexivity
              | apply (proj2 (Bool.negb_true_iff _)); first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; lia
              | apply (proj2 (Bool.negb_false_iff _)); first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; lia
              | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ] ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma growA : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cap : Z),
  (65536 <= cap < 2 ^ 26)%Z ->
  evt s0segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13628) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7
                                         s2 (Z_to_bv 64 cap) s4 (Z_to_bv 64 (2 * cap)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x29504) fc None m (seg_rom s0segs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 cap) s4 (Z_to_bv 64 cap) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13614) fc None m (seg_rom s0segs)).
Proof.
  intros until cap. intros Hcap.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  zstep.            (* [comment removed for export] *)
  rewrite (Z.shiftr_div_pow2 cap 26) by lia. replace (cap / 2 ^ 26)%Z with 0%Z by (symmetry; apply Z.div_small; lia).
  step. if_false.   (* [comment removed for export] *)
  zstep.            (* [comment removed for export] *)
  step. step.       (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 cap 1) by lia. replace (cap * 2 ^ 1)%Z with (2 * cap)%Z by lia.
  finish.
Qed.

(* [comment removed for export] *)
Lemma growR : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt s0segs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                                         s2 (Z_to_bv 64 67108864) s4 (Z_to_bv 64 67108864) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x137c8) fc None m (seg_rom s0segs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 67108864) s4 (Z_to_bv 64 67108864) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13614) fc None m (seg_rom s0segs)).
Proof.
  intros until m.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  zstep. change (67108864 ≫ 26)%Z with 1%Z.
  step. if_true.
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma growB : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r buf cap : Z),
  (0 < r < 2 ^ 64)%Z -> (0 < cap < 2 ^ 64)%Z ->
  evt s0segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13644) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 r) (Z_to_bv 64 r) (Z_to_bv 64 buf) (Z_to_bv 64 cap) a3 a4 a5 a6 a7
                                         s2 (Z_to_bv 64 cap) s4 s5 s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x306ac) fc None m (seg_rom s0segs))
      (MS (mkR (Z_to_bv 64 0x13628) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 cap) s4 s5 s6 (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13628) fc None m (seg_rom s0segs)).
Proof.
  intros until cap. intros Hr Hcap.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. if_decide false.   (* [comment removed for export] *)
  step.                    (* [comment removed for export] *)
  step. if_decide false.   (* [comment removed for export] *)
  do 4 step.               (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Lemma growC : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt s0segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1364c) sp gp tp t0 t1 t2 s0 s1 s7 a1 a2 a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x293c4) fc None m (seg_rom s0segs))
      (MS (mkR (Z_to_bv 64 0x13644) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13644) fc None m (seg_rom s0segs)).
Proof.
  intros until m.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. step. finish.
Qed.

(* [comment removed for export] *)
Lemma grow0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf cap : Z),
  (0 < buf < 2 ^ 64)%Z -> (0 < cap < 2 ^ 64)%Z ->
  evt s0segs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 buf) (Z_to_bv 64 0x345e0) a1 a2 a3 a4 a5 a6 a7
                                         s2 (Z_to_bv 64 0) s4 (Z_to_bv 64 cap) (Z_to_bv 64 0x340d9) (Z_to_bv 64 buf) s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x1364c) fc None m (seg_rom s0segs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 cap) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x135d4) fc None m (seg_rom s0segs)).
Proof.
  intros until cap. intros Hbuf Hcap.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. if_decide false.     (* [comment removed for export] *)
  step. step.                (* [comment removed for export] *)
  zstep. zstep.              (* [comment removed for export] *)
  try change (0x345e0 + -1287)%Z with 213209%Z. try change (214496 + -1287)%Z with 213209%Z.
  step. if_decide true.      (* [comment removed for export] *)
  step. step.                (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Definition cfgw (b0 b1 : byte) : Z := Z.lor ((bv_unsigned (sxb b1) ≪ 57 mod 18446744073709551616) ≫ 49) (bv_unsigned b0).
Definition cfg_hi (x1 : Z) : Z := (bv_unsigned (sxb (Z_to_bv 8 x1)) ≪ 57 mod 18446744073709551616) ≫ 49.
Fixpoint zlist (k : nat) (lo : Z) : list Z := match k with O => [] | S k' => lo :: zlist k' (lo + 1) end.
Lemma in_zlist_nat : forall k lo x, (lo <= x < lo + Z.of_nat k)%Z -> In x (zlist k lo).
Proof.
  induction k as [|k IH]; intros lo x Hx; [lia|]. cbn [zlist]. destruct (Z.eq_dec lo x) as [->|NE]; [left; reflexivity| right]. apply IH. lia.
Qed.
Lemma in_zlist : forall n lo x, (lo <= x < lo + n)%Z -> In x (zlist (Z.to_nat n) lo).
Proof. intros n lo x H. apply in_zlist_nat. rewrite Z2Nat.id by lia. exact H. Qed.
Definition CFGCHK (x1 : Z) : bool :=
  let h := cfg_hi x1 in forallb (fun x0 => Z.lor h x0 =? (x0 + 256 * x1) mod 32768)%Z (zlist (Z.to_nat 256) 0).
Lemma cfgchk_ok : forallb CFGCHK (zlist (Z.to_nat 256) 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cfgw_val : forall b0 b1, cfgw b0 b1 = ((bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768)%Z.
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256%Z in R0, R1.
  pose proof cfgchk_ok as K. rewrite forallb_forall in K. specialize (K (bv_unsigned b1) (in_zlist 256 0 (bv_unsigned b1) ltac:(lia))).
  unfold CFGCHK in K. cbv zeta in K. rewrite forallb_forall in K. specialize (K (bv_unsigned b0) (in_zlist 256 0 (bv_unsigned b0) ltac:(lia))).
  apply Z.eqb_eq in K. unfold cfg_hi in K.
  replace (Z_to_bv 8 (bv_unsigned b1)) with b1 in K by (apply bv_eq; rewrite Z_to_bv_small; [reflexivity| change (bv_modulus 8) with 256%Z; lia]).
  exact K.
Qed.

(* [comment removed for export] *)
Lemma hdr_walk : forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bufA L cfg : Z) (b0 b1 c0 c1 c2 c3 : byte),
  (65536 <= L < 2 ^ 26)%Z -> (0x66000 <= bufA)%Z -> (bufA + L <= 0x800000000000)%Z ->   (* [comment removed for export] *)
  ((bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768 = cfg)%Z ->
  rw_cells s0segs m bufA [C1 b0; C1 b1] ->
  rw_cells s0segs m (bufA + cfg + 2) [C1 c0; C1 c1; C1 c2; C1 c3] -> mem_inv s0segs m ->
  evt s0segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x136f4) sp gp tp t0 t1 t2 (Z_to_bv 64 (bufA + 2)) (Z_to_bv 64 bufA)
                                         (Z_to_bv 64 (bufA + 2)) (Z_to_bv 64 cfg) (Z_to_bv 64 (bufA + cfg + 6)) (Z_to_bv 64 (L - cfg + -6))
                                         (Z_to_bv 64 (bv_unsigned c3)) a5 a6 a7
                                         (Z_to_bv 64 cfg) (Z_to_bv 64 (bufA + cfg + 6)) (Z_to_bv 64 (L - cfg + -6)) (sxb b1)
                                         s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x13850) fc None m (seg_rom s0segs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 bufA) a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 L) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1367c) fc None m (seg_rom s0segs)).
Proof.
  intros until c3. intros HL HB1 HB2 Hcfg BUF PB MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  pose proof (Z.mod_pos_bound (bv_unsigned b0 + 256 * bv_unsigned b1) 32768 ltac:(lia)) as CB. rewrite Hcfg in CB.
  step. step. if_decide false.   (* [comment removed for export] *)
  zstep.   (* [comment removed for export] *)
  zstep.   (* [comment removed for export] *)
  zstep. zstep. zstep.  (* [comment removed for export] *)
  change (Z.lor ((bv_unsigned (sxb b1) ≪ 57 mod 18446744073709551616) ≫ 49) (bv_unsigned b0)) with (cfgw b0 b1).
  rewrite cfgw_val, Hcfg.
  zstep.                 (* [comment removed for export] *)
  step. if_decide false. (* [comment removed for export] *)
  zstep. zstep.          (* [comment removed for export] *)
  replace (Z_to_bv 64 (bufA + 2 + cfg)) with (Z_to_bv 64 (bufA + cfg + 2)) by (f_equal; lia).
  do 4 zstep.            (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  do 4 zstep.            (* [comment removed for export] *)
  zstep.                 (* [comment removed for export] *)
  step. step.            (* [comment removed for export] *)
  do 5 step.             (* [comment removed for export] *)
  finish.
Qed.
End S0GrowWalk.

Unset Lia Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac if_decide b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b; [cbv iota|
        symmetry; unfold bv_eqb, bv_ltu, bv_lts; cbn [negb]; rewrite ?unsigned_lit by lia;
        first [ reflexivity
              | apply (proj2 (Bool.negb_true_iff _)); first [apply Z.eqb_neq | apply Z.ltb_ge | apply Z.leb_gt]; lia
              | apply (proj2 (Bool.negb_false_iff _)); first [apply Z.eqb_eq | apply Z.ltb_lt | apply Z.leb_le]; lia
              | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ] ]
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition calls_of (cfglen b2 : Z) : Z := if (cfglen =? 0)%Z then 1 else (Z.land b2 3 + 1).

Ltac if_lit b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) => replace c with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac fixst :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => change (Z_to_le_bytes 8 z) with (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem.le8 (Z_to_bv 64 z))
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => change (Z_to_le_bytes 4 z) with (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem.le4 (Z_to_bv 64 z))
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem.le1 (Z_to_bv 64 ?z))) _) => change (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Mem.le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]
      | _ => idtac
      end; mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
Definition ax_list (p1 p2 : list byte) (slot head : Z) (nx f0 : word) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 p1; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 slot); CB 4 p2; C8 (Z_to_bv 64 head); C8 nx; C8 f0].

Definition atx_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spv : Z) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (p1 p2 : list byte) (nx : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [(spv - 48, spv); (0x64230, 0x64234); (0x64238, 0x64240); (0x64248, 0x64250); (0x64348, 0x64350)]%Z m m'
    /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ stk s0segs m' lo spv
    /\ rw_cells s0segs m' 0x64228 (ax_list p1 p2 1 0x64240 nx (Z_to_bv 64 0x2916c))
    /\ rw_cells s0segs m' 0x64348 [C8 (Z_to_bv 64 0x139a8)].

Lemma atx_reg : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (spv : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (nx f0 a0w : word),
  a0 = Z_to_bv 64 0x139a8 -> (spv < 2 ^ 64)%Z ->
  stk s0segs m lo spv -> (lo <= spv - 48)%Z -> (0x66000 <= lo)%Z ->
  rw_cells s0segs m 0x64228 (ax_list p1 p2 0 0 nx f0) -> rw_cells s0segs m 0x64348 [C8 a0w] ->
  rw_cells s0segs m 0x64473 [C1 (Z_to_bv 8 0)] ->
  mem_inv s0segs m ->
  evt s0segs (atx_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spv F fc lo p1 p2 nx m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x290a8) fc None m (seg_rom s0segs)).
Proof.
  intros until a0w. intros -> HS ST LO LOI AX A0 NL MI.
  unfold ax_list in AX.
  pose proof (munch_refl [(spv - 48, spv); (0x64230, 0x64234); (0x64238, 0x64240); (0x64248, 0x64250); (0x64348, 0x64350)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  carve_frame 48%nat ST.
  do 6 step.
  do 6 step.
  step. step. step. if_true.
  step.
  step. step. step. if_false.
  step. step. if_false.
  zstep. step. fixst.
  zstep. try rewrite (sx32_small (Z_to_bv 64 0)) by (vm_compute; reflexivity). zstep. step. if_true.
  do 6 zstep.
  step. fixst. step. fixst. step. fixst.
  step. step.
  zstep. try rewrite (sx32_small (Z_to_bv 64 0)) by (vm_compute; reflexivity). step. if_false. step.
  do 6 step.
  release_frame FR ST spv.
  step. step.
  unfold atx_post, ax_list. finish.
Qed.

(* [comment removed for export] *)
Definition trP_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 a0 a1 a2 a3 : word) (lo : Z) (p1 p2 : list byte) (nx : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk8,
    ms' = MS (mkR (Z_to_bv 64 0x138e4) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                 (* [comment removed for export] *) a3 a2
                 (* [comment removed for export] *) (Z_to_bv 64 0) xa1 xa2 xa3 a4 a5 a6 a7
                 (* [comment removed for export] *)
                 a1 a0 (Z_to_bv 64 0x440e0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13898) fc None m' (seg_rom s0segs)
    /\ munch [(bv_unsigned sp + -128, bv_unsigned sp); (0x440e0, 0x440e1); (0x64230, 0x64234); (0x64238, 0x64240); (0x64248, 0x64250); (0x64348, 0x64350)]%Z m m'
    /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ stk s0segs m' lo (bv_unsigned sp + -80)
    /\ rw_cells s0segs m' (bv_unsigned sp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]
    /\ rw_cells s0segs m' 0x440e0 [C1 (Z_to_bv 8 1)]
    /\ rw_cells s0segs m' 0x64228 (ax_list p1 p2 1 0x64240 nx (Z_to_bv 64 0x2916c))
    /\ rw_cells s0segs m' 0x64348 [C8 (Z_to_bv 64 0x139a8)].

Lemma trP : forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (p1 p2 : list byte) (nx f0 a0w : word),
  stk s0segs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 128)%Z -> (0x66000 <= lo)%Z ->
  mem_inv s0segs m ->
  rw_cells s0segs m 0x440e0 [C1 (Z_to_bv 8 0)] ->
  rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)] ->
  rw_cells s0segs m 0x64228 (ax_list p1 p2 0 0 nx f0) -> rw_cells s0segs m 0x64348 [C8 a0w] ->
  rw_cells s0segs m 0x64473 [C1 (Z_to_bv 8 0)] ->
  evt s0segs (trP_post sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 a0 a1 a2 a3 lo p1 p2 nx F fc m)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13850) fc None m (seg_rom s0segs)).
Proof.
  intros until a0w. intros ST LO LOI MI INI GOT AX A0 NL.
  unfold ax_list in AX. move INI at bottom.   (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (0x440e0, 0x440e1); (0x64230, 0x64234); (0x64238, 0x64240); (0x64248, 0x64250); (0x64348, 0x64350)]%Z m) as MU.
  pose proof (wmono_refl s0segs m) as WM.
  carve_frame 80%nat ST.
  do 17 step.              (* [comment removed for export] *)
  step. if_true.           (* [comment removed for export] *)
  step. step. fixst.   (* [comment removed for export] *)
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (atx_reg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp + -80)%Z F fc mm lo p1 p2 nx f0 a0w);
      first [ reflexivity | lia | eassumption ]
    | post_call s0segs mm ] end.
  step. if_true.
  step. step. step. if_true.
  unfold trP_post. finish. all: eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition trA_post (sp gp tp s0 s1 s2 s3 s6 s7 s8 s9 s10 s11 : word) (b2 : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR (Z_to_bv 64 0x138b4) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 (Z_to_bv 64 0x440e0) (Z_to_bv 64 (calls_of (bv_unsigned s2) b2)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x29504) fc None m (seg_rom s0segs).

Lemma trA : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b2 : Z),
  mem_inv s0segs m ->
  rw_cells s0segs m (bv_unsigned s3) [C1 (Z_to_bv 8 b2)] -> (0 <= b2 < 256)%Z ->
  (0 < bv_unsigned s0)%Z ->
  evt s0segs (trA_post sp gp tp s0 s1 s2 s3 s6 s7 s8 s9 s10 s11 b2 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x440e0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13898) fc None m (seg_rom s0segs)).
Proof.
  intros until b2. intros MI CFG Hb2 LEN.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. if_cases Hc; zify_cond Hc.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step. step. if_true. step. step.
    unfold trA_post, calls_of. rewrite Hc. cbn [Z.eqb]. finish.
  - (* [comment removed for export] *)
    do 3 zstep. step. if_false. step. step.
    unfold trA_post, calls_of. replace (bv_unsigned s2 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (bv_unsigned (Z_to_bv 8 b2)) with b2 by (symmetry; apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
    finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition trA0_post (ra sp gp tp s0 s2 s3 s8 s9 s10 s11 : word) (b2 : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 xa0 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0x440f0) xa0 xa1 xa2 xa3 a4 a5 a6 a7
                 (Z_to_bv 64 0) s3 (Z_to_bv 64 0x440e0) (Z_to_bv 64 (calls_of (bv_unsigned s2) b2)) (Z_to_bv 64 0) (Z_to_bv 64 (-2))
                 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x13908) fc None m (seg_rom s0segs).

Lemma trA0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b2 : Z),
  mem_inv s0segs m ->
  rw_cells s0segs m (bv_unsigned s3) [C1 (Z_to_bv 8 b2)] -> (0 <= b2 < 256)%Z ->
  bv_unsigned s0 = 0%Z ->
  evt s0segs (trA0_post ra sp gp tp s0 s2 s3 s8 s9 s10 s11 b2 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x440e0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13898) fc None m (seg_rom s0segs)).
Proof.
  intros until b2. intros MI CFG Hb2 LEN.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. step. if_false. do 4 zstep.
    unfold trA0_post, calls_of. rewrite Hc. cbn [Z.eqb]. finish.
  - do 3 zstep. step. if_true. do 4 zstep.
    unfold trA0_post, calls_of. replace (bv_unsigned s2 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    replace (bv_unsigned (Z_to_bv 8 b2)) with b2 by (symmetry; apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
    finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition final_status (s5v : word) (v : Z) : Z := if (2 ^ 63 <=? bv_unsigned s5v)%Z then 0 else v.

Definition trE_post (sp gp tp ms1 ms2 ms3 ms4 ms5 ms6 ms7 s8 s9 s10 s11 : word) (v : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR (Z_to_bv 64 0x1377c) sp gp tp t0 t1 t2
                 (Z_to_bv 64 (final_status ms5 v)) ms1 ms1 a1 a2 a3 a4 a5 a6 a7
                 ms2 ms3 ms4 ms5 ms6 ms7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x293c4) fc None m (seg_rom s0segs).

Lemma trE : forall (xra sp gp tp t0 t1 t2 xs0 xs1 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 xs7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 : word) (junk8 : list byte) (v : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  rw_cells s0segs m (bv_unsigned sp + -80) [CB 8 junk8; C8 ms7; C8 ms6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 ra0] ->
  ra0 = Z_to_bv 64 0x136f4 -> (0 <= v < 251)%Z ->
  mem_inv s0segs m ->
  evt s0segs (trE_post sp gp tp ms1 ms2 ms3 ms4 ms5 ms6 ms7 s8 s9 s10 s11 v F fc m)
      (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
               xs2 xs3 xs4 xs5 xs6 xs7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13954) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros FR -> Hv MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  do 11 step.               (* [comment removed for export] *)
  step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    do 6 step. if_true. step. step.
    unfold trE_post, final_status. replace (2 ^ 63 <=? bv_unsigned ms5)%Z with true by (symmetry; apply Z.leb_le; lia). finish.
  - (* [comment removed for export] *)
    do 4 step.
    unfold trE_post, final_status. replace (2 ^ 63 <=? bv_unsigned ms5)%Z with false by (symmetry; apply Z.leb_gt; lia). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition trB_post (sp gp tp s0 s1 r s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR (Z_to_bv 64 0x138c8) sp gp tp t0 t1 t2 s0 s1 r s1 s0 a3 a4 a5 a6 a7 r s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x306ac) fc None m (seg_rom s0segs).

Lemma trB : forall (sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned r <> 0%Z -> mem_inv s0segs m ->
  evt s0segs (trB_post sp gp tp s0 s1 r s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR (Z_to_bv 64 0x138b4) sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138b4) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros Hr MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. if_false. do 4 step. unfold trB_post. finish.
Qed.

(* [comment removed for export] *)
Definition trC_post (sp gp tp s0 s2 s3 s4 s5 s8 s9 s10 s11 ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13908) fc None m (seg_rom s0segs).

Lemma trC : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv s0segs m ->
  evt s0segs (trC_post sp gp tp s0 s2 s3 s4 s5 s8 s9 s10 s11 ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138c8) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. step. zstep. zstep. unfold trC_post. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition L1_post (sp gp tp len al ow s3 j s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m', ms' = MS (mkR (Z_to_bv 64 0x1391c) sp gp tp t0 t1 t2 len al al len a2 a3 a4 a5 a6 a7
                                       ow s3 (Z_to_bv 64 0x440e0) j s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 (hi_entry S0I)) fc None m' (seg_rom s0segs)
    /\ munch [(0x440e4, 0x440e5)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ rw_cells s0segs m' 0x440e4 [C1 (Z_to_bv 8 1)].

Lemma L1 : forall (ra sp gp tp t0 t1 t2 len al a0 a1 a2 a3 a4 a5 a6 a7 ow s3 j s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fv : byte),
  mem_inv s0segs m -> rw_cells s0segs m 0x440e4 [C1 fv] ->
  evt s0segs (L1_post sp gp tp len al ow s3 j s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 len al a0 a1 a2 a3 a4 a5 a6 a7 ow s3 (Z_to_bv 64 0x440e0) j s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13908) fc None m (seg_rom s0segs)).
Proof.
  intros until fv. intros MI FL.
  pose proof (munch_refl [(0x440e4, 0x440e5)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. step. fixst.
  do 3 step. unfold L1_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition L4_post (sp gp tp len al ow j s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m', ms' = MS (mkR (Z_to_bv 64 0x1392c) sp gp tp t0 t1 t2 len al (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                       ow (Z_to_bv 64 0) (Z_to_bv 64 0x440e0) j s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x139d8) fc None m' (seg_rom s0segs)
    /\ munch [(0x440e4, 0x440e5)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ rw_cells s0segs m' 0x440e4 [C1 (Z_to_bv 8 0)].

Lemma L4 : forall (ra sp gp tp t0 t1 t2 len al a1 a2 a3 a4 a5 a6 a7 ow s3 j s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fv : byte),
  mem_inv s0segs m -> rw_cells s0segs m 0x440e4 [C1 fv] ->
  evt s0segs (L4_post sp gp tp len al ow j s6 s7 s8 s9 s10 s11 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 len al (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 ow s3 (Z_to_bv 64 0x440e0) j s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1391c) fc None m (seg_rom s0segs)).
Proof.
  intros until fv. intros MI FL.
  pose proof (munch_refl [(0x440e4, 0x440e5)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
  step. step. fixst.
  step. step. unfold L4_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition L5loop_post (sp gp tp s0 s1 s2 s4 : word) (j : Z) (s6 s7 s8 s9 s10 s11 ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 (Z_to_bv 64 (j - 1)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x13908) fc None m (seg_rom s0segs).

Lemma L5loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j : Z)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 < j <= 4)%Z -> mem_inv s0segs m ->
  evt s0segs (L5loop_post sp gp tp s0 s1 s2 s4 j s6 (Z_to_bv 64 (-2)) s8 s9 s10 s11 ra a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 (Z_to_bv 64 j) s6 (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1392c) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros Hj MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  zstep. try rewrite swrap32_small by lia. step. if_lit true.
  zstep. rewrite swrap32_small by lia. step. if_decide true. unfold L5loop_post. apply evt_done. do 2 f_equal. all: try reflexivity. all: f_equal; lia.
Qed.

Definition L5last_post (sp gp tp s0 s1 s2 s4 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR (Z_to_bv 64 0x13948) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x293c4) fc None m (seg_rom s0segs).

Lemma L5last : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv s0segs m ->
  evt s0segs (L5last_post sp gp tp s0 s1 s2 s4 s6 (Z_to_bv 64 (-2)) s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 (Z_to_bv 64 1) s6 (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1392c) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  zstep. try rewrite swrap32_small by lia. step. if_lit true.
  zstep. change (bv_swrap 32 (1 + -1)) with 0%Z. step. if_false. step. step. unfold L5last_post. apply evt_done. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma L6 : forall (sp gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 : word) (junk8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  rw_cells s0segs m (bv_unsigned sp + -80) [CB 8 junk8; C8 ms7; C8 ms6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 ra0] ->
  ra0 = Z_to_bv 64 0x136f4 ->
  mem_inv s0segs m ->
  evt s0segs (trE_post sp gp tp ms1 ms2 ms3 ms4 ms5 ms6 ms7 s8 s9 s10 s11 0 F fc m)
      (MS (mkR (Z_to_bv 64 0x13948) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
               xs2 xs3 xs4 xs5 (Z_to_bv 64 0) xs7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13948) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros FR Hra MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  zstep. zstep. zstep. eapply trE with (v := 0%Z); [exact FR | exact Hra | lia | exact MI].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition L7_post (sp gp tp st fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR (Z_to_bv 64 0x28c4c) (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 fs0 fs1 st a1 a2 a3 a4 a5 a6 a7
                 fs2 fs3 fs4 fs5 fs6 fs7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x291c0) fc None m (seg_rom s0segs).

(* [comment removed for export] *)
Lemma L7 : forall (ra sp gp tp t0 t1 t2 st s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 : word) (junk8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  rw_cells s0segs m (bv_unsigned sp) [CB 8 junk8; C8 fs7; C8 fs6; C8 fs5; C8 fs4; C8 fs3; C8 fs2; C8 fs1; C8 fs0; C8 (Z_to_bv 64 0x28c48)] ->
  mem_inv s0segs m ->
  evt s0segs (L7_post sp gp tp st fs0 fs1 fs2 fs3 fs4 fs5 fs6 fs7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 st s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1377c) fc None m (seg_rom s0segs)).
Proof.
  intros until m. intros FR MI. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
  do 12 step.    (* [comment removed for export] *)
  step.          (* [comment removed for export] *)
  unfold L7_post. finish.
Qed.
