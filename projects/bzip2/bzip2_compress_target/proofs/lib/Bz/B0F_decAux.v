(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 BzDU4 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV B0F_decRet.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decRet.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

(* [comment removed for export] *)
Lemma zb8_clear256_snoc : forall a k, (0 <= k < 256)%Z ->
  zb8 (zset (clear256 (Z.to_nat k) 0 a) k 0) 256 = zb8 (clear256 (Z.to_nat (k + 1)) 0 a) 256.
Proof.
  intros a k Hk. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (Z.to_nat 256)) as [Hn|Hn].
  - replace n with (Z.to_nat (Z.of_nat n)) by lia. rewrite !zb8_nth by lia. f_equal. f_equal.
    rewrite zget_zset, !zget_clear256.
    destruct (Z.eqb_spec (Z.of_nat n) k) as [E|NE];
    destruct (Z.leb_spec 0 (Z.of_nat n)); destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat k)));
    destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat (k + 1)))); cbn [andb]; try reflexivity; try lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite zb8_length_nat; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma makeMaps_d_pair : forall d,
  makeMaps_d d = d_set_nInUse (d_set_s2u d (fst (mkmaps 256 0 (d_inUse d) (d_s2u d) 0))) (snd (mkmaps 256 0 (d_inUse d) (d_s2u d) 0)).
Proof. intros d. unfold makeMaps_d. destruct (mkmaps 256 0 (d_inUse d) (d_s2u d) 0). reflexivity. Qed.
Lemma mkmaps_n_bound : forall n i inUse s2u n0, (n0 <= snd (mkmaps n i inUse s2u n0) <= n0 + Z.of_nat n)%Z.
Proof.
  induction n as [|n IH]; intros i inUse s2u n0; cbn [mkmaps snd]; [lia|].
  destruct (negb (zget inUse i =? 0)%Z).
  - pose proof (IH (i + 1)%Z inUse (zset s2u n0 i) (n0 + 1)%Z). lia.
  - pose proof (IH (i + 1)%Z inUse s2u n0). lia.
Qed.
Lemma mkmaps_s2u_byte : forall n i inUse s2u n0, (0 <= i)%Z -> (i + Z.of_nat n <= 256)%Z -> (forall k, (0 <= zget s2u k < 256)%Z) ->
  forall k, (0 <= zget (fst (mkmaps n i inUse s2u n0)) k < 256)%Z.
Proof.
  induction n as [|n IH]; intros i inUse s2u n0 Hi Hn HB k; cbn [mkmaps fst]; [apply HB|].
  destruct (negb (zget inUse i =? 0)%Z).
  - apply IH; [lia | lia |]. intros j. rewrite zget_zset. destruct (Z.eqb_spec j n0); [lia| apply HB].
  - apply IH; [lia | lia | exact HB].
Qed.
(* [comment removed for export] *)
Lemma K_HMK_ret : forall F L d s a n, makeMaps_d d = d_set_nInUse (d_set_s2u d a) n ->
  K_HMK F L d s = K_L4M F L (d_set_nInUse (d_set_s2u d a) n) s 256.
Proof. intros F L d s a n E. unfold K_HMK. rewrite E, K_L4M_exit. reflexivity. Qed.

(* [comment removed for export] *)
Lemma zw32_clear256_snoc : forall a k, (0 <= k < 256)%Z ->
  zw32 (zset (clear256 (Z.to_nat k) 0 a) k 0) 256 = zw32 (clear256 (Z.to_nat (k + 1)) 0 a) 256.
Proof.
  intros a k Hk. apply nth_error_ext. intros n.
  destruct (Nat.lt_ge_cases n (Z.to_nat 256)) as [Hn|Hn].
  - replace n with (Z.to_nat (Z.of_nat n)) by lia. rewrite !zw32_nth by lia. f_equal. f_equal.
    rewrite zget_zset, !zget_clear256.
    destruct (Z.eqb_spec (Z.of_nat n) k) as [E|NE];
    destruct (Z.leb_spec 0 (Z.of_nat n)); destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat k)));
    destruct (Z.ltb_spec (Z.of_nat n) (0 + Z.of_nat (Z.to_nat (k + 1)))); cbn [andb]; try reflexivity; try lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia).
    rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.
