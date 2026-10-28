(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_I ASlot_W13 ASlot_W14.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMallocKit_A2 RMalloc_fp RF_enframe.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_ntf_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RMallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.
From Stdlib Require Lia. 
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RMalloc_fp. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_malloc_join. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RASlot_W4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RASlot_W14.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_fast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_entry OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_enframe OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_AB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W0.ASlot_W3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W14.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_get_meta OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp.RMallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_A2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMalloc_fp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_malloc_join.RAllocSlot_iface OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_I OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RMallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.RASlot_W2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RASlot_W4.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
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
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sx32_congr (a : word) (b : Z) : bv_unsigned a mod 2^32 = b mod 2^32 -> sx32 a = wz (sxv b).
Proof.
  intros E. unfold sx32, wz, sxv. apply Z_to_bv_eqm. rewrite Z.mod_mod by lia.
  f_equal. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  rewrite <- (Zplus_mod_idemp_l (bv_unsigned a)), E, Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_mod32_pred_sxv y : bv_unsigned (Z_to_bv 64 (bv_unsigned (wz (sxv y)) + -1)) mod 2^32 = (y - 1) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (wz_unsigned (sxv y)) by (apply sxv_range).
  rewrite (mod_mod_pow2 _ 32 64) by lia.
  rewrite <- Zplus_mod_idemp_l, sxv_mod32, Zplus_mod_idemp_l. f_equal. 
Qed.

(* [comment removed for export] *)
Lemma unsigned_mod32_swrap_add_not a b :
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 a + Z.lxor (bv_unsigned (wz (sxv b))) 18446744073709551615)) mod 2^32 = (a - 1 - b) mod 2^32.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite (mod_mod_pow2 _ 32 64) by lia.
  pose proof (sxv_range b) as RB.
  rewrite zb_lxor_ones by (rewrite wz_unsigned by lia; lia). rewrite (wz_unsigned (sxv b)) by lia.
  replace (bv_swrap 32 a + (18446744073709551615 - sxv b)) with ((bv_swrap 32 a - sxv b - 1) + 2^32 * 2^32) by lia.
  rewrite Z.mod_add by lia.
  unfold sxv. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
  set (x := (a + 2^31) mod 2^32). set (y := ((b + 2^31) mod 2^32 - 2^31) mod 2^64).
  assert (Hx : x = (a + 2^31) mod 2^32) by reflexivity. assert (Hy : y = ((b + 2^31) mod 2^32 - 2^31) mod 2^64) by reflexivity.
  clearbody x y. Z.div_mod_to_equations. nia.
Qed.
Lemma land224_m32 x : 0 <= x < 256 -> Z.land x 224 = Z.land x 18446744073709551584.
Proof.
  intros Hx. rewrite <- (Z.mod_small x 256) by lia. change 256 with (2^8). rewrite <- Z.land_ones by lia.
  rewrite <- !Z.land_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr) (r : region).
Let G := conc stT mt.
Let P := conc stT p.
Let AV := mask_upto ai.
Let FR := mask_upto (cnt - 1) - mask_upto ai.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml < 2^52.
Hypothesis MST : meta_slot stT mt.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis Hr : (s_regions stT) !! (fst p) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis P0 : 0 <= snd p.
Hypothesis P16 : snd p mod 16 = 0.
Hypothesis PEND : snd p + 16 <= round_up_pg (r_len r).
Hypothesis GNONE : (s_groups stT) !! p = None.
Hypothesis NOGRP : forall b' gh, (s_groups stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b'.
Hypothesis OLD12 : forall o v t, snd p <= o < snd p + 12 ->
  (r_cells (get_shadow stT (fst p))) !! o = Some (v, t) -> (t < s_tick stT)%N.
Hypothesis UR : 0 <= usage stT sc < 2^60.
Hypothesis ACT : active stT sc = None.
Hypothesis TK : ticks_ok stT.

(* [comment removed for export] *)
Definition rtailW : list (Z * Z) :=
  [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8); (G, G + 40); (P, P + 9); (RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z.

(* [comment removed for export] *)
Lemma rtail_walk :
  forall (ra sp gp tp t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) F fc mC,
  rmrep stT mC -> mem_inv rsegs mC ->
  evt rsegs (fun ms' => exists (s0' a1' a2' a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0' (Z_to_bv 64 G) (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7
                   s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2aa64) fc None m' (seg_rom rsegs)
      /\ munch rtailW mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
      /\ rmrep (stFin stT sc cnt ai ml mt p) m' /\ ticks_ok (stFin stT sc cnt ai ml mt p))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 P) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 ai) a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 (RCTX + 80 + 8 * sc)) s6 (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a90c) fc None mC (seg_rom rsegs)).
Proof.
  pose proof UR as KEEP__; clear KEEP__.   (* [comment removed for export] *)
  intros until mC. intros MR MI.
  pose proof (munch_refl rtailW mC) as MU. pose proof (wmono_refl rsegs mC) as WM. unfold rtailW in MU.
  cps_pose (rmeta_slot_bounds stT mC mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  cps_pose (rregion_facts stT mC (fst p) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). bz_ceil.
  assert (CP : P = r_base r + snd p) by (unfold P; apply conc_region'; exact Hr).
  cps_pose (AV_FR_range stT cnt ai mt p CNT AI P0) as (AVR & FRR & AV1R). fold AV in AVR, AV1R. fold AV FR in FRR.
  (* [comment removed for export] *)
  destruct (rmrep_hdr_havoc stT mC p MR TK) as [MRA TKA]. fold (stA stT p) in MRA, TKA.
  bz_ceil; unfold RCTX, RMLOCK in *.
  (* [comment removed for export] *)
  pose proof (rmrep_usage_read (stA stT p) mC sc (wa (410856 + 464 + 8 * sc)) MRA SC eq_refl) as RDU.
  change (usage (stA stT p) sc) with (usage stT sc) in RDU.
  replace (wa (410856 + 464 + 8 * sc)) with (Z_to_bv 64 (410848 + 8 * sc + 472)) in RDU by (unfold wa; f_equal; lia).
  step. clear RDU.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned (usage stT sc)), ?(unsigned_lit cnt) by lia. step.
  (* [comment removed for export] *)
  cps_pose MRA as (_ & (_ & _ & USG & _) & _).
  pose proof (u64arr_store_ok rsegs _ _ (usages (stA stT p)) sc (wa (410856 + 464 + 8 * sc)) USG
                ltac:(rewrite usages_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK. clear USG.
  replace (wa (410856 + 464 + 8 * sc)) with (Z_to_bv 64 (410848 + 8 * sc + 472)) in SOK by (unfold wa; f_equal; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_usage (stA stT p) mX sc (usage stT sc + cnt) MRA SC) as MRB; unfold RCTX in MRB; fold (stB stT sc cnt p) in MRB end.
  rraw_store_finish0 (410856 + 464 + 8 * sc) (le8 (wz (usage stT sc + cnt))) MU WM SOK.
  assert (TKB : ticks_ok (stB stT sc cnt p)) by exact TKA.
  assert (MSTB : meta_slot (stB stT sc cnt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRA TKA.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia. rewrite ASlot_W14.sllw2_word by lia.
  step.
  set (v3 := Z_to_bv 64 (bv_unsigned (wz (sxv (2 ^ (ai + 1)))) + -1)).
  rmchunk MRB MSTB CH. change (conc (stB stT sc cnt p) mt) with G in CH. change (get_meta_rec (stB stT sc cnt p) mt) with (get_meta_rec stT mt) in CH.
  rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
  replace (meta_word _) with (4096 * ml) in CH by (unfold meta_word; cbn; lia).
  rmeta_open G MUa WMa.
  (* [comment removed for export] *)
  step. step.
  assert (V3 : bv_unsigned v3 mod 2^32 = AV mod 2^32).
  { subst v3. rewrite unsigned_mod32_pred_sxv. unfold AV, mask_upto. reflexivity. }
  rewrite (sx32_congr v3 AV V3).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia. rewrite ASlot_W14.sllw2_word by lia. replace (cnt - 1 + 1) with cnt by lia.
  step. step.
  set (v4 := Z_to_bv 64 (bv_swrap 32 (2 ^ cnt) + Z.lxor (bv_unsigned (wz (sxv AV))) 18446744073709551615)).
  assert (V4 : bv_unsigned v4 mod 2^32 = FR mod 2^32).
  { subst v4. rewrite unsigned_mod32_swrap_add_not. unfold FR, AV, mask_upto. replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
  (* [comment removed for export] *)
  step. step.
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRC : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRB| exact MSTB| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
      unfold meta_cells, recA, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes app];
      change (conc (stB stT sc cnt p) p) with P; unfold wz at 3 4;
      rewrite (le4_congr v3 (Z_to_bv 64 AV)) by (rewrite V3, unsigned_lit by lia; reflexivity);
      rewrite (le4_congr v4 (Z_to_bv 64 FR)) by (rewrite V4, unsigned_lit by lia; reflexivity);
      replace (meta_word _) with (4096 * ml) by (unfold meta_word; cbn; lia); reflexivity
    | clear MUa WMa; rename H into CH1 ] end.
  assert (TKC : ticks_ok (stC stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stB stT sc cnt p) mt (fun _ => recA cnt ai ml p) TKB)).
  assert (MSTC : meta_slot (stC stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear MRB TKB MSTB.
  (* [comment removed for export] *)
  cps_pose MRC as (WFC & _ & _ & _ & _ & SHC). cps_pose WFC as (_ & _ & DJ & _ & WG).
  destruct (SHC (fst p) r Hr Hk) as [WR _]. clear SHC.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    destruct (rwr_at_bytes_exist mX P 9 ltac:(eapply wr_at_sub; [exact WR| (first [ solve [clear - P0 PEND RI1 RI2 CP; lia] | lia ])| (first [ solve [clear - P0 PEND RI1 RI2 CP; lia] | lia ])]) ltac:((first [ solve [clear - P0 PEND RI1 RI2 CP; lia] | lia ])) ltac:((first [ solve [clear - P0 PEND RI1 RI2 CP; lia] | lia ]))) as (hb & LHB & HB) end.
  destruct hb as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|? ?]]]]]]]]]]; try (cbn in LHB; discriminate).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HDR : rw_cells rsegs mX P [CB 8 [y0; y1; y2; y3; y4; y5; y6; y7]; C1 y8]);
    [ apply rw_cells_of_bytes; [cbn; repeat split; reflexivity| exact HB| cbn; eapply wr_at_sub; [exact WR| lia| lia]]
    | clear HB LHB ] end.
  cps_pose (rmeta_chunk_facts (stC stT sc cnt ai ml mt p) _ mt MRC MSTC) as (_ & _ & _ & _ & _ & GRG & _).
  pose proof (GRG (fst p) r Hr Hk) as GX. change (conc (stC stT sc cnt ai ml mt p) mt) with G in GX. clear GRG.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(P, P + 9)]%Z mX) as MUb; pose proof (wmono_refl rsegs mX) as WMb end.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step.
  pose proof (byte_range y8) as Y8.
  step. unfold zxb.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit ai) by lia.
  replace (Z.land ai 31) with ai by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (cnt - 1)) by lia.
  replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  step. rewrite ?(unsigned_lit (bv_unsigned y8)) by lia.
  step.
  pose proof (land_upper (bv_unsigned y8) 224 ltac:(lia) ltac:(lia)) as L8R.
  rewrite ?(unsigned_lit (Z.land (bv_unsigned y8) 224)), ?(unsigned_lit ai) by lia.
  rewrite (land224_m32 (bv_unsigned y8)) by lia.
  pose proof (hdr_byte_facts (bv_unsigned y8) ai Y8 ltac:(lia)) as [W8R W8L].
  (* [comment removed for export] *)
  set (nbv := Z.lor (Z.land (bv_unsigned y8) 18446744073709551584) ai) in *.
  step. rewrite (le1_mod nbv). mem_after_store. rewrite (Z.mod_small nbv 256) in * by lia.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX P _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    rename H into HDR2;
    assert (MRC2 : rmrep (stC stT sc cnt ai ml mt p) mX);
    [ eapply (rmrep_transport_unowned _ _ _ _ MRC MUb WMb)
    | assert (MRD : rmrep (stD stT sc cnt ai ml mt p) mX);
      [ eapply (rmrep_put_group_new (stC stT sc cnt ai ml mt p) mX p mt ai r (b8 nbv) MRC2 GNONE Hr Hk P0 PEND P16);
        [ change (conc (stC stT sc cnt ai ml mt p) p) with P; unfold pw, wz; cbn [oconc]; change (conc (stC stT sc cnt ai ml mt p) mt) with G; exact HDR2
        | rewrite b8_unsigned by lia; rewrite W8L; symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity ]
      | ] ] end.
  { (* [comment removed for export] *)
    intros lo' hi' a [E|[]] Ha. inversion E; subst lo' hi'. intros RF.
    pose proof (lr_lo_group r Hk) as LRr. specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
    destruct RF as [X1|[X2|[X3|[X4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[X5|X6]]]]]]]].
    - unfold RCTX in X1. first [ solve [clear - P0 PEND RI2 CP Ha X1; lia] | lia ].
    - unfold RMLOCK in X2. first [ solve [clear - P0 PEND RI2 CP Ha X2; lia] | lia ].
    - unfold RNEED_LOCKS in X3. lia.
    - unfold RPAGE_SIZE in X4. first [ solve [clear - P0 PEND RI2 CP Ha X4; lia] | lia ].
    - change (s_areas (stC stT sc cnt ai ml mt p)) with (s_areas stT) in Hak. change (conc (stC stT sc cnt ai ml mt p) ak) with (conc stT ak) in Rak.
      cps_destruct (rarea_conc stT ak ar WFC Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst p) by (intros EQ; rewrite EQ, Hr in Hra; injection Hra as E'; apply NK; rewrite <- E'; exact Hk).
      pose proof (rarea_lr_lo stT ak ar rga WFC Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; lia.
    - change (s_groups (stC stT sc cnt ai ml mt p)) with (s_groups stT) in Hb. change (conc (stC stT sc cnt ai ml mt p) b) with (conc stT b) in Rb.
      cps_destruct (rgroup_conc stT b gh WFC Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b) (fst p)) as [EQ|NE].
      + rewrite EQ, Hr in Hrb. inversion Hrb; subst rb. destruct (NOGRP b gh Hb EQ); lia.
      + pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE) as [D|D]; lia.
    - change (s_regions (stC stT sc cnt ai ml mt p)) with (s_regions stT) in Hq. change (get_shadow (stC stT sc cnt ai ml mt p) q) with (get_shadow (hdr_havoc p stT) q) in Cq.
      destruct (N.eq_dec q (fst p)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (cell_read_hdr_havoc_old stT p (a - r_base r - snd p) P16 ltac:(lia)
                    ltac:(intros v' t' Hc; eapply (OLD12 (snd p + (a - r_base r - snd p))); [lia| exact Hc])) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; lia.
    - unfold RGOT_SSP in X5. first [ solve [clear - P0 PEND RI2 CP Ha X5; lia] | lia ].
    - unfold RSSP_GUARD in X6. first [ solve [clear - P0 PEND RI2 CP Ha X6; lia] | lia ]. }
  clear MRC MRC2 MUb WMb HDR2.
  assert (TKD : ticks_ok (stD stT sc cnt ai ml mt p)) by exact TKC.
  assert (MSTD : meta_slot (stD stT sc cnt ai ml mt p) mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  clear TKC MSTC.
  (* [comment removed for export] *)
  cps_pose MRD as (_ & (_ & ACTS & _) & _). pose proof (actives_length (stD stT sc cnt ai ml mt p)) as LACT. unfold RCTX in ACTS.
  rmchunk MRD MSTD CH.
  change (get_meta_rec (stD stT sc cnt ai ml mt p) mt) with (get_meta_rec (put_meta mt (recA cnt ai ml p) (stB stT sc cnt p)) mt) in CH. rewrite get_meta_rec_put_same in CH.
  unfold recA in CH. cbn [m_prev m_next m_mem m_avail m_freed] in CH. unfold pw in CH. cbn [oconc] in CH.
  change (conc (stD stT sc cnt ai ml mt p) mt) with G in CH. change (conc (stD stT sc cnt ai ml mt p) p) with P in CH. unfold wz in CH.
  set (W := meta_word _) in CH. assert (EW : W = 4096 * ml) by (subst W; unfold meta_word; cbn; lia). clearbody W.
  rmeta_open G MUc WMc.
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (unsigned_lit sc), Z.shiftl_mul_pow2, (unsigned_lit (sc * 2 ^ 58)), Z.shiftr_div_pow2 by lia.
  replace (sc * 2 ^ 58 / 2 ^ 52) with (sc * 2 ^ 6) by (change (2 ^ 58) with (2 ^ 6 * 2 ^ 52); rewrite Z.mul_assoc, Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit W), EW, land_pg_mask by lia.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6)), ?(unsigned_lit (cnt - 1)) by lia. rewrite (lor_shl_small sc 6 (cnt - 1)) by lia.
  step. rewrite ?(unsigned_lit (sc * 2 ^ 6 + (cnt - 1))), ?(unsigned_lit (4096 * ml)) by lia.
  replace (4096 * ml) with (ml * 2 ^ 12) by lia. rewrite (lor_small_shl ml 12 (sc * 2 ^ 6 + (cnt - 1))) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. step. step. step.
  rewrite ?(unsigned_lit (mask_upto ai)) by lia.
  (* [comment removed for export] *)
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_read rsegs mX (410856 + 80) (actives (stD stT sc cnt ai ml mt p)) sc (pw (stD stT sc cnt ai ml mt p) (active (stD stT sc cnt ai ml mt p) sc)) (wa (410856 + 80 + 8 * sc)) H
                  (actives_nth (stD stT sc cnt ai ml mt p) sc SC) ltac:(lia) eq_refl) as RDA end.
  change (active (stD stT sc cnt ai ml mt p) sc) with (active stT sc) in RDA. rewrite ACT in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA.
  replace (wa (410856 + 80 + 8 * sc)) with (Z_to_bv 64 (410936 + 8 * sc + 0)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. step. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRE : rmrep (stE stT sc cnt ai ml mt p) mX);
    [ eapply rmrep_put_meta_frame; [exact MRD| exact MSTD| exact MUc| exact WMc|];
      eapply rw_cells_congr; [| | | exact H]
    | clear MUc WMc; rename H into CH3 ] end.
  { unfold meta_cells, recF, pw. cbn [m_prev m_next m_mem m_avail m_freed oconc cells_bytes cbytes].
    change (conc (stD stT sc cnt ai ml mt p) mt) with G. change (conc (stD stT sc cnt ai ml mt p) p) with P.
    unfold wz. rewrite !app_nil_r.
    rewrite (le4_congr (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (mask_upto ai))) + -1)) (Z_to_bv 64 (AV - 1))).
    2:{ rewrite (unsigned_lit (mask_upto ai)), Z_to_bv_unsigned, (unsigned_lit (AV - 1)) by lia. unfold bv_wrap. change (bv_modulus 64) with (2^64).
        rewrite (mod_mod_pow2 _ 32 64) by lia. unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
        fold AV. Z.div_mod_to_equations. lia. }
    do 6 f_equal. unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. f_equal. lia. }
  { reflexivity. }
  { cbn. tauto_fast. }
  assert (TKE : ticks_ok (stE stT sc cnt ai ml mt p)) by (exact (ticks_ok_upd_meta (stD stT sc cnt ai ml mt p) mt (fun _ => recF sc cnt ai ml mt p) TKD)).
  clear MRD TKD MSTD.
  (* [comment removed for export] *)
  clear CH3.
  lazymatch goal with H : u64arr rsegs ?mX _ (actives (stD stT sc cnt ai ml mt p)) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (u64arr_store_ok rsegs _ _ (actives (stD stT sc cnt ai ml mt p)) sc (wa (410856 + 80 + 8 * sc)) H
                  ltac:(rewrite actives_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK; clear H end.
  replace (wa (410856 + 80 + 8 * sc)) with (Z_to_bv 64 (410936 + 8 * sc + 0)) in SOK by (unfold wa; f_equal; lia).
  st1.
  replace (Z_to_bv 64 (410936 + 8 * sc + 0)) with (Z_to_bv 64 (410936 + 8 * sc)) in SOK by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active (stE stT sc cnt ai ml mt p) mX sc (Some mt) MRE SC) as MRF; unfold RCTX in MRF; fold (stFin stT sc cnt ai ml mt p) in MRF end.
  unfold pw in MRF. cbn [oconc] in MRF. change (conc (stE stT sc cnt ai ml mt p) mt) with G in MRF.
  rraw_store_finish0 (410856 + 80 + 8 * sc) (le8 (wz G)) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MRF| exact TKE].
Qed.
End TAIL.

End ACeilS1.
End RASlot_W14.

Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
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
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

(* [comment removed for export] *)
Lemma rnenf_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
  0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv rsegs m1 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x2a614) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (RSIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x2a614) fc None m' (seg_rom rsegs)
      /\ munch [(P - 3, P)]%Z m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ rmrep (enf0_st st g b idx) m' /\ ticks_ok (enf0_st st g b idx))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a5e8) fc None m1 (seg_rom rsegs)).
Proof.
  intros until fc. intros CTR MI.
  cps_pose (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  pose proof (size_class_range j J) as SZR.
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  cps_destruct (rslot_facts st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND. 
  cps_pose (rmeta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
  bz_ceil.
  set (G := conc st g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  cps_pose MW as (LI0 & FB0 & SCR0 & ML0).
  cps_pose MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
  unfold RSIZE_CLASSES, RMLOCK, RCTX in *.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. step.
  (* [comment removed for export] *)
  pose proof (rsize_classes_read m1 j MI J) as SCRD. unfold RSIZE_CLASSES in SCRD.
  replace (69272 + 2 * j) with (69272 + j * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  (* [comment removed for export] *)
  pose proof (rmrep_active_read st m1 j (wa (410856 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
  replace (wa (410856 + 80 + 8 * j)) with (Z_to_bv 64 (410848 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  step.
  (* [comment removed for export] *)
  step.
  eapply evt_mono.
  { eapply (renframe_walk (Z_to_bv 64 0x2a614) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
              (pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
         | |- _ => idtac end.
    all: try (rewrite (unsigned_lit G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
    - exact (so_maplen _ _ _ _ _ _ SO). }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
  cps_destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
  set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
  pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
  replace (fold_off off0 0) with 0 in EM |- * by lia.
  rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
  replace (ret_pc (Z_to_bv 64 0x2a614)) with (Z_to_bv 64 0x2a614) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - N < 2^31) by lia.
  assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
  assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
  assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
  cps_destruct (renframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
    as (MRr & TKr & CONCr & FSTr & SNDr). clear T1 T3 T0 TN T4.
  rewrite Z.mul_0_r, Z.add_0_r in MRr.
  change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
  fold P in MRr, EM. rewrite <- EM in MRr.
  destruct (enf0_st_eq st g b r idx j STR SO) as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
  (* [comment removed for export] *)
  assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
  { rewrite EM. unfold renframe_tail_mem, renframe_off_mem. cbn [Z.eqb].
    replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
  assert (MU : munch [(P - 3, P)]%Z m1 m').
  { rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono rsegs m1 m').
  { rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
  do 14 eexists. exists m'.
  split; [unfold P, G; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

(* [comment removed for export] *)
Lemma renfD_walk :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
  meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
  rmrep (enf0_st st g b idx) mC -> ticks_ok (enf0_st st g b idx) -> mem_inv rsegs mC ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2a63c) fc None m' (seg_rom rsegs)
      /\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
      /\ rmrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))) m'
      /\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) (enf0_st st g b idx))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a614) fc None mC (seg_rom rsegs)).
Proof.
  pose proof J as KEEP__; clear KEEP__.   (* [comment removed for export] *)
  intros until mC. intros MST MWT CR MRC TKC MIC.
  cps_pose (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  cps_pose (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). bz_ceil.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  set (st0' := enf0_st st g b idx) in *.
  assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  cps_pose (rmeta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _).
  change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
  cps_pose (rmeta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _).
  assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
  assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
  rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
  pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
  cps_pose MWT as (LI0 & FB0 & SCR0 & ML0). pose proof (meta_word_range _ MWT) as MWR.
  bz_ceil.
  (* [comment removed for export] *)
  rmchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
  rmeta_open (conc st mt) MUt WMt.
  step.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
  set (w := meta_word (get_meta_rec st mt)) in *.
  rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
  rewrite (meta_word_mod4096 st g b idx j _ MWT).
  step.
  lazymatch goal with H : rw_cells rsegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR5 : rmrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
    [ eapply rmrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto_fast];
      unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
    | clear MUt WMt H ] end.
  set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
  assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
  (* [comment removed for export] *)
  pose proof (land31_range idx) as L31.
  assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
  { change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
    rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
      [| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
    change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (rmrep_shadow_read st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
    by (unfold wa; f_equal; unfold P; lia).
  step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit cnt), swrap32_small by lia.
  step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
  step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
  (* [comment removed for export] *)
  cps_pose MR5 as (_ & _ & _ & _ & _ & SH5). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
  pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
  assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
  cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
  assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
  specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
  replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
  rewrite <- (lor_192 (Z.land idx 31)) by lia.
  rraw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit P) by (unfold P; lia).
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
(* [comment removed for export] *)
Lemma rzero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
  s_regions stz = s_regions st -> s_groups stz = s_groups st ->
  rmrep stz mC -> ticks_ok stz -> mem_inv rsegs mC ->
  munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono rsegs mC0 mC ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2a90c) fc None m' (seg_rom rsegs)
      /\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono rsegs mC0 m' /\ mem_inv rsegs m'
      /\ rmrep (zero_hdrs (pp st g b idx) (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs (pp st g b idx) (16 * szc) i k stz)
      /\ s_regions (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs (pp st g b idx) (16 * szc) i k stz) = s_groups st
      /\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2a63c) fc None mC (seg_rom rsegs)).
Proof using MR STR SO.   (* [comment removed for export] *)
  induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
  { exfalso. lia. }
  cps_pose (enf_facts st g b r idx j SO) as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
  cps_pose (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2). bz_ceil.
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  (* [comment removed for export] *)
  assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
  cps_pose MRz as (WFz & _ & _ & _ & _ & SHz). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
  pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_wr8 stz mX (aadd (pp st g b idx) (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
  unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
  specialize (MR2 Hr' Hk ltac:(lia)).
  assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
            ~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
  { intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). cps_pose WF as (_ & _ & _ & _ & GWF).
    cps_destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16).
    destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
    assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
    assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
    assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
    clear M16 B16 SMOD.
    (* [comment removed for export] *)
    assert (E3 : stride * idx = 16 * (stride / 16 * idx)) by (transitivity (16 * (stride / 16) * idx); [f_equal; exact E2 | ring]).
    lia. }
  specialize (MR2 NOG ltac:(lia)). clear NOG.
  replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
    assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
    [ intros u Hu Hux;
      rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
      destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
      exfalso; lia
    | apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
      apply (wmono_write rsegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
      lazymatch goal with HI : mem_inv rsegs mX |- _ =>
        apply (mem_inv_store rsegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
        [| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
      end;
      clear SOK;
      let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
  end.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
    replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    eapply evt_mono.
    { (eapply (IH (i + 1) szc cnt);
      [ lia | lia | exact SZC | exact CNT | exact FIT
      | rewrite s_regions_wr8; exact RGz
      | rewrite s_groups_wr8; exact GRz
      | exact MR2
      | apply ticks_ok_wr8; exact TKz
      | assumption | exact MU | exact WM ]). }
    cbv beta. (intros ms'; cps_intros (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW)).
    eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact X7|].
    intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
  - (* [comment removed for export] *)
    assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
    split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
    intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.

End ACeilS1.
