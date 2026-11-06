(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma land7_mod8 : forall A, (0 <= A)%Z -> (A mod 8 = 0)%Z -> Z.land A 7 = 0%Z.
Proof. intros A H0 H8. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H8. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma tix_shr61 : forall i, 0 <= i < 2^60 -> Z.shiftr (i + 1152921504606846976) 61 = 0.
Proof. intros i Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma tix_land7 : forall T i, T mod 8 = 0 -> 0 <= T -> 0 <= i -> Z.land (T + 8 * i) 7 = 0.
Proof.
  intros T i HT T0 I0. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  rewrite Z.add_mod, HT, Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Lemma tix_cps : forall Q (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D TAPE i RA : Z) (rest : list cell),
  rw_cells usegs m D (C8 (Z_to_bv 64 TAPE) :: rest) -> 0 < TAPE -> 0 <= i -> TAPE + 8 * i < 2^63 -> i < 2^60 -> TAPE mod 8 = 0 ->
  0 <= D -> D + 8 < 2^64 -> ra = Z_to_bv 64 RA -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
  (forall (xa1 xa2 xa3 xa4 : word),
     evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (TAPE + 8 * i)) xa1 xa2 xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 RA) fc None m (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ATP_TIX) fc None m (seg_rom usegs)).
Proof.
  intros until rest. intros DC T0 I0 TI I60 T8 D0 D64 -> RA0 RA2 HK.
  unfold ATP_TIX.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. astep. astep. astep. astep.
  replace (0 <? TAPE) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (TAPE + 8 * i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  step. if_false.

  astep. astep. astep. astep. rewrite tix_shr61 by lia.
  step. if_lia.

  step. if_lia. step. if_lia. astep. rewrite tix_land7 by lia. step. if_lia.
  step.
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
  eapply evt_eq; [| eapply HK]. atp_st_eq.
Qed.

End WithCeiling0.
