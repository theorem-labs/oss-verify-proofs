(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_kitu Atp_arrl.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma fresh_block_sep : forall s p A n LB m a, RHEAP s ((p, A, n) :: LB) m -> A <= a < A + n -> ~ in_block LB a.
Proof.
  intros s p A n LB m a H Ha (b & Hb & Hr).
  pose proof (LH_nodup _ _ _ H) as ND.
  assert (NE : blk_id (p, A, n) <> blk_id b).
  { intros E. cbn [map] in ND. inversion ND as [|x l NI ND' EQ]. subst. apply NI. rewrite E. apply in_map. exact Hb. }
  pose proof (LH_disjoint _ _ _ _ _ H ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
Qed.

Lemma substr_cps_le : forall Q (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (SV A n pos cnt RA : Z),
  rw_cells usegs m SV [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n)] -> 0 <= pos <= n -> 0 < A -> A + n < 2^63 -> 0 <= cnt <= n - pos ->
  0 <= SV -> SV + 16 < 2^64 -> ra = Z_to_bv 64 RA -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
  (forall (xa3 xa4 xa5 : word),
     evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (A + pos)) (Z_to_bv 64 cnt) (Z_to_bv 64 cnt) xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 RA) fc None m (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SV) (Z_to_bv 64 pos) (Z_to_bv 64 cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x29880) fc None m (seg_rom usegs)).
Proof.
  intros until RA. intros SVC POS A0 AN CNT SV0 SV64 -> RA0 RA2 HK.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. step. if_lia. step. astep. step. if_lia.

  astep. astep.
  replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; lia).
  first [ replace (pos + A <? 1) with false by (symmetry; apply Z.ltb_ge; lia)
        | replace (A + pos <? 1) with false by (symmetry; apply Z.ltb_ge; lia) ].
  cbn [Z.b2z Z.lxor Pos.lxor]. astep. step. if_false.

  astep. step. if_lia. step. step.
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
  eapply evt_eq; [| eapply HK]. atp_st_eq.
Qed.

End WithCeiling0.
