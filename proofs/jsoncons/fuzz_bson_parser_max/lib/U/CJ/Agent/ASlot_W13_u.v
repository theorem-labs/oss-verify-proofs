(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u F_malloc_free_u F_malloc_fast_u F_malloc_entry_u F_malloc_enframe_u MallocTree_u MallocKit_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_AB_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import Malloc_fp_u MallocKit_A2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Agent Require Import MallocKit_A3_u ASlot_W1_u ASlot_W10_u ASlot_W12_u.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
(* [comment removed for export] *)
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

Lemma enf_facts : m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b mod 16 = 0
  /\ 0 <= idx <= m_last_idx mr /\ m_last_idx mr < 32
  /\ snd b + 16 + stride * (m_last_idx mr + 1) <= round_up_pg (r_len r) /\ 16 <= stride /\ stride mod 16 = 0
  /\ (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b')
  /\ cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0
  /\ (forall off, 0 <= off -> 16 * off + N + 4 <= stride -> (stride * idx + 16 * off) / 16 < 65536).
Proof.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
  repeat (split; [assumption|]). exact Q16.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enf0_st : mstate :=
  wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
    (wr8 (fst b, snd b + (16 + stride * idx) + -3) idx
      (wr16 (fst b, snd b + (16 + stride * idx) + -2) ((snd b + (16 + stride * idx) - (snd b + 16)) / 16) st)).

Lemma enf0_st_eq : fst (enframe_at st g idx N 0) = enf0_st /\ snd (enframe_at st g idx N 0) = (fst b, snd b + (16 + stride * idx)).
Proof.
  pose proof enf_facts as (Hmem & _).
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
  change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
  unfold set_size. cbn [fst snd].
  replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
  cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
  intros (LI & FB & SC & ML). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
  rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.

Lemma le1_lor_m64 a : 0 <= a < 32 -> le1 (Z_to_bv 64 (Z.lor a 18446744073709551552)) = [b8 (Z.lor a 192)].
Proof.
  intros Ha. unfold le1. cbn [Z_to_le_bytes]. f_equal. unfold b8. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  rewrite <- !(Z.land_ones _ 8) by lia. change (Z.ones 8) with 255.
  rewrite <- (Z.land_ones (Z.lor a 18446744073709551552) 64) by lia.
  change (Z.ones 64) with 18446744073709551615.
  rewrite !Z.land_lor_distr_l. rewrite <- !Z.land_assoc.
  change (Z.land 18446744073709551615 255) with 255. change (Z.land 18446744073709551552 255) with 192.
  change (Z.land 192 255) with 192. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).
(* [comment removed for export] *)
End ENF.
End CEIL_WRAP_1.

