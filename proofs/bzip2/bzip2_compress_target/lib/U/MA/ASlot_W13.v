(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp MallocKit_A2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require ASlot_W10 ASlot_W12.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W10 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.ASlot_W12.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

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
Hypothesis MR : mrep st m1.
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
(* [comment removed for export] *)
Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
  cps_intros (LI & FB & SC & ML). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
  rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).

(* [comment removed for export] *)
End ENF.

End ACeilS1.
