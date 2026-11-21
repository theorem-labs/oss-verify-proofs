(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM03.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_B.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM10.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM05.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require F_ntf_H.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MallocFacts_Bpres.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASlot_W13.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_malloc_entry. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1. Import MM08.ASlot_W10. Import MM03. Import MM03.ASlot_W12.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
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

Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).
End ENF.


End CANSEC1.
End ASlot_W13.

Module ASlot_W4.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition t1_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End T1.


End CANSEC1.
End ASlot_W4.

Module ASlot_W5.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import Malloc_fp. Import MM14. Import MM14.MallocKit_A2.
Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
  intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
  rewrite upd_meta_put. reflexivity.
Qed.

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
  intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
  rewrite !upd_meta_put.
  match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
  rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
  f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
  rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

Definition deq_regs (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 CTX) a0 a1 a2 (Z_to_bv 64 (CTX + 8 * (sc + 10))) a4 a5 a6 a7
      (Z_to_bv 64 (sc + 10)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
End DEQ.


End CANSEC1.
End ASlot_W5.

Module F_ntf.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocTree. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_B.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
Import MM13. Import MM13.MallocKit_B. Import MM07. Import MM07.MallocKit_B2. Import MM12. Import MM12.MallocModel_B. Import MM06. Import MM06.F_ntf_A. Import MM07.F_ntf_B. Import MM06.F_ntf_C.
Import MM14. Import MM14.MallocKit_B3. Import MM10. Import MM10.F_ntf_D. Import MM10.F_ntf_E. Import MM05. Import MM05.F_ntf_F. Import MM05.F_ntf_G. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import F_ntf_H.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
  intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
  unfold mw_ok. repeat split; lia.
Qed.

Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
  nontrivial_free dec (S f) st g i k bail =
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if ntf_cond st g i then
    match m_next mr with
    | Some _ =>
      guard 50 (sc <? 48) (
        let activate_new := optr_eqb (active st sc) (Some g) in
        let st1 := dequeue (LActive sc) g st in
        match activate_new, active st1 sc with
        | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
        | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
        end) bail
    | None => free_group R dec (nontrivial_free dec f) st g k bail
    end
  else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
    guard 51 (sc <? 48) (
      if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
      else k (aor_st st g i) None) bail
  else k (aor_st st g i) None.
Proof. reflexivity. Qed.

Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  free_group R dec rec st g k bail =
  let mr := get_meta_rec st g in
  let st1 := fg_usage_st st g in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then
      free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else
      dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
Proof. reflexivity. Qed.


Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
  match mi with
  | None => a1v = wz 0
  | Some (b, len) =>
      a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
      /\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
      /\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
  end.

Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
  forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
    8 <= (r_base r + q) mod 16 ->
    cell_read (get_shadow st rid) q = Unknown h ->
    o (wa (r_base r + q)) = m (wa (r_base r + q)).

Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
  intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma free_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
  intros FR HS H. eapply (free_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.


Lemma free_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  free_fp st' lo sp a -> free_fp st lo sp a.
Proof. intros ER ES EG H. eapply (free_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof. intros H. unfold rdv. rewrite H. reflexivity. Qed.

Section NTF.
Variables (ra0 : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : ATOP <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
End NTF.


End CANSEC1.
End F_ntf.
