(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Definition httpmsg_compare_entry := 0x14038%Z.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap.
  change (bv_swrap 32 (e mod 2^64)) with (((e mod 2^64) + 2^31) mod 2^32 - 2^31)%Z.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma mod64_small_signed : forall a, (-2^31 <= a < 2^31)%Z ->
  (a mod 2^64 = if (a <? 0)%Z then a + 2^64 else a)%Z.
Proof.
  intros a Ha. destruct (Z.ltb_spec0 a 0).
  - rewrite <- (Z.mod_add a 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma mod64_inj_signed : forall a b, (-2^31 <= a < 2^31)%Z -> (-2^31 <= b < 2^31)%Z ->
  (a mod 2^64 = b mod 2^64)%Z -> a = b.
Proof.
  intros a b Ha Hb E. rewrite !mod64_small_signed in E by lia.
  destruct (Z.ltb_spec0 a 0); destruct (Z.ltb_spec0 b 0); lia.
Qed.

Definition cmp32_expr (ia ib : Z) : word :=
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 ia))) (bv_unsigned (sx32 (Z_to_bv 64 ib))))) 1.

Lemma cmp32_eval : forall ia ib, (-2^31 <= ia < 2^31)%Z -> (-2^31 <= ib < 2^31)%Z ->
  cmp32_expr ia ib = Z_to_bv 64 (if (ia =? ib)%Z then 1 else 0).
Proof.
  intros ia ib Ha Hb. unfold cmp32_expr. rewrite !sx32_lit by lia. rewrite v_sltiu_b2z.
  rewrite !unsigned_lit_wrap.
  assert (R1 : (0 <= ia mod 2^64 < 2^64)%Z) by (apply Z.mod_pos_bound; lia).
  assert (R2 : (0 <= ib mod 2^64 < 2^64)%Z) by (apply Z.mod_pos_bound; lia).
  pose proof (zr_lxor _ _ R1 R2) as RX. unfold inr64 in RX.
  rewrite (Z.mod_small (Z.lxor _ _)) by lia.
  change (bv_wrap 64 1) with 1%Z.
  f_equal. destruct (Z.eqb_spec ia ib) as [E|NE].
  - subst. rewrite Z.lxor_nilpotent. reflexivity.
  - destruct (Z.ltb_spec0 (Z.lxor (ia mod 2^64) (ib mod 2^64)) 1) as [L|L]; [|reflexivity].
    exfalso. assert (E0 : Z.lxor (ia mod 2^64) (ib mod 2^64) = 0%Z) by lia.
    apply (proj1 (zb_lxor_eq0 _ _)) in E0. apply NE. apply mod64_inj_signed; [lia|lia|]. exact E0.
Qed.

Definition httpmsg_compare_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ia ib : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if (ia =? ib)%Z then 1 else 0)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Definition httpmsg_compare_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B ia ib : Z) (ja : list byte) (n1 n2 pad : word),
  rw_cells rsegs m A [CB 16%nat ja; C4 (wz ia)] ->
  rw_cells rsegs m B [C8 n1; C8 n2; C4 (wz ib); C4 pad] ->
  (- 2^31 <= ia < 2^31)%Z -> (- 2^31 <= ib < 2^31)%Z ->
  (A <> 0)%Z -> (A mod 8 = 0)%Z -> (B <> 0)%Z -> (B mod 8 = 0)%Z ->
  mem_inv rsegs m -> a0 = wz A -> a1 = wz B ->
  evt rsegs (httpmsg_compare_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ia ib m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz httpmsg_compare_entry) fc None m (seg_rom rsegs)).

Lemma httpmsg_compare_spec : httpmsg_compare_stmt.
Proof.
  intros until pad. intros CA CB2 RA RB NA AA NB AB MI -> ->. unfold httpmsg_compare_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ CA) as BA. pose proof (rw_cells_bound rsegs _ _ _ CB2) as BB.
  cbn [cells_size csize Nat.add] in BA, BB.
  ub_null. ub_align. ub_null. ub_align.
  step. step. step. step. step.
  change (v_sltiu _ 1) with (cmp32_expr ia ib). rewrite cmp32_eval by assumption.
  finish.
Qed.
