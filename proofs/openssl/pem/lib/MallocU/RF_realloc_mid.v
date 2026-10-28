(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RF_realloc_frame.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memcpy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition rrmid_post (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (q p n n0 : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x2b2ad0) sp gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 p) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (p + n0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rfree_entry) fc None m' (seg_rom usegs)
    /\ munch [(q, q + Z.min n n0)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' q [CB (Z.to_nat (Z.min n n0)) src]
    /\ bytes_at usegs m' p src.

Lemma rrealloc_mid : forall (x1 sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (q p n n0 : Z) (src junk : list byte),
  0 < q < 2^64 -> 0 <= p -> 0 <= n < 2^62 -> 0 <= n0 -> p + n0 < 2^64 ->
  bytes_at usegs m p src -> length src = Z.to_nat (Z.min n n0) ->
  rw_cells usegs m q [CB (Z.to_nat (Z.min n n0)) junk] ->
  (p + Z.min n n0 <= q \/ q + Z.min n n0 <= p) ->
  mem_inv usegs m ->
  evt usegs (rrmid_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q p n n0 src m)
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 p) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (p + n0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2aa8) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros Q P N N0 PN SRC LEN DST SEP MI.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  (* [comment removed for export] *)
  step. rewrite ?unsigned_lit by lia. replace (p + n0 + - p) with n0 by lia.
  step.
  assert (CALL : forall (y11 y12 : word), y12 = Z_to_bv 64 (Z.min n n0) ->
    evt usegs (rrmid_post sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc q p n n0 src m)
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 p) (Z_to_bv 64 q) y11 y12 a3 a4 a5 a6 a7
               (Z_to_bv 64 (p + n0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2abc) fc None m (seg_rom usegs))).
  { intros y11 y12 ->.
    (* [comment removed for export] *)
    step. step. step.
    assert (UQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    assert (UP : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 (Z.min n n0)) = Z.min n n0) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply (memcpy_spec _ sp gp tp _ _ _ _ _ (Z_to_bv 64 q) (Z_to_bv 64 p) (Z_to_bv 64 (Z.min n n0)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m src junk);
        rewrite ?UQ, ?UP, ?UN; assumption. }
    intros ms1 (y5 & y6 & y7 & z11 & z12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU & WM & MI1 & DST1 & SRC1).
    rewrite ?UQ, ?UP, ?UN in *.
    replace (ret_pc (Z_to_bv 64 0x2b2ac8)) with (Z_to_bv 64 0x2b2ac8) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    step. step.
    apply evt_done. unfold rrmid_post, rfree_entry. do 15 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact DST1| exact SRC1]. }
  step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    apply CALL. f_equal. lia.
  - step. apply CALL. rewrite Z.min_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_tail : forall (x1 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z),
  rw_cells usegs m (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
  evt usegs (rrepi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q0 F fc lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2ad0) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros FR ST LO MI.
  step. step.
  eapply (rrealloc_epilogue _ ra sp gp tp _ _ _ s0 s1 s2 s3 s4 s5 s6 q0 q1 q2 q3 q4 q5 q6 q0); eassumption.
Qed.
End WithCeiling0.
