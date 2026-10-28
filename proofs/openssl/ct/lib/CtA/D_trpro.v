(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Nodes RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition e_target_run : Z := 0x1f3f18.
Definition e_emit : Z := 0x1f40a4.
Definition e_atexit : Z := 0x51fb14.          (* [comment removed for export] *)
Definition AEF_GUARD : Z := 0x1f4074.         (* [comment removed for export] *)
Definition AEF_INCB : Z := 0xba4694.          (* [comment removed for export] *)
Definition AEF_ARGC : Z := 0x5aebc8.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition tr_calls (L : Z) (c0 : byte) : Z := if L =? 0 then 1 else Z.land (bv_unsigned c0) 3 + 1.

(* [comment removed for export] *)
Definition tr_frame (m : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
  exists junk, rw_cells ctasegs m (sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma rw_cells_c8_blob : forall segs (m : word -> option byte) A v cs, rw_cells segs m A (C8 v :: cs) -> rw_cells segs m A (CB 8 (le8 v) :: cs).
Proof.
  intros segs m A v cs [[W B] Wr]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le8| exact (proj2 W)].
  - exact B.
  - exact Wr.
Qed.

(* [comment removed for export] *)
Lemma tr_pro_atexit : forall (sp cp L pp plen : Z)
    (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z),
  stk ctasegs m lo sp -> SEGTOP_A <= lo -> lo + 0x1000 <= sp -> sp mod 16 = 0 -> sp < 2^47 ->
  0 < cp < 2^47 -> 0 <= L < 32768 -> 0 < pp < 2^47 -> 0 <= plen < 2^26 ->
  rw_cells ctasegs m TR_INIT [C1 (Z_to_bv 8 0)] -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : word -> option byte) junk,
                 ms' = entry_st (Z_to_bv 64 0x1f3fb0) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
                          (Z_to_bv 64 pp) (Z_to_bv 64 AEF_GUARD) (Z_to_bv 64 0) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7
                          (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_atexit m'
       /\ munch [(sp - 80, sp); (TR_INIT, TR_INIT + 1)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
       /\ rw_cells ctasegs m' (sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ stk ctasegs m' lo (sp - 80) /\ rw_cells ctasegs m' TR_INIT [C1 (Z_to_bv 8 1)])
    (entry_st ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_target_run m).
Proof.
  intros until lo. intros ST SL LO U16 UT Hcp HL Hpp Hpl LT MI.
  unfold entry_st, e_target_run. pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl [(sp - 80, sp); (12207760, 12207761)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  unfold TR_INIT in LT.
  carve_frame 80%nat ST.
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  do 18 step.
  assert (EZ : bv_unsigned (zxb (Z_to_bv 8 0)) = 0) by reflexivity.
  if_true. do 2 step.
  change (le1 (Z_to_bv 64 1)) with (le1 (zxb (Z_to_bv 8 1))).
  mem_after_store.
  do 4 step.
  apply evt_done. do 2 eexists. split; [unfold entry_st, AEF_GUARD, e_atexit; reflexivity|].
  unfold TR_INIT. replace (sp - 80) with (sp + -80) by lia.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact FR|].
  split; [exact ST| exact LT].
Qed.

(* [comment removed for export] *)
Lemma tr_pro_init : forall (sp cp L pp plen : Z)
    (gp t0 t1 t2 v1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (junk : list byte) (c0 c1 c2 c3 c4 c5 c6 c7 cra : word)
    F fc (m : word -> option byte),
  sp mod 16 = 0 -> 0x1000 <= sp -> sp < 2^47 ->
  rw_cells ctasegs m (sp - 80) [CB 8 junk; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra] ->
  ro_cells ctasegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0x1f40ec)] -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : word -> option byte),
                 ms' = entry_st (Z_to_bv 64 0x1f4070) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
                          (Z_to_bv 64 pp) (Z_to_bv 64 AEF_ARGC) (Z_to_bv 64 (sp - 80)) a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_init m'
       /\ munch [(sp - 80, sp)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
       /\ tr_frame m' sp cra c0 c1 c2 c3 c4 c5 c6 c7)
    (MS (mkR (Z_to_bv 64 0x1f3fb0) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 0)
             v1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f3fb0) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros U16 SLO UT FR GI MI.
  pose proof (munch_refl [(sp - 80, sp)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 (sp - 80)) = sp - 80) by (apply unsigned_lit; lia).
  unfold GOT_LLVMINIT in GI.
  step. if_true.
  do 3 step. if_false.
  do 4 step.
  change (Z_to_le_bytes 8 5958608) with (le8 (Z_to_bv 64 5958608)). mem_after_store.
  do 2 step.
  apply evt_done. eexists. split; [unfold entry_st, AEF_ARGC, e_init; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  exists (le8 (Z_to_bv 64 5958608)). exact (rw_cells_c8_blob _ _ _ _ _ FR).
Qed.

(* [comment removed for export] *)
Definition tr_cells (l : byte) (p : list byte) (b : byte) : list cell := [C1 l; CB 3 p; C1 b].

(* [comment removed for export] *)
Lemma tr_pro2_copy : forall (sp cp L pp plen : Z) (c0 : byte)
    (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  0 < cp < 2^47 -> 0 <= L < 32768 -> 0 < plen < 2^26 ->
  (0 < L -> bytes_at ctasegs m cp [c0]) -> mem_inv ctasegs m ->
  evt ctasegs (eq (entry_st (Z_to_bv 64 0x1f3f7c) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
                          (Z_to_bv 64 pp) (Z_to_bv 64 plen) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp)
                          (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m))
    (MS (mkR (Z_to_bv 64 0x1f4070) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) v
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f4070) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros Hcp HL Hpl HC0 MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  step.
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - step. if_true. step. step. if_true. do 2 step.
    apply evt_done. unfold entry_st, tr_calls. rewrite (proj2 (Z.eqb_eq L 0) LZ). reflexivity.
  - step. if_false.
    pose proof (u8ro_read ctasegs m _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0.
    step. clear R0. step. step. step. if_false. do 2 step.
    apply evt_done. unfold entry_st, tr_calls. rewrite (proj2 (Z.eqb_neq L 0) LNZ). rewrite ZX. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tr_pro2_empty : forall (sp cp L pp : Z) (c0 : byte) (l b : byte) (p : list byte)
    (gp t0 t1 t2 v a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte),
  0 < cp < 2^47 -> 0 <= L < 32768 ->
  (0 < L -> bytes_at ctasegs m cp [c0]) -> rw_cells ctasegs m TR_INIT (tr_cells l p b) -> mem_inv ctasegs m ->
  evt ctasegs (fun ms' => exists (m' : word -> option byte),
               ms' = entry_st (Z_to_bv 64 0x1f3fe8) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0)
                          (Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 cp)
                          (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m'
               /\ munch [(AEF_INCB, AEF_INCB + 1)] m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
               /\ rw_cells ctasegs m' TR_INIT (tr_cells l p (Z_to_bv 8 1)))
    (MS (mkR (Z_to_bv 64 0x1f4070) (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 pp) v
             a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1f4070) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros Hcp HL HC0 TC MI.
  pose proof (munch_refl [(12207764, 12207765)] m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b0; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b0) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold tr_cells in TC. unfold TR_INIT in *.
  step.
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - step. if_true. step. step. if_false. do 6 step.
    change (le1 (Z_to_bv 64 1)) with (le1 (zxb (Z_to_bv 8 1))). mem_after_store.
    do 3 step.
    apply evt_done. eexists. split; [unfold entry_st, tr_calls, TR_EMPTY, TR_INIT; rewrite (proj2 (Z.eqb_eq L 0) LZ); reflexivity|].
    unfold AEF_INCB, tr_cells. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact TC].
  - step. if_false.
    pose proof (u8ro_read ctasegs m _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0.
    step. clear R0. step. step. step. if_true. do 6 step.
    change (le1 (Z_to_bv 64 1)) with (le1 (zxb (Z_to_bv 8 1))). mem_after_store.
    do 3 step.
    apply evt_done. eexists. split; [unfold entry_st, tr_calls, TR_EMPTY, TR_INIT; rewrite (proj2 (Z.eqb_neq L 0) LNZ); rewrite ZX; reflexivity|].
    unfold AEF_INCB, tr_cells. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact TC].
Qed.
