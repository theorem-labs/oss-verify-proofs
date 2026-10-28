(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx X_aexdefs D_aex D_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Definition e_target_run : Z := 0xae478.
Definition e_emit : Z := 0xae600.
Definition TR_JOIN : Z := 0xae4c0.
Definition TR_HEAD : Z := 0xae530.

Definition tr_calls (L : Z) (c0 : byte) : Z := if L =? 0 then 1 else Z.land (bv_unsigned c0) 3 + 1.

Definition tr_frame (m : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
  exists junk, rw_cells bsegs m (sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition TRPRO_FP (sp : Z) : list (Z * Z) := [(sp - 128, sp); (AEX, AEX + 48); (AEX_A0, AEX_A0 + 16); (TR_LATCH, TR_LATCH + 1)].

Lemma tr_pro_join : forall (sp cp L pp plen : Z)
    (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z)
    (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo sp -> SEGTOP_A <= lo -> lo + 0x1000 <= sp -> sp mod 16 = 0 -> sp < 2^47 ->
  aexA m -> rw_cells bsegs m 0x6cb5f8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  ro_cells bsegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)] -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
                 ms' = MS (mkR x1 (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 pp)
                               a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_LATCH) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (Z_to_bv 64 TR_JOIN) fc None m' (seg_rom bsegs)
       /\ munch (TRPRO_FP sp) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ tr_frame m' sp ra s0 s1 s2 s3 s4 s5 s6 s7 /\ stk bsegs m' lo (sp - 80) /\ aex_reg m')
    (entry_st ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_target_run m).
Proof.
  intros until tm1. intros ST SL LO U16 UT AEXH LCH GI MI.
  unfold entry_st, e_target_run, TR_JOIN, TRPRO_FP. pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  aex_lits. unfold GOT_LLVMINIT, TP_A in *.
  pose proof (munch_refl [(sp - 128, sp); (0x6cb3b8, 0x6cb3b8 + 48); (0x6cb4d8, 0x6cb4d8 + 16); (0x6a9790, 0x6a9790 + 1)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  carve_frame 80%nat ST.
  destruct AEXH as [((p1 & p2 & f1 & TBL) & (a1v & TA0) & LT & FL) | ((p1 & p2 & TBL) & TA0 & LT & FL)]; unfold aex_tbl in TBL; aex_lits.
  -
    steps_to 0xae4bc%Z. step.
    change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
    step. step. change (le1 (Z_to_bv 64 1)) with (le1 (zxb (Z_to_bv 8 1))). mem_after_store.

    steps_to 0x14f6e4%Z.
    remember (Z_to_bv 64 (sp + -80) : word) as sp1 eqn:Esp1.
    assert (Hsp1 : bv_unsigned sp1 = sp + -80) by (rewrite Esp1; apply unsigned_lit; lia).
    call (atexitA_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo X_AEXGUARD p1 p2 f1 (Z_to_bv 64 X_COVDUMP) a1v cdt thr sec tm1);
      [ rewrite ?Hsp1; aex_lits; first [hyp_by_addr | reflexivity | lia] .. | ].

    rewrite ?Hsp1 in *. subst sp1.
    astep.
    steps_to 0xae4c0%Z.
    apply evt_done. unfold tr_frame, aex_reg. aex_lits. replace (sp - 80) with (sp + -80) by lia. sys_finish.
    all: try (eexists; eassumption); try (do 2 eexists; eassumption).

  -
    steps_to 0xae4bc%Z. step.
    change (zxb (Z_to_bv 8 1)) with (Z_to_bv 64 1 : word). if_false.
    apply evt_done. unfold tr_frame, aex_reg. aex_lits. replace (sp - 80) with (sp + -80) by lia. sys_finish.
    all: try (eexists; eassumption); try (do 2 eexists; eassumption).

  Qed.

Lemma tr_pro_copy : forall (sp cp L pp plen : Z) (c0 : byte)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z),
  0 < cp < 2^47 -> 0 <= L < 32768 -> 0 < plen < 2^26 -> sp < 2^47 -> lo + 0x1000 <= sp -> SEGTOP_A <= lo ->
  cp + 1 <= lo -> (SEGTOP_A <= cp \/ cp + 1 <= 0x10000) ->
  (0 < L -> bytes_at bsegs m cp [c0]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a1' a2' a3' : word),
                 ms' = entry_st (Z_to_bv 64 0xae4dc) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
                          (Z_to_bv 64 pp) (Z_to_bv 64 plen) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp)
                          (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 (tr_calls L c0)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_malloc m)
    (MS (mkR x1 (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 pp)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_LATCH) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TR_JOIN) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hcp HL Hpl UT LO SL Hclo Hcseg HC0 MI.
  unfold entry_st, TR_JOIN. unfold SEGTOP_A in SL, Hcseg. aex_lits. unfold TP_A in *.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - step. if_true. step. step. if_true. do 2 step.
    apply evt_done. do 3 eexists. unfold entry_st, tr_calls. rewrite (proj2 (Z.eqb_eq L 0) LZ). replace (sp - 80) with (sp + -80) by lia. cbv delta [mkR]. reflexivity.
  - step. if_false.
    pose proof (u8ro_read bsegs m _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0.
    step. clear R0. step. step. step. if_false. do 2 step.
    apply evt_done. do 3 eexists. unfold entry_st, tr_calls. rewrite (proj2 (Z.eqb_neq L 0) LNZ). rewrite ZX. replace (sp - 80) with (sp + -80) by lia. cbv delta [mkR]. reflexivity.
Qed.

Lemma tr_pro_empty : forall (sp cp L pp : Z) (c0 : byte)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z),
  0 < cp < 2^47 -> 0 <= L < 32768 -> sp < 2^47 -> lo + 0x1000 <= sp -> SEGTOP_A <= lo ->
  cp + 1 <= lo -> (SEGTOP_A <= cp \/ cp + 1 <= 0x10000) ->
  (0 < L -> bytes_at bsegs m cp [c0]) -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists (a0' : word),
                 ms' = MS (mkR x1 (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 TR_EMPTY)
                               a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 cp) (Z_to_bv 64 TR_LATCH) (Z_to_bv 64 (tr_calls L c0))
                               (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 TR_HEAD) fc None m (seg_rom bsegs))
    (MS (mkR x1 (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 pp)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_LATCH) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TR_JOIN) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros Hcp HL UT LO SL Hclo Hcseg HC0 MI.
  unfold TR_JOIN, TR_HEAD, TR_EMPTY. unfold SEGTOP_A in SL, Hcseg. aex_lits. unfold TP_A in *.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - step. if_true. step. step. if_false. steps_to 0xae530%Z.
    apply evt_done. eexists. unfold tr_calls. rewrite (proj2 (Z.eqb_eq L 0) LZ). cbv delta [mkR]. reflexivity.
  - step. if_false.
    pose proof (u8ro_read bsegs m _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0.
    step. clear R0. step. step. step. if_true. steps_to 0xae530%Z.
    apply evt_done. eexists. unfold tr_calls. rewrite (proj2 (Z.eqb_neq L 0) LNZ). rewrite ?ZX. cbv delta [mkR]. reflexivity.
Qed.
