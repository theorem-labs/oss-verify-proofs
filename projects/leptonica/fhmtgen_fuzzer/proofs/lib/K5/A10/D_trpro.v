(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Nodes RzCPS NodesA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx X_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Import ListNotations.
Open Scope Z_scope.

Definition e_target_run : Z := 0x90c78.
Definition e_emit : Z := 0x90e00.
Definition TR_BASE : Z := 0x622c10.
Definition AEF_GUARD : Z := 0x90dd0.

(* [comment removed for export] *)
Definition tr_calls (L : Z) (c0 : byte) : Z := if L =? 0 then 1 else Z.land (bv_unsigned c0) 3 + 1.

(* [comment removed for export] *)
Definition tr_frame (m : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 : word) : Prop :=
  exists junk, rw_cells asegs m (sp - 80) [CB 8 junk; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition TR_PRO_W (sp : Z) : list (Z * Z) :=
  [(sp - 128, sp); (0x622c10, 0x622c11); (0x6437d8, 0x6437f0); (0x643800, 0x643808); (0x643900, 0x643908)].

Ltac xstep := lstep; fold_closed_in_goal; try (first [if_true | if_false]).
Ltac xsteps_to p := repeat (tryif at_pc p then fail else xstep).
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.

Section TrPro.
Variables (sp cp L pp : Z) (c0 fl : byte) (p1 p2 : list byte) (cdt thr sec : byte) (tm1 j1 j2 : word)
          (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo : Z).
Hypotheses (ST : stk asegs m lo sp) (SL : SEGTOP_A <= lo) (LO : lo + 0x1000 <= sp) (U16 : sp mod 16 = 0) (UT : sp < 2^47)
           (Hcp : 0 < cp < 2^47) (HL : 0 <= L < 32768) (Hpp : 0 < pp < 2^47)
           (Hclo : cp + 1 <= lo) (Hcseg : SEGTOP_A <= cp \/ cp + 1 <= 0x10000)
           (HC0 : 0 < L -> bytes_at asegs m cp [c0])
           (ATX : rw_cells asegs m 0x6437d8 (atexit_cells (Z_to_bv 8 0) p1 p2 1 0x6437f0 0 0xd0858))
           (F1 : rw_cells asegs m 0x643800 [C8 j1]) (A1 : rw_cells asegs m 0x643900 [C8 j2])
           (LIBC : rw_cells asegs m 0x643a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
           (LATCH : rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 0)])
           (FL : rw_cells asegs m TR_INIT [C1 fl])
           (GI : ro_cells asegs m GOT_LLVMINIT [C8 (Z_to_bv 64 0)])
           (MI : mem_inv asegs m).

Definition tr_pro_mem (m' : word -> option byte) : Prop :=
  wmono asegs m m' /\ mem_inv asegs m' /\ tr_frame m' sp ra s0 s1 s2 s3 s4 s5 s6 s7 /\ stk asegs m' lo (sp - 80)
  /\ reg_post m' /\ rw_cells asegs m' 0x643a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].

Local Ltac fin_mem MU WM EU80 EU80' :=
  split; [exact MU|];
  split;
  [ unfold tr_pro_mem; split; [exact WM|]; split; [assumption|];
    split; [eexists; rewrite <- EU80'; eassumption|];
    split; [match goal with H : stk asegs _ lo _ |- _ => first [rewrite EU80 in H; rewrite EU80' in H; exact H | rewrite EU80' in H; exact H | exact H] end|];
    split; [| assumption];
    unfold reg_post, atexit_cells; do 2 eexists; repeat match goal with |- _ /\ _ => split end; eassumption
  | assumption ].

Local Ltac prefix ATX' F1 A1 LIBC EU80 :=
  xsteps_to 0xd0794%Z;
  (call atexit_reg_spec; [reflexivity| lia| rewrite EU80; eassumption| exact ATX'| exact F1| exact A1| exact LIBC| assumption| rewrite EU80; lia| lia|]);
  xstep; xstep; xstep; xstep.

(* [comment removed for export] *)
Lemma tr_pro_copy : forall plen : Z, 0 < plen < 2^26 ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
                 ms' = entry_st (Z_to_bv 64 0x90cdc) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 plen)
                          (Z_to_bv 64 pp) (Z_to_bv 64 plen) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 L) (Z_to_bv 64 cp)
                          (Z_to_bv 64 TR_BASE) (Z_to_bv 64 (tr_calls L c0)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc e_malloc m'
       /\ munch (TR_PRO_W sp) m m' /\ tr_pro_mem m' /\ rw_cells asegs m' TR_INIT [C1 fl])
    (entry_st ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_target_run m).
Proof using All.
  intros plen Hpl.
  unfold entry_st, e_target_run. pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl (TR_PRO_W sp) m) as MU. unfold TR_PRO_W in MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  pose proof FL as FL'. unfold TR_INIT in FL'. pose proof GI as GI'. unfold GOT_LLVMINIT in GI'. pose proof LATCH as LATCH'. unfold TR_LATCH in LATCH'.
  pose proof ATX as ATX'. unfold atexit_cells in ATX'. clear FL GI LATCH ATX.
  carve_frame 80%nat ST.
  assert (EU80 : bv_unsigned (Z_to_bv 64 (sp + -80)) = sp + -80) by (apply unsigned_lit; lia).
  assert (EU80' : sp + -80 = sp - 80) by lia.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (EP : bv_unsigned (Z_to_bv 64 plen) = plen) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold SEGTOP_A in Hcseg.
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - prefix ATX' F1 A1 LIBC EU80.
    xstep. xstep. xstep. xstep. xstep.
    apply evt_done. do 15 eexists. split; [unfold tr_calls; rewrite (proj2 (Z.eqb_eq L 0) LZ); cbv delta [mkR]; reflexivity|].
    fin_mem MU WM EU80 EU80'.
  - prefix ATX' F1 A1 LIBC EU80.
    xstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0 end.
    xstep. clear R0. xstep. xstep. xstep. xstep. xstep.
    apply evt_done. do 15 eexists. split; [unfold tr_calls; rewrite (proj2 (Z.eqb_neq L 0) LNZ); rewrite ?ZX; cbv delta [mkR]; reflexivity|].
    fin_mem MU WM EU80 EU80'.
Qed.

(* [comment removed for export] *)
Lemma tr_pro_empty :
  evt asegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
                 ms' = entry_st (Z_to_bv 64 0x90d44) (Z_to_bv 64 (sp - 80)) gp (Z_to_bv 64 TP_A) t0' t1' t2' (Z_to_bv 64 0)
                          (Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 TR_EMPTY) (Z_to_bv 64 0) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 0) (Z_to_bv 64 cp)
                          (Z_to_bv 64 TR_BASE) (Z_to_bv 64 (tr_calls L c0)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6'
                          F fc e_fuzz m'
       /\ munch ((TR_INIT, TR_INIT + 1) :: TR_PRO_W sp) m m' /\ tr_pro_mem m' /\ rw_cells asegs m' TR_INIT [C1 (Z_to_bv 8 1)])
    (entry_st ra (Z_to_bv 64 sp) gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 0)
       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_target_run m).
Proof using All.
  unfold entry_st, e_target_run. pose proof ST as (STa & STb & _). unfold SEGTOP_A in SL.
  pose proof (munch_refl ((TR_INIT, TR_INIT + 1) :: TR_PRO_W sp) m) as MU. unfold TR_PRO_W, TR_INIT in MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  pose proof FL as FL'. unfold TR_INIT in FL'. pose proof GI as GI'. unfold GOT_LLVMINIT in GI'. pose proof LATCH as LATCH'. unfold TR_LATCH in LATCH'.
  pose proof ATX as ATX'. unfold atexit_cells in ATX'. clear FL GI LATCH ATX.
  carve_frame 80%nat ST.
  assert (EU80 : bv_unsigned (Z_to_bv 64 (sp + -80)) = sp + -80) by (apply unsigned_lit; lia).
  assert (EU80' : sp + -80 = sp - 80) by lia.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ZX : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b) by (intros b; unfold zxb; apply unsigned_lit; pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia).
  unfold SEGTOP_A in Hcseg.
  destruct (Z.eq_dec L 0) as [LZ|LNZ]; [clear HC0| specialize (HC0 ltac:(lia))].
  - prefix ATX' F1 A1 LIBC EU80.
    xsteps_to 0x90e48%Z.
    apply evt_done. do 14 eexists. split; [unfold tr_calls, TR_EMPTY, TR_BASE; rewrite (proj2 (Z.eqb_eq L 0) LZ); cbv delta [mkR]; reflexivity|].
    fin_mem MU WM EU80 EU80'.
  - prefix ATX' F1 A1 LIBC EU80.
    xstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm _ _ 0 c0 (wa (cp + 0)) HC0 eq_refl ltac:(lia) eq_refl) as R0 end.
    xstep. clear R0.
    xsteps_to 0x90e48%Z.
    apply evt_done. do 14 eexists. split; [unfold tr_calls, TR_EMPTY, TR_BASE; rewrite (proj2 (Z.eqb_neq L 0) LNZ); rewrite ?ZX; cbv delta [mkR]; reflexivity|].
    fin_mem MU WM EU80 EU80'.
Qed.

End TrPro.
