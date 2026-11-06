(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated by R4Printf.BzPrintfPort (a Theorem Labs lane) onto plugin-hostd/fuzz_reply.asan from a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/K/I_vfprintfw.v: module paths and 12 address numerals, rewritten in one pass, each paired by object (the code functions are identical modulo pc-relative fields): 0x1eb50->0x1eaab string "vfprintf" (code ref ___interceptor_vfprintf+0x4c addi); 0x42688->0x421d0 trampoline_vfprintf+0x0; 0x44fdc->0x45964 printf_common+0x0; 0x45aa4->0x4642c ___interceptor_vfprintf+0x0; 0x45af8->0x46480 ___interceptor_vfprintf+0x54; 0x45afc->0x46484 ___interceptor_vfprintf+0x58; 0x45b10->0x46498 ___interceptor_vfprintf+0x6c; 0x45b14->0x4649c ___interceptor_vfprintf+0x70; 0x5a078->0x5adf0 TryAsanInitFromRtl+0x0; 0x92d48->0x92d08 vfprintf+0x0; 0xa1468->0x9f768 REAL(vfprintf)+0x0; 0x5f7000->0x5fb000 try_init_spec's stack bound (our I_ikit.v), fuzz_reply image end. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.K Require Import I_vprintfw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The state at the printf_common call 0x46480 (jal, ra = 0x46484): the own frame of 48 bytes at usp - 48 holds
   [V; V; s2; s1; s0; ra]; s0 = f (the format), s1 = F (the FILE), s2 = V (the va_list); a0 = "vfprintf" (0x1eaab),
   a1 = f, a2 = V. *)
Definition vfwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x46484) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 a1 a0 (Z_to_bv 64 0x1eaab) a1 a2
                  a3 a4 a5 a6 a7 a2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x45964) fc None m' (seg_rom asegs)
    /\ munch [(usp - 64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [C8 a2; C8 a2; C8 s2; C8 s1; C8 s0; C8 ra].

(* From the trampoline 0x421d0 (j 0x4642c) with a0 = F, a1 = f, a2 = V: the frame, TryAsanInitFromRtl (returns 1),
   check_printf = 1, to the printf_common call. *)
Lemma vfprintf_walkA1 : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> 0x5fb000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv asegs m ->
  evt asegs (vfwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421d0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC MI.
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 48%nat ST. rename FR into FRv.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRv; [| reflexivity]. cbn [mk_CB_cells app] in FRv.
  xsteps_to 0x5adf0%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0x45964%Z.
  apply evt_done. unfold vfwA1_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FRv].
Qed.

(* From printf_common's return 0x46484 to the REAL(vfprintf) call 0x46498 (jalr a3, a3 = musl vfprintf 0x92d08 from
   the REAL cell 0x9f768; ra = 0x4649c): a0 = s1 = F, a1 = s0 = f, a2 = V from the frame. *)
Lemma vfprintf_walkA2 : forall (usp : Z) (c0 v c1 c2 c3 ra0 : word)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m (usp + -48) [C8 c0; C8 v; C8 c1; C8 c2; C8 c3; C8 ra0] ->
  ro_cells asegs m 0x9f768 [C8 (Z_to_bv 64 0x92d08)] ->
  usp <= 2^47 -> 48 <= usp -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' : word), ms' =
      MS (mkR (Z_to_bv 64 0x4649c) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 s1 s0 v a3' a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x92d08) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46484) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros FRv RVF SPH SPL MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  do 6 lstep.
  apply evt_done. eexists. reflexivity.
Qed.

(* From the return 0x4649c of the REAL(vfprintf) call to the caller: restores ra, s0, s1, s2 from the frame, pops it
   and returns; a0 = the result. *)
Lemma vfprintf_walkB : forall (usp lo : Z) (c0 c1 : word)
    (ra' ra gp tp t0 t1 t2 s0 s1 s2 s0' s1' s2' a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo (usp + -48) -> lo <= usp + -48 -> usp <= 2^47 ->
  rw_cells asegs m (usp + -48) [C8 c0; C8 c1; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x4649c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UT FRv MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  do 6 lstep.
  release_frame FRv ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.

(* The state at the REAL(vfprintf) call: pc = musl vfprintf 0x92d08, ra = 0x4649c, sp = usp - 48, a0 = s1 = F,
   a1 = s0 = f, a2 = s2 = V; the memory differs from the entry memory only in [usp - 2368, usp) (the frame,
   TryAsanInitFromRtl's and printf_common's windows); the frame holds [V; V; s2; s1; s0; ra]. *)
Definition vfprintf_at_call (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR (Z_to_bv 64 0x4649c) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 a1 a0 a0 a1 a2 a3 a4 a5 a6 a7
                  a2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x92d08) fc None m' (seg_rom asegs)
    /\ munch [(usp - 2368, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [C8 a2; C8 a2; C8 s2; C8 s1; C8 s0; C8 ra].

Section WithPC.
Variable pc_pre : word -> word -> mem -> Prop.
Hypothesis PCOM : pcom_stmt pc_pre.

(* From the trampoline 0x421d0 to the REAL(vfprintf) call: vfprintf_walkA1, printf_common (PCOM, its start premise for
   (f, V) in every memory that differs from the entry memory only in [usp - 64, usp)), vfprintf_walkA2. *)
Lemma vfprintf_walkA : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 2368 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> pfcells m ->
  (forall m', munch [(usp - 64, usp)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> pc_pre a1 a2 m') ->
  mem_inv asegs m ->
  evt asegs (vfprintf_at_call usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421d0) fc None m (seg_rom asegs)).
Proof using PCOM.
  intros until m. intros ST LO LOLO SPH S16 PFC PRE MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO'.
  pose proof PFC as (_ & _ & _ & _ & RVF).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply (vfprintf_walkA1 usp lo); [exact ST | lia | lia | exact SPH | exact PFC | exact MI] |].
  intros ms1 H1. unfold vfwA1_post in H1.
  destruct H1 as (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MU1 & WM1 & MI1 & ST1 & FR1).
  pose proof (PRE m1 MU1 WM1 MI1) as PRE1.
  assert (RVF1 : ro_cells asegs m1 0x9f768 [C8 (Z_to_bv 64 0x92d08)]).
  { apply (ro_cells_transport asegs _ m m1 _ _ RVF MU1).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  pose proof PCOM as PC. unfold pcom_stmt in PC.
  eapply evt_cut.
  { apply PC with (lo := lo);
      [ rewrite EU48; exact ST1 | rewrite EU48; lia | exact LOLO | rewrite EU48; lia
      | rewrite EU48; Z.div_mod_to_equations; lia | exact PRE1 | exact MI1 ]. }
  intros ms2 H2. unfold pcom_post in H2.
  destruct H2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite EU48 in MU2, ST2.
  assert (FR2 : rw_cells asegs m2 (usp + -48) [C8 a2; C8 a2; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (RVF2 : ro_cells asegs m2 0x9f768 [C8 (Z_to_bv 64 0x92d08)]).
  { apply (ro_cells_transport asegs _ m1 m2 _ _ RVF1 MU2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  replace (ret_pc (Z_to_bv 64 0x46484)) with (Z_to_bv 64 0x46484) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply evt_cut; [apply (vfprintf_walkA2 usp a2 a2 s2 s1 s0 ra); [exact FR2 | exact RVF2 | exact SPH | lia | exact MI2] |].
  intros ms3 (a3'' & ->).
  apply evt_done. unfold vfprintf_at_call. exists m2. do 12 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans [(usp - 2368, usp)] m m1 m2).
    - apply (munch_weaken [(usp - 64, usp)]); [| exact MU1].
      unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
    - apply (munch_weaken [(usp + -48 - 2320, usp + -48)]); [| exact MU2].
      unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2| exact FR2].
Qed.
End WithPC.
