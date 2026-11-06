(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated by R4Printf.BzPrintfPort (a Theorem Labs lane) onto plugin-hostd/fuzz_reply.asan from a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/K/I_vprintfw.v: module paths and 22 address numerals, rewritten in one pass, each paired by object (the code functions are identical modulo pc-relative fields): 0x140d5->0x140af string "vprintf" (code ref ___interceptor_vprintf+0x44 addi); 0x42684->0x421cc trampoline_vprintf+0x0; 0x44f40->0x458c8 ___interceptor_vprintf+0x0; 0x44f8c->0x45914 ___interceptor_vprintf+0x4c; 0x44f90->0x45918 ___interceptor_vprintf+0x50; 0x44fa0->0x45928 ___interceptor_vprintf+0x60; 0x44fa4->0x4592c ___interceptor_vprintf+0x64; 0x44fdc->0x45964 printf_common+0x0; 0x5a078->0x5adf0 TryAsanInitFromRtl+0x0; 0x92d48->0x92d08 vfprintf+0x0; 0x982c8->0x95e18 vprintf+0x0; 0x9f6e0->0x9d9c0 GOT cell of common_flags_dont_use, code ref printf_common+0x610 ld; 0x9f6e8->0x9d9c8 end of GOT cell of common_flags_dont_use (0x9f6e0 + 8); 0xa1460->0x9f760 REAL(vprintf)+0x0; 0xa1468->0x9f768 REAL(vfprintf)+0x0; 0xa1470->0x9f770 REAL(vsnprintf)+0x0; 0xa8c18->0xa6d98 asan_inited+0x0; 0xa8c19->0xa6d99 end of asan_inited (+1); 0x139a68->0x137be8 common_flags_dont_use+0x0; 0x139abc->0x137c3c common_flags_dont_use+0x54; 0x139abd->0x137c3d common_flags_dont_use+0x55, end of check_printf byte (+0x54..+0x55); 0x5f7000->0x5fb000 try_init_spec's stack bound (our I_ikit.v), fuzz_reply image end. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread X_atexit D_kit I_ikit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The cells the vprintf and fprintf wrappers read: TryAsanInitFromRtl's flag 0xa6d98 (= 1); the GOT cell 0x9d9c0 of
   common_flags() (0x137be8) and its check_printf byte 0x137c3c (= 1); the REAL cells of vprintf (0x9f760: musl vprintf
   0x95e18) and vfprintf (0x9f768: musl vfprintf 0x92d08). *)
Definition pfcells (m : mem) : Prop :=
  rw_cells asegs m 0xa6d98 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x9d9c0 [C8 (Z_to_bv 64 0x137be8)]
  /\ ro_cells asegs m 0x137c3c [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x9f760 [C8 (Z_to_bv 64 0x95e18)]
  /\ ro_cells asegs m 0x9f768 [C8 (Z_to_bv 64 0x92d08)].
Definition in_PFR (x : Z) : Prop :=
  (0xa6d98 <= x < 0xa6d99) \/ (0x9d9c0 <= x < 0x9d9c8) \/ (0x137c3c <= x < 0x137c3d) \/ (0x9f760 <= x < 0x9f770).

Lemma pfcells_munch : forall W m m', pfcells m -> munch W m m' -> wmono asegs m m' ->
  (forall x, in_PFR x -> outside W x) -> pfcells m'.
Proof.
  intros W m m' (X1 & X2 & X3 & X4 & X5) MU WM HW.
  pose proof (agree_of_munch W m m' _ MU HW) as AG.
  assert (RO : forall A cs, ro_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PFR x) ->
                 ro_cells asegs m' A cs).
  { intros A cs H HX. apply (ro_cells_agree asegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). exact HX. }
  assert (RW : forall A cs, rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> in_PFR x) ->
                 rw_cells asegs m' A cs).
  { intros A cs H HX. apply (rw_cells_agree asegs m m' _ _ H); [| exact WM].
    apply (agree_sub _ _ _ _ AG). exact HX. }
  split; [| split; [| split; [| split]]].
  all: first [ apply RW; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PFR; lia]
             | apply RO; [assumption| cbn [cells_size csize]; intros x Hx; unfold in_PFR; lia] ].
Qed.

(* printf_common (0x45964), which both wrappers call with a0 = the wrapper's name, a1 = the format, a2 = the va_list:
   its stack bound and its return to ra with sp, gp, tp, s0-s11 kept and only its window [sp - 2320, sp) changed. Its
   proof is a separate piece; the walks through it (vprintf_walkA here, fprintf_walkA of I_fprintfw.v) take
   pcom_stmt as a section hypothesis, over its start premise pc_pre (format, va_list, memory). *)
Notation PCOM_DEPTH := 2320%Z (only parsing).

Definition pcom_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - PCOM_DEPTH, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition pcom_stmt (pc_pre : word -> word -> mem -> Prop) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo ->
  bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 -> pc_pre a1 a2 m -> mem_inv asegs m ->
  evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45964) fc None m (seg_rom asegs)).

(* The state at the printf_common call 0x45914 (jal, ra = 0x45918): the own frame of 48 bytes at usp - 48 holds
   [junk; ap; ap; s1; s0; ra]; s0 = fmt, s1 = ap; a0 = "vprintf" (0x140af), a1 = fmt, a2 = ap. *)
Definition vpwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x45918) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 0x140af) a0 a1
                  a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x45964) fc None m' (seg_rom asegs)
    /\ munch [(usp - 64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [CB 8 junk; C8 a1; C8 a1; C8 s1; C8 s0; C8 ra].

(* From the trampoline 0x421cc (j 0x458c8) with a0 = fmt, a1 = ap: the frame, TryAsanInitFromRtl (returns 1),
   check_printf = 1, to the printf_common call. *)
Lemma vprintf_walkA1 : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> 0x5fb000 <= lo -> usp <= 2^47 -> pfcells m -> mem_inv asegs m ->
  evt asegs (vpwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421cc) fc None m (seg_rom asegs)).
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
  apply evt_done. unfold vpwA1_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FRv].
Qed.

(* From printf_common's return 0x45918 to the REAL(vprintf) call 0x45928 (jalr a2, a2 = musl vprintf 0x95e18 from the
   REAL cell 0x9f760; ra = 0x4592c): a0 = s0 = fmt, a1 = ap from the frame. *)
Lemma vprintf_walkA2 : forall (usp : Z) (junk : list byte) (v ra0 c0 c1 : word)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m (usp + -48) [CB 8 junk; C8 v; C8 v; C8 c1; C8 c0; C8 ra0] ->
  ro_cells asegs m 0x9f760 [C8 (Z_to_bv 64 0x95e18)] ->
  usp <= 2^47 -> 48 <= usp -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' : word), ms' =
      MS (mkR (Z_to_bv 64 0x4592c) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 s0 v a2' a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x95e18) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45918) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros FRv RVP SPH SPL MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  do 5 lstep.
  apply evt_done. eexists. reflexivity.
Qed.

(* From the return 0x4592c of the REAL(vprintf) call to the caller: restores ra, s0, s1 from the frame, pops it and
   returns; a0 = the result. *)
Lemma vprintf_walkB : forall (usp lo : Z) (junk : list byte)
    (v ra' ra gp tp t0 t1 t2 s0 s1 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  stk asegs m lo (usp + -48) -> lo <= usp + -48 -> usp <= 2^47 ->
  rw_cells asegs m (usp + -48) [CB 8 junk; C8 v; C8 v; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0' s1' a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4592c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UT FRv MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  do 5 lstep.
  release_frame FRv ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.

(* The state at the REAL(vprintf) call: pc = musl vprintf 0x95e18, ra = 0x4592c, sp = usp - 48, a0 = s0 = fmt,
   a1 = s1 = ap; the memory differs from the entry memory only in [usp - 2368, usp) (the frame, TryAsanInitFromRtl's
   and printf_common's windows); the frame holds [junk; ap; ap; s1; s0; ra]. *)
Definition vprintf_at_call (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x4592c) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 a0 a1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x95e18) fc None m' (seg_rom asegs)
    /\ munch [(usp - 2368, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [CB 8 junk; C8 a1; C8 a1; C8 s1; C8 s0; C8 ra].

Section WithPC.
Variable pc_pre : word -> word -> mem -> Prop.
Hypothesis PCOM : pcom_stmt pc_pre.

(* From the trampoline 0x421cc to the REAL(vprintf) call: vprintf_walkA1, printf_common (PCOM, its start premise in
   every memory that differs from the entry memory only in [usp - 64, usp)), vprintf_walkA2. *)
Lemma vprintf_walkA : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 2368 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> pfcells m ->
  (forall m', munch [(usp - 64, usp)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> pc_pre a0 a1 m') ->
  mem_inv asegs m ->
  evt asegs (vprintf_at_call usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421cc) fc None m (seg_rom asegs)).
Proof using PCOM.
  intros until m. intros ST LO LOLO SPH S16 PFC PRE MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO'.
  pose proof PFC as (_ & _ & _ & RVP & _).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply (vprintf_walkA1 usp lo); [exact ST | lia | lia | exact SPH | exact PFC | exact MI] |].
  intros ms1 H1. unfold vpwA1_post in H1.
  destruct H1 as (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1
                  & ST1 & FR1).
  pose proof (PRE m1 MU1 WM1 MI1) as PRE1.
  assert (RVP1 : ro_cells asegs m1 0x9f760 [C8 (Z_to_bv 64 0x95e18)]).
  { apply (ro_cells_transport asegs _ m m1 _ _ RVP MU1).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  pose proof PCOM as PC. unfold pcom_stmt in PC.
  eapply evt_cut.
  { apply PC with (lo := lo);
      [ rewrite EU48; exact ST1 | rewrite EU48; lia | exact LOLO | rewrite EU48; lia
      | rewrite EU48; Z.div_mod_to_equations; lia | exact PRE1 | exact MI1 ]. }
  intros ms2 H2. unfold pcom_post in H2.
  destruct H2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite EU48 in MU2, ST2.
  assert (FR2 : rw_cells asegs m2 (usp + -48) [CB 8 junk; C8 a1; C8 a1; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport asegs _ m1 m2 _ _ FR1 MU2 WM2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  assert (RVP2 : ro_cells asegs m2 0x9f760 [C8 (Z_to_bv 64 0x95e18)]).
  { apply (ro_cells_transport asegs _ m1 m2 _ _ RVP1 MU2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  replace (ret_pc (Z_to_bv 64 0x45918)) with (Z_to_bv 64 0x45918) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  eapply evt_cut; [apply (vprintf_walkA2 usp junk a1 ra s0 s1); [exact FR2 | exact RVP2 | exact SPH | lia | exact MI2] |].
  intros ms3 (a2' & ->).
  apply evt_done. unfold vprintf_at_call. exists m2. do 13 eexists. exists junk. split; [reflexivity|].
  split.
  { apply (munch_trans [(usp - 2368, usp)] m m1 m2).
    - apply (munch_weaken [(usp - 64, usp)]); [| exact MU1].
      unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
    - apply (munch_weaken [(usp + -48 - 2320, usp + -48)]); [| exact MU2].
      unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans asegs m m1 m2 WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2| exact FR2].
Qed.
End WithPC.
