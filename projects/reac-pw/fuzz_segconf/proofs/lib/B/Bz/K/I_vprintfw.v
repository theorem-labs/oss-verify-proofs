(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/K/I_vprintfw.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 59 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_manifest.asan from proofs/omx-clap-core/fuzz_state/lib/A/Bz/K/I_vprintfw.v: module paths and 61 address numerals by the address relocator 7a60a01f65f446d8, each paired by object; the decided numerals are listed in the commit body. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread X_atexit D_kit I_ikit. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The cells the vprintf and fprintf wrappers read: TryAsanInitFromRtl's flag 0xb1918 (= 1); the GOT cell 0xa5f40 of
   common_flags() (0x142768) and its check_printf byte 0x1427bc (= 1); the REAL cells of vprintf (0xa7ce8: musl vprintf
   0x9dfd0) and vfprintf (0xa7cf0: musl vfprintf 0x9aec0). *)
Definition pfcells (m : mem) : Prop :=
  rw_cells asegs m 0xad498 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa3200 [C8 (Z_to_bv 64 0x13e2e8)]
  /\ ro_cells asegs m 0x13e33c [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa4f98 [C8 (Z_to_bv 64 0x9a4ec)]
  /\ ro_cells asegs m 0xa4fa0 [C8 (Z_to_bv 64 0x973dc)].
Definition in_PFR (x : Z) : Prop :=
  (0xad498 <= x < 0xad499) \/ (0xa3200 <= x < 0xa3208) \/ (0x13e33c <= x < 0x13e33d) \/ (0xa4f98 <= x < 0xa4fa8).

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

(* printf_common (0x48d28), which both wrappers call with a0 = the wrapper's name, a1 = the format, a2 = the va_list:
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
        F (Z_to_bv 64 0x48174) fc None m (seg_rom asegs)).

(* The state at the printf_common call 0x44cd4 (jal, ra = 0x48cdc): the own frame of 48 bytes at usp - 48 holds
   [junk; ap; ap; s1; s0; ra]; s0 = fmt, s1 = ap; a0 = "vprintf" (0x1411e), a1 = fmt, a2 = ap. *)
Definition vpwA1_post (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x48128) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 a0 a1 (Z_to_bv 64 0x141ab) a0 a1
                  a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x48174) fc None m' (seg_rom asegs)
    /\ munch [(usp - 64, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [CB 8 junk; C8 a1; C8 a1; C8 s1; C8 s0; C8 ra].

(* From the trampoline 0x451bc (j 0x44c88) with a0 = fmt, a1 = ap: the frame, TryAsanInitFromRtl (returns 1),
   check_printf = 1, to the printf_common call. *)
Lemma vprintf_walkA1 : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> kImgEnd <= lo -> usp <= 2^47 -> pfcells m -> mem_inv asegs m ->
  evt asegs (vpwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ae0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH PFC MI. unfold kImgEnd in LOLO.
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  destruct PFC as (AI & GCF & CPF & RVP & RVF).
  carve_frame 48%nat ST. rename FR into FRv.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRv; [| reflexivity]. cbn [mk_CB_cells app] in FRv.
  xsteps_to 0x5de08%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0x48174%Z.
  apply evt_done. unfold vpwA1_post. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FRv].
Qed.

(* From printf_common's return 0x48cdc to the REAL(vprintf) call 0x44ce8 (jalr a2, a2 = musl vprintf 0x9dfd0 from the
   REAL cell 0xa7ce8; ra = 0x48cf0): a0 = s0 = fmt, a1 = ap from the frame. *)
Lemma vprintf_walkA2 : forall (usp : Z) (junk : list byte) (v ra0 c0 c1 : word)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  rw_cells asegs m (usp + -48) [CB 8 junk; C8 v; C8 v; C8 c1; C8 c0; C8 ra0] ->
  ro_cells asegs m 0xa4f98 [C8 (Z_to_bv 64 0x9a4ec)] ->
  usp <= 2^47 -> 48 <= usp -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' : word), ms' =
      MS (mkR (Z_to_bv 64 0x4813c) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 s0 v a2' a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x9a4ec) fc None m (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x48128) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros FRv RVP SPH SPL MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  do 5 lstep.
  apply evt_done. eexists. reflexivity.
Qed.

(* From the return 0x48cf0 of the REAL(vprintf) call to the caller: restores ra, s0, s1 from the frame, pops it and
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
        F (Z_to_bv 64 0x4813c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UT FRv MI.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  do 5 lstep.
  release_frame FRv ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.

(* The state at the REAL(vprintf) call: pc = musl vprintf 0x9dfd0, ra = 0x48cf0, sp = usp - 48, a0 = s0 = fmt,
   a1 = s1 = ap; the memory differs from the entry memory only in [usp - 2368, usp) (the frame, TryAsanInitFromRtl's
   and printf_common's windows); the frame holds [junk; ap; ap; s1; s0; ra]. *)
Definition vprintf_at_call (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x4813c) (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 a0 a1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x9a4ec) fc None m' (seg_rom asegs)
    /\ munch [(usp - 2368, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -48)
    /\ rw_cells asegs m' (usp + -48) [CB 8 junk; C8 a1; C8 a1; C8 s1; C8 s0; C8 ra].

Section WithPC.
Variable pc_pre : word -> word -> mem -> Prop.
Hypothesis PCOM : pcom_stmt pc_pre.

(* From the trampoline 0x451bc to the REAL(vprintf) call: vprintf_walkA1, printf_common (PCOM, its start premise in
   every memory that differs from the entry memory only in [usp - 64, usp)), vprintf_walkA2. *)
Lemma vprintf_walkA : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 2368 -> kHighShadowEnd + 8 <= lo -> usp <= 2^47 -> usp mod 16 = 0 -> pfcells m ->
  (forall m', munch [(usp - 64, usp)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> pc_pre a0 a1 m') ->
  mem_inv asegs m ->
  evt asegs (vprintf_at_call usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x43ae0) fc None m (seg_rom asegs)).
Proof using PCOM.
  intros until m. intros ST LO LOLO SPH S16 PFC PRE MI.
  pose proof LOLO as LOLO'. unfold kHighShadowEnd in LOLO'.
  pose proof PFC as (_ & _ & _ & RVP & _).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  eapply evt_cut; [apply (vprintf_walkA1 usp lo); [exact ST | lia | unfold kImgEnd; lia | exact SPH | exact PFC | exact MI] |].
  intros ms1 H1. unfold vpwA1_post in H1.
  destruct H1 as (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & -> & MU1 & WM1 & MI1
                  & ST1 & FR1).
  pose proof (PRE m1 MU1 WM1 MI1) as PRE1.
  assert (RVP1 : ro_cells asegs m1 0xa4f98 [C8 (Z_to_bv 64 0x9a4ec)]).
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
  assert (RVP2 : ro_cells asegs m2 0xa4f98 [C8 (Z_to_bv 64 0x9a4ec)]).
  { apply (ro_cells_transport asegs _ m1 m2 _ _ RVP1 MU2).
    cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I]. }
  replace (ret_pc (Z_to_bv 64 0x48128)) with (Z_to_bv 64 0x48128) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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
