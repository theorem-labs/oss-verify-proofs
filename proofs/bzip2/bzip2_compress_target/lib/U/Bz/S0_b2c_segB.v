(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 CmpSess CmpSessB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv BzWalkArith3 DecTacM CmpCarve S0_b2c_segA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import ZBridge.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_cmp_prep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpSessFast.   (* [comment removed for export] *)
Local Ltac slia ::= CmpSessFast.slia_sep_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Ltac wst := wstep; fix_lit_store.
Local Ltac simpl_arr_sizes ::= CmpFast.sas8_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section WRAP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dst dl src len wf0 nZ lo : Z) (qsp : Z).
  Notation usp := (bv_unsigned sp).
  Hypothesis HW : wrap_sec sp dl src len wf0 nZ lo qsp.
  Local Notation FRW := (S0_b2c_segA.FRW ra s0 s1 s2 s3 s4).
  Local Notation FRI := (S0_b2c_segA.FRI s5 s6 dst dl src len).
  Local Notation RETpost := (S0_b2c_segA.RETpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).

  Ltac prep :=
    pose proof HW as HW'; unfold wrap_sec in HW';
    cps_destruct HW' as (LEN & NZ & WF0 & WFE & ALQ & STK & LO & SPH & DL1 & DL2 & DL4 & SRC1 & SRC2);
    unfold CEIL, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, BZF_STRM, IMG_LO3, IMG_HI3 in *; bz_ceil; bz_params.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma G3a : forall m J (E r2 r3 : Z) (c40 : word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z -> (0 <= r3 < 2 ^ 64)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 r2) c40) -> mem_inv s0segs m ->
    evt s0segs (fun ms' => exists m',
                  ms' = MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                (Z_to_bv 64 r3) (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x13dbc) fc None m' (seg_rom s0segs)
                  /\ munch [(E + 40, E + 48)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
                  /\ rw_cells s0segs m' E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 r2) (Z_to_bv 64 r3)))
      (MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 r3) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13d20)) fc None m (seg_rom s0segs)).
  Proof.
    intros m J E r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 RR EH MI.
    prep. unfold EJ1w in EH.
    pose proof (munch_refl [(E + 40, E + 48)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13d20) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wst. wstep; try (if_cases K0; zify_cond_z K0; [|exfalso; clear -K0; apply K0; reflexivity]).
    finish. all: unfold EJ1w; assumption.
  Qed.

  Lemma G3b : forall m J jb (E r1 r2 r3 : Z) (c40 : word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z -> 
    (0 < r1 < 2 ^ 64)%Z -> (0 <= r2 < 2 ^ 64)%Z -> (0 <= r3 < 2 ^ 64)%Z -> (r2 = 0 \/ r3 = 0)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) ->
    rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (fun ms' => exists (xa2' : word) m',
                  ms' = MS (mkR (Z_to_bv 64 0x13dbc) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                (Z_to_bv 64 r1) (Z_to_bv 64 r1) xa2' xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x293c4) fc None m' (seg_rom s0segs)
                  /\ munch [(E + 40, E + 48)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
                  /\ rw_cells s0segs m' E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3))
                  /\ rw_cells s0segs m' (usp - 128) (FRW jb DBZA DBZF))
      (MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 r3) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13d20)) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E r1 r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 R1 R2 R3 RZ EH SM MI.
    prep. unfold EJ1w in EH. unfold FRW, DBZA, DBZF in SM.
    pose proof (munch_refl [(E + 40, E + 48)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13d20) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wst. wstep; if_cases K0; zify_cond_z K0; [exfalso; clear -K0 R1; lia|].
    wstep.
    assert (TAIL : forall xa2', evt s0segs (fun ms' => exists (xa2'' : word) m',
                  ms' = MS (mkR (Z_to_bv 64 0x13dbc) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                (Z_to_bv 64 r1) (Z_to_bv 64 r1) xa2'' xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x293c4) fc None m' (seg_rom s0segs)
                  /\ munch [(E + 40, E + 48)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
                  /\ rw_cells s0segs m' E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3))
                  /\ rw_cells s0segs m' (usp - 128) (FRW jb DBZA DBZF))
      (MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 r3) (Z_to_bv 64 r1) xa2' xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13db0) fc None m0 (seg_rom s0segs))).
    { intros xa2'.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep; if_cases K9; zify_cond_z K9; [exfalso; clear -K9 R1; lia|].
      wstep. wstep. finish. all: unfold EJ1w, FRW, DBZA, DBZF; assumption. }
    wstep; if_cases K1; zify_cond_z K1.
    - apply TAIL.
    - wstep; if_cases K2; zify_cond_z K2; [apply TAIL|]. exfalso. clear -K1 K2 RZ R2 R3. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma G4a : forall m J (E r1 r3 : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 0) (Z_to_bv 64 r3)) -> mem_inv s0segs m ->
    evt s0segs (fun ms' =>
                  ms' = MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                xa0 (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x13dd0) fc None m (seg_rom s0segs))
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13dbc) fc None m (seg_rom s0segs)).
  Proof.
    intros m J E r1 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 EH MI.
    prep. unfold EJ1w in EH.
    (* [comment removed for export] *)
    wstep. wstep; try (if_cases K0; zify_cond_z K0; [|exfalso; clear -K0; apply K0; reflexivity]).
    apply evt_done. reflexivity.
  Qed.

  Lemma G4b : forall m J jb (E r1 r2 r3 : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z -> (0 < r2 < 2 ^ 64)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3)) ->
    rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (fun ms' =>
                  ms' = MS (mkR (Z_to_bv 64 0x13dd0) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                (Z_to_bv 64 r2) (Z_to_bv 64 r2) (Z_to_bv 64 DBZF) xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x293c4) fc None m (seg_rom s0segs))
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13dbc) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E r1 r2 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 R2 EH SM MI.
    prep. unfold EJ1w in EH. unfold FRW, DBZA, DBZF in SM.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; clear -K0 R2; lia|].
    wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 R2; lia|].
    wstep. wstep. apply evt_done. unfold DBZF. reflexivity.
  Qed.

  Lemma G5a : forall m J (E r1 r2 : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 0)) -> mem_inv s0segs m ->
    evt s0segs (fun ms' =>
                  ms' = MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                xa0 (Z_to_bv 64 0) xa2 xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x13de4) fc None m (seg_rom s0segs))
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13dd0) fc None m (seg_rom s0segs)).
  Proof.
    intros m J E r1 r2 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 EH MI.
    prep. unfold EJ1w in EH.
    wstep. wstep; try (if_cases K0; zify_cond_z K0; [|exfalso; clear -K0; apply K0; reflexivity]).
    apply evt_done. reflexivity.
  Qed.

  Lemma G5b : forall m J jb (E r1 r2 r3 : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z -> (0 < r3 < 2 ^ 64)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 r3)) ->
    rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (fun ms' =>
                  ms' = MS (mkR (Z_to_bv 64 0x13de4) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                (Z_to_bv 64 r3) (Z_to_bv 64 r3) (Z_to_bv 64 DBZF) xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x293c4) fc None m (seg_rom s0segs))
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13dd0) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E r1 r2 r3 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 R3 EH SM MI.
    prep. unfold EJ1w in EH. unfold FRW, DBZA, DBZF in SM.
    wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; clear -K0 R3; lia|].
    wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 R3; lia|].
    wstep. wstep. apply evt_done. unfold DBZF. reflexivity.
  Qed.

  Lemma G6 : forall m jb (E : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z ->
    rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (fun ms' =>
                  ms' = MS (mkR (Z_to_bv 64 0x13df4) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                                (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 DBZF) xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x293c4) fc None m (seg_rom s0segs))
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13de4) fc None m (seg_rom s0segs)).
  Proof.
    intros m jb E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 xs6 RE1 RE2 SM MI.
    prep. unfold FRW, DBZA, DBZF in SM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 RE1; lia|].
    wstep. wstep. apply evt_done. unfold DBZF. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma G7 : forall m (jb : list byte) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 : word) (E : Z),
    rw_cells s0segs m (usp - 192) FRI -> rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) ->
    mem_inv s0segs m -> stk s0segs m lo (usp - 192) ->
    evt s0segs (RETpost (-3) [(usp - 192, usp)]%Z m)
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) xs6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x13df4) fc None m (seg_rom s0segs)).
  Proof.
    intros m jb xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 E FR2 FR MI ST. prep.
    unfold S0_b2c_segA.FRI in FR2. unfold S0_b2c_segA.FRW in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl [(usp - 192, usp)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    unfold WRET in FR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    try rewrite (ret_pc_even 0x15e9c) by (first [lia | reflexivity]).
    replace (usp - 192 + 64)%Z with (usp - 128)%Z by lia.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K1; zify_cond_z K1; [| exfalso; clear -K1; lia].
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    release_frame FR2 ST (bv_unsigned sp - 128)%Z. release_frame FR ST (bv_unsigned sp).
    replace (Z_to_bv 64 (usp - 128 + 128)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    unfold S0_b2c_segA.RETpost. finish.
    replace (Z_to_bv 64 18446744073709551613) with (Z_to_bv 64 (-3)) by (rewrite <- (Z_to_bv_mod64 (-3)); reflexivity). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition EFIN (J : list byte) (E r1 r2 r3 : Z) : list cell :=
    [C8 (Z_to_bv 64 (usp - 128)); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 2); C4 (jw4 J 16); C4 (jw4 J 20);
     C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3); C4 (jw4 J 48); C4 (jw4 J 52);
     C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 0);
     C4 (Z_to_bv 64 WORKFACTOR); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 0); C4 (jw4 J 100); C4 (jw4 J 104);
     C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 NBLOCKMAX); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (jw4 J 124)].
  Definition EFIN2 (J : list byte) : list cell :=
    [C4 (jw4 J 640); C4 (jw4 J 644); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1);
     C4 (Z_to_bv 64 BLOCKSIZE100K); C4 (jw4 J 668)].
  (* [comment removed for export] *)
  Definition STRMW (jb : list byte) (E : Z) : list cell :=
    [C8 (Z_to_bv 64 src); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (jw4 jb 20);
     C8 (Z_to_bv 64 dst); C4 (Z_to_bv 64 nZ); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (jw4 jb 44);
     C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 DBZA); C8 (Z_to_bv 64 DBZF); C8 (Z_to_bv 64 0)].
  (* [comment removed for export] *)
  Definition FRWR : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition Tpost (J jb : list byte) (E r1 r2 r3 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x15ecc) (Z_to_bv 64 (usp - 128)) gp tp t0' t1' t2' (Z_to_bv 64 dl) (Z_to_bv 64 0)
                    (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 2) a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13ea0) fc None m' (seg_rom s0segs)
      /\ munch [(usp - 192, usp); (E, E + 384); (E + 640, E + 672)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m' /\ stk s0segs m' lo (usp - 128)
      /\ rw_cells s0segs m' E (EFIN J E r1 r2 r3)
      /\ u8arr s0segs m' (E + 128) (repeat (Z_to_bv 8 0) 256)
      /\ rw_cells s0segs m' (E + 640) (EFIN2 J)
      /\ rw_cells s0segs m' (usp - 128) (STRMW jb E)
      /\ rw_cells s0segs m' (usp - 48) FRWR.
  Lemma T : forall m J jb (E r1 r2 r3 : Z) (c40 : word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 : word),
    (0 < E)%Z -> (E mod 16 = 0)%Z -> (E + 55768 <= CEIL)%Z -> (0 < r1 < 2 ^ 64)%Z -> (0 < r2 < 2 ^ 64)%Z -> (0 < r3 < 2 ^ 64)%Z -> Z.of_nat (length jb) = 56%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) c40) ->
    u8arr s0segs m (E + 128) (ovb znew (jseg J 128 256) 256) ->
    rw_cells s0segs m (E + 640) (EJ2 J) ->
    rw_cells s0segs m (usp - 192) FRI -> rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> rw_cells s0segs m dl [C4 (Z_to_bv 64 nZ)] ->
    mem_inv s0segs m -> stk s0segs m lo (usp - 192) ->
    evt s0segs (Tpost J jb E r1 r2 r3 m)
      (MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 r3) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) xs5 (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13d20)) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E r1 r2 r3 c40 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xs5 RE1 RE16 RE2 R1 R2 R3 LJB EH INU EH2 FR2 FR DLC MI ST.
    prep. unfold EJ1w in EH. unfold EJ2 in EH2. cbn [jcells jcell ESHAPE2 Nat.eqb] in EH2. zlit_in EH2.
    apply (DecTacM.rw_cells_C8_split s0segs m (E + 640) [C4 (jw4 J 640); C4 (jw4 J 644)]) in EH2. cbn [app] in EH2.
    assert (LE7 : Z.land E 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide E 8 ltac:(lia))).
      exists (2 * (E / 16))%Z. pose proof (Z.div_mod E 16 ltac:(lia)) as DM. lia. }
    assert (LD3 : Z.land dl 3 = 0%Z).
    { change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact DL4. }
    unfold S0_b2c_segA.FRI, WRET in FR2. unfold S0_b2c_segA.FRW in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (ovb_length znew (jseg J 128 256) 256 ltac:(lia)) as INUL.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_cons_iff _ _ _ _ _)) in FR. destruct FR as [SJ FRr]. cbn [csize] in FRr.
    assert (SJ' : rw_cells s0segs m (usp - 128) (jcells jb 0 [8; 4; 4; 4; 4; 8; 4; 4; 4; 4; 8]%nat)).
    { eapply carve_cb; [exact SJ | apply jcells_wf; cbn; lia | rewrite jcells_bytes by (cbn; lia); cbn [sum_nat Nat.add]; apply jseg_all; exact LJB | rewrite jcells_size; reflexivity]. }
    clear SJ. cbn [jcells jcell Nat.eqb] in SJ'.
    replace (0 + 8)%Z with 8%Z in SJ' by reflexivity. replace (8 + 4)%Z with 12%Z in SJ' by reflexivity. replace (12 + 4)%Z with 16%Z in SJ' by reflexivity.
    replace (16 + 4)%Z with 20%Z in SJ' by reflexivity. replace (20 + 4)%Z with 24%Z in SJ' by reflexivity. replace (24 + 8)%Z with 32%Z in SJ' by reflexivity.
    replace (32 + 4)%Z with 36%Z in SJ' by reflexivity. replace (36 + 4)%Z with 40%Z in SJ' by reflexivity. replace (40 + 4)%Z with 44%Z in SJ' by reflexivity.
    replace (44 + 4)%Z with 48%Z in SJ' by reflexivity.
    pose proof (munch_refl [(usp - 192, usp); (E, E + 384); (E + 640, E + 672)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13d20) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wst.
    wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 R1; lia|].
    wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2 R2; lia|].
    wstep; if_cases K3; zify_cond_z K3; [exfalso; clear -K3 R3; lia|].
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    wst. wst. wst. wst.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wst. wst. wst. wst. wst. wst. wst. wst. wst.
    (* [comment removed for export] *)
    wst. wst. wst. wst. wst.
    (* [comment removed for export] *)
    wstep. wstep.
    wstep. rewrite LE7. wstep; notrap.
    wst. wst. wst. wstep. wstep. wst.
    reword_C4 EH2 2%nat 4294967295%Z. { reflexivity. }
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U0_cmp_prep.prep_loop _ E (jseg J 128 256) gp tp F fc RE1 ltac:(lia) mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 256%nat 0%Z znew mm);
      [st_eq | cbn; lia | reflexivity | lia | exact INU | assumption | apply munch_refl | apply wmono_refl |] end.
    clear INU. intros m' x11 x12 INU MI' MUl WMl.
    lazymatch type of MUl with munch _ ?ma ?mb =>
      transport_after_call s0segs ma mb MUl WMl; try (match goal with H : mem_inv _ ma |- _ => clear H end) end.
    clear MUl WMl. rewrite ovb_inUse_clear in INU.
    wstep. wstep. wstep; notrap. wst. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    do 10 wstep.
    replace (usp - 192 + 64)%Z with (usp - 128)%Z by lia.
    lazymatch goal with H : stk _ _ _ _ |- _ => release_frame FR2 H (usp - 128)%Z end.
    try (rewrite (ret_pc_even 0x15e9c) by (first [lia | reflexivity])).
    (* [comment removed for export] *)
    wstep. wstep; if_cases K4; zify_cond_z K4; [exfalso; clear -K4; lia|].
    wstep. rewrite LD3. wst. wst. wst. wstep; notrap. wstep. wst. wstep. wstep. wstep.
    (* [comment removed for export] *)
    match goal with H : rw_cells s0segs ?mm E _ |- _ =>
      apply (DecTacM.rw_cells_C8_split s0segs mm E [C8 (Z_to_bv 64 (usp - 128))]) in H; cbn [app] in H;
      rewrite unsigned_lit in H by lia; cell_mod32 H 8%nat end.
    replace (0 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z with 20%Z in SJ' by reflexivity.
    replace (0 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z with 44%Z in SJ' by reflexivity.
    lazymatch goal with H : rw_cells s0segs ?mm (usp - 128 + Z.of_nat 56)%Z _ |- _ => rename H into FRr' end.
    lazymatch type of FRr' with rw_cells s0segs ?mm _ _ =>
      apply (proj1 (DecTac2.rw_cells_app_iff s0segs mm _ [C8 (Z_to_bv 64 DBZA); C8 (Z_to_bv 64 DBZF); C8 (Z_to_bv 64 0)] _)) in FRr' end.
    destruct FRr' as [FRa FRb]. cbn [cells_size csize Nat.add] in FRb.
    replace (usp - 128 + Z.of_nat 56 + Z.of_nat 24)%Z with (usp - 48)%Z in FRb by lia.
    lazymatch type of SJ' with rw_cells s0segs ?mm ?A ?cs =>
      pose proof (proj2 (DecTac2.rw_cells_app_iff s0segs mm A cs [C8 (Z_to_bv 64 DBZA); C8 (Z_to_bv 64 DBZF); C8 (Z_to_bv 64 0)])
                    (conj SJ' ltac:(cbn [cells_size csize Nat.add]; exact FRa))) as STR end.
    cbn [app] in STR. clear SJ' FRa.
    unfold Tpost, EFIN, EFIN2, STRMW, FRWR. finish.
  Qed.
End WRAP.
End ACeilS1.
