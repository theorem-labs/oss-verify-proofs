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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 CmpSess CmpSessB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv BzWalkArith3 DecTacM CmpCarve.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import ZBridge.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
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

(* [comment removed for export] *)
Definition WRET : Z := 0x15e9c.      (* [comment removed for export] *)
Definition DBZA : Z := 0x13e24.      (* [comment removed for export] *)
Definition DBZF : Z := 0x13e3c.      (* [comment removed for export] *)
Definition MALLOC : Z := 0x29504.
Definition FREE : Z := 0x293c4.

Section WRAP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dst dl src len wf0 nZ lo : Z) (qsp : Z).
  Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition wrap_sec : Prop :=
    (0 <= len < 2 ^ 26)%Z /\ (nZ = len + 600 + len / 100)%Z /\ (0 <= wf0 <= 250)%Z /\ (WORKFACTOR = (if wf0 =? 0 then 30 else wf0))%Z /\
    (usp = 16 * qsp)%Z /\ (lo + 17408 <= usp)%Z /\ (CEIL <= lo)%Z /\ (usp + 48 <= 2 ^ 47)%Z /\
    (usp <= dl)%Z /\ (dl + 4 <= 2 ^ 64)%Z /\ (dl mod 4 = 0)%Z /\ (0 < src)%Z /\ (src + len <= CEIL)%Z.
  Hypothesis HW : wrap_sec.

  Ltac prep :=
    pose proof HW as HW'; unfold wrap_sec in HW';
    cps_destruct HW' as (LEN & NZ & WF0 & WFE & ALQ & STK & LO & SPH & DL1 & DL2 & DL4 & SRC1 & SRC2);
    unfold CEIL, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, BZF_STRM, IMG_LO3, IMG_HI3 in *; bz_ceil; bz_params.

  (* [comment removed for export] *)
  Definition FRW (jb : list byte) (bza bzf : Z) : list cell :=
    [CB 56 jb; C8 (Z_to_bv 64 bza); C8 (Z_to_bv 64 bzf); C8 (Z_to_bv 64 0); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition FRI : list cell :=
    [C8 s6; C8 s5; C8 (Z_to_bv 64 src); C8 (Z_to_bv 64 dst); C8 (Z_to_bv 64 len); C8 (Z_to_bv 64 (-2)); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 WRET)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition W1apost (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom s0segs)
      /\ a0' = Z_to_bv 64 (-2)
      /\ munch [(usp - 128, usp)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m' /\ stk s0segs m' lo usp.
  Lemma W1a : forall m (t0 t1 t2 a7 t3 t4 t5 t6 : word),
    dst = 0%Z -> mem_inv s0segs m -> stk s0segs m lo usp ->
    evt s0segs (W1apost m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 dl) (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 BLOCKSIZE100K)
               (Z_to_bv 64 0) (Z_to_bv 64 wf0) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15e1c) fc None m (seg_rom s0segs)).
  Proof.
    intros m t0 t1 t2 a7 t3 t4 t5 t6 D0 MI ST. prep. subst dst.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl [(usp - 128, usp)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    carve_frame 128%nat ST.
    wst. wst. wst. wst. wst. wst. wst.
    replace (usp + -128)%Z with (usp - 128)%Z in * by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 WF0; lia|].
    wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2; lia|].
    wstep; if_cases K3; zify_cond_z K3; [| exfalso; clear -K3; lia].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    release_frame FR ST (bv_unsigned sp).
    replace (Z_to_bv 64 (usp - 128 + 128)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    unfold W1apost. finish.
    replace (Z_to_bv 64 18446744073709551614) with (Z_to_bv 64 (-2)) by (rewrite <- (Z_to_bv_mod64 (-2)); reflexivity). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wf_fix : forall m (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    evt s0segs (fun ms' => ms' = MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 WORKFACTOR) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                      F (Z_to_bv 64 0x15e7c) fc None m (seg_rom s0segs))
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 wf0) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x15e74) fc None m (seg_rom s0segs)).
  Proof.
    intros. prep.
    wstep; if_cases K7; zify_cond_z K7.
    - replace (Z_to_bv 64 wf0) with (Z_to_bv 64 WORKFACTOR)
        by (rewrite WFE; replace (wf0 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      apply evt_done. reflexivity.
    - wstep. replace (Z_to_bv 64 30) with (Z_to_bv 64 WORKFACTOR)
        by (rewrite WFE; replace (wf0 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition W1bpost (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (jb : list byte),
      ms' = MS (mkR (Z_to_bv 64 0x13ca0) (Z_to_bv 64 (usp - 192)) gp tp t0' t1' t2' (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                    (Z_to_bv 64 55768) (Z_to_bv 64 55768) (Z_to_bv 64 1) (Z_to_bv 64 DBZA) a4' a5' a6' a7'
                    (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 MALLOC) fc None m' (seg_rom s0segs)
      /\ munch [(usp - 192, usp)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m' /\ stk s0segs m' lo (usp - 192)
      /\ rw_cells s0segs m' (usp - 192) FRI /\ rw_cells s0segs m' (usp - 128) (FRW jb DBZA DBZF).
  Lemma W1b : forall m (t0 t1 t2 a7 t3 t4 t5 t6 : word),
    dst <> 0%Z -> (0 < dst < 2 ^ 64)%Z -> mem_inv s0segs m -> stk s0segs m lo usp ->
    evt s0segs (W1bpost m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 dl) (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 BLOCKSIZE100K)
               (Z_to_bv 64 0) (Z_to_bv 64 wf0) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15e1c) fc None m (seg_rom s0segs)).
  Proof.
    intros m t0 t1 t2 a7 t3 t4 t5 t6 D0 DR MI ST. prep.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl [(usp - 192, usp)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    carve_frame 128%nat ST.
    wst. wst. wst. wst. wst. wst. wst.
    replace (usp + -128)%Z with (usp - 128)%Z in * by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 WF0; lia|].
    wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2; lia|].
    wstep; if_cases K3; zify_cond_z K3; [exfalso; clear -K3 D0 DR; lia|].
    (* [comment removed for export] *)
    wstep. wstep; if_cases K4; zify_cond_z K4; [exfalso; clear -K4 DL1 LONN STK LO; lia|].
    wstep. wstep; if_cases K5; zify_cond_z K5; [exfalso; clear -K5 SRC1 SRC2; lia|].
    wstep. wstep. wstep; if_cases K6; zify_cond_z K6; [exfalso; clear -K6 BZbsL__ BZbsH__; change 18446744073709551615%Z with (Z.ones 64) in K6; rewrite Z.land_ones in K6 by lia; mlia|].
    wstep.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply wf_fix|]. intros ms' ->.
    (* [comment removed for export] *)
    wst. wst. wst. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    replace (usp - 128)%Z with (usp + -128)%Z in * by lia.
    carve_frame 64%nat ST.
    do 9 wst.
    replace (usp + -128 + -64)%Z with (usp - 192)%Z in * by lia. replace (usp + -128)%Z with (usp - 128)%Z in * by lia.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K8; zify_cond_z K8; [exfalso; clear -K8 LONN STK LO; lia|].
    wstep. wstep. wstep. wstep. wstep; if_cases K9; zify_cond_z K9; [exfalso; clear -K9 BZbsL__ BZbsH__; change 18446744073709551615%Z with (Z.ones 64) in K9; rewrite Z.land_ones in K9 by lia; mlia|].
    wstep. wstep. wstep; if_cases K10; zify_cond_z K10; [exfalso; clear -K10 BZwfL__ BZwfH__; mlia|].
    wstep. wstep; if_cases K11; zify_cond_z K11; [|exfalso; clear -K11 BZwfL__ BZwfH__; mlia].
    assert (LA7 : Z.land (usp - 128) 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide (usp - 128) 8 ltac:(lia))).
      exists (2 * qsp - 16)%Z. lia. }
    wstep. rewrite LA7. wstep; notrap.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K12; zify_cond_z K12; [exfalso; clear -K12; lia|].
    wstep. wstep. wst.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K13; zify_cond_z K13; [exfalso; clear -K13; lia|].
    wstep. wstep. wst.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep; notrap. wstep. wstep.
    unfold W1bpost. finish.
    all: first [ unfold FRI; replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 18446744073709551614) by (rewrite <- (Z_to_bv_mod64 (-2)); reflexivity); eassumption
               | unfold FRW, DBZA, DBZF; eassumption
               | match goal with |- ?g => idtac "LEFT:" g end ].
  Qed.

  (* [comment removed for export] *)
  Definition EJ1w (J : list byte) (c0 c24 c32 c40 : word) : list cell :=
    [C8 c0; C8 (jw8 J 8); C4 (jw4 J 16); C4 (jw4 J 20); C8 c24; C8 c32; C8 c40; C4 (jw4 J 48); C4 (jw4 J 52);
     C8 (jw8 J 56); C8 (jw8 J 64); C8 (jw8 J 72); C8 (jw8 J 80); C4 (jw4 J 88); C4 (jw4 J 92); C4 (jw4 J 96); C4 (jw4 J 100);
     C4 (jw4 J 104); C4 (jw4 J 108); C4 (jw4 J 112); C4 (jw4 J 116); C4 (jw4 J 120); C4 (jw4 J 124)].

  (* [comment removed for export] *)
  Definition RETpost (rc : Z) (W : list (Z * Z)) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom s0segs)
      /\ a0' = Z_to_bv 64 rc
      /\ munch W m m' /\ wmono s0segs m m' /\ mem_inv s0segs m' /\ stk s0segs m' lo usp.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma W2f : forall m (jb : list byte) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    rw_cells s0segs m (usp - 192) FRI -> rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) ->
    mem_inv s0segs m -> stk s0segs m lo (usp - 192) ->
    evt s0segs (RETpost (-3) [(usp - 192, usp)]%Z m)
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13ca0)) fc None m (seg_rom s0segs)).
  Proof.
    intros m jb xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 FR2 FR MI ST. prep.
    unfold FRI in FR2. unfold FRW in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl [(usp - 192, usp)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13ca0) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wstep; if_cases K0; zify_cond_z K0; [| exfalso; clear -K0; lia].
    unfold WRET in FR2.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    try rewrite (ret_pc_even 0x15e9c) by (first [lia | reflexivity]).
    replace (usp - 192 + 64)%Z with (usp - 128)%Z by lia.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K1; zify_cond_z K1; [| exfalso; clear -K1; lia].
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    release_frame FR2 ST (bv_unsigned sp - 128)%Z. release_frame FR ST (bv_unsigned sp).
    replace (Z_to_bv 64 (usp - 128 + 128)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    unfold RETpost. finish.
    replace (Z_to_bv 64 18446744073709551613) with (Z_to_bv 64 (-3)) by (rewrite <- (Z_to_bv_mod64 (-3)); reflexivity). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition W2post (J jb : list byte) (E : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x13ce4) (Z_to_bv 64 (usp - 192)) gp tp t0' t1' t2' (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                    (Z_to_bv 64 ARR1_SIZE) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 MALLOC) fc None m' (seg_rom s0segs)
      /\ munch [(E, E + 48)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
      /\ rw_cells s0segs m' E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
      /\ rw_cells s0segs m' (usp - 128) (FRW jb DBZA DBZF).
  Lemma W2 : forall m J jb (E : Z) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    (0 < E)%Z -> (E mod 16 = 0)%Z -> (E + 55768 <= CEIL)%Z ->
    rw_cells s0segs m E (EJ1 J) -> rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (W2post J jb E m)
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 E) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 dst) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13ca0)) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 RE1 RE16 RE2 EH FR MI.
    prep. unfold EJ1 in EH. cbn [jcells jcell ESHAPE1 Nat.eqb] in EH. zlit_in EH. unfold FRW, DBZA, DBZF in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (munch_refl [(E, E + 48)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13ca0) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; clear -K0 RE1; lia|].
    assert (LE7 : Z.land E 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide E 8 ltac:(lia))).
      exists (2 * (E / 16))%Z. pose proof (Z.div_mod E 16 ltac:(lia)) as DM. lia. }
    wstep. wstep. rewrite LE7. wstep; notrap. wst. wst. wst. wst.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. bz32. wstep. wstep. wstep. wstep. wstep. bz32. rewrite ?Z.mul_1_l. wstep; notrap. wstep. wstep. rewrite ?Z.mul_1_r, ?Z.add_0_r.
    replace (Z_to_bv 64 18446744073709551613) with (Z_to_bv 64 (-3)) by (rewrite <- (Z_to_bv_mod64 (-3)); reflexivity).
    unfold W2post, EJ1w, FRW, DBZA, DBZF, MALLOC. finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition W3post (J jb : list byte) (E r1 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x13d00) (Z_to_bv 64 (usp - 192)) gp tp t0' t1' t2' (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                    (Z_to_bv 64 ARR2_SIZE) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 MALLOC) fc None m' (seg_rom s0segs)
      /\ munch [(E + 24, E + 32)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
      /\ rw_cells s0segs m' E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 0) (Z_to_bv 64 0))
      /\ rw_cells s0segs m' (usp - 128) (FRW jb DBZA DBZF).
  Lemma W3 : forall m J jb (E r1 : Z) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z -> (0 <= r1 < 2 ^ 64)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (W3post J jb E r1 m)
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 r1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13ce4)) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E r1 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 RE1 RE2 RR EH FR MI.
    prep. unfold EJ1w in EH. unfold FRW, DBZA, DBZF in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (munch_refl [(E + 24, E + 32)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13ce4) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wstep. wst. wstep. bz32. wstep. wstep. wstep. wstep. wstep. bz32. rewrite ?Z.mul_1_l. wstep; notrap. wstep. wstep. rewrite ?Z.mul_1_r, ?Z.add_0_r.
    unfold W3post, EJ1w, FRW, DBZA, DBZF, MALLOC. finish.
  Qed.

  Definition W4post (J jb : list byte) (E r1 r2 : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (Z_to_bv 64 0x13d20) (Z_to_bv 64 (usp - 192)) gp tp t0' t1' t2' (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
                    (Z_to_bv 64 262148) a1' a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 MALLOC) fc None m' (seg_rom s0segs)
      /\ munch [(E + 32, E + 40)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
      /\ rw_cells s0segs m' E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 0))
      /\ rw_cells s0segs m' (usp - 128) (FRW jb DBZA DBZF).
  Lemma W4 : forall m J jb (E r1 r2 : Z) (xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    (0 < E)%Z -> (E + 55768 <= CEIL)%Z -> (0 <= r2 < 2 ^ 64)%Z ->
    rw_cells s0segs m E (EJ1w J (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 r1) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
    rw_cells s0segs m (usp - 128) (FRW jb DBZA DBZF) -> mem_inv s0segs m ->
    evt s0segs (W4post J jb E r1 r2 m)
      (MS (mkR xra (Z_to_bv 64 (usp - 192)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 WORKFACTOR)
               (Z_to_bv 64 r2) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 BLOCKSIZE100K) (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 (-3)) (Z_to_bv 64 ARR1_SIZE) s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x13d00)) fc None m (seg_rom s0segs)).
  Proof.
    intros m J jb E r1 r2 xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 RE1 RE2 RR EH FR MI.
    prep. unfold EJ1w in EH. unfold FRW, DBZA, DBZF in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (munch_refl [(E + 32, E + 40)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x13d00) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wstep. wst. wstep. wstep. wstep. wstep. wstep. wstep. wstep. bz32. rewrite ?Z.mul_1_l. wstep; notrap. wstep. wstep. rewrite ?Z.mul_1_r, ?Z.add_0_r.
    unfold W4post, EJ1w, FRW, DBZA, DBZF, MALLOC. finish.
  Qed.

End WRAP.
End ACeilS1.
