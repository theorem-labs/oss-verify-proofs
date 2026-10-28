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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0_b2c_segB.
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

Section WRAP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (dst dl src len wf0 nZ lo : Z) (qsp : Z).
  Notation usp := (bv_unsigned sp).
  Hypothesis HW : wrap_sec sp dl src len wf0 nZ lo qsp.
  Local Notation RETpost := (S0_b2c_segA.RETpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo).
  Local Notation FRWR := (S0_b2c_segB.FRWR ra s0 s1 s2 s3 s4).

  Ltac prep :=
    pose proof HW as HW'; unfold wrap_sec in HW';
    cps_destruct HW' as (LEN & NZ & WF0 & WFE & ALQ & STK & LO & SPH & DL1 & DL2 & DL4 & SRC1 & SRC2);
    unfold CEIL, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, BZF_STRM, IMG_LO3, IMG_HI3 in *; bz_ceil; bz_params.

  (* [comment removed for export] *)
  Definition STRMX (w0 : word) (w1 w2 w3 w4 : word) (w5 : word) (avo : Z) (w7 w8 w9 : word) (E : Z) : list cell :=
    [C8 w0; C4 w1; C4 w2; C4 w3; C4 w4; C8 w5; C4 (Z_to_bv 64 avo); C4 w7; C4 w8; C4 w9;
     C8 (Z_to_bv 64 E); C8 (Z_to_bv 64 DBZA); C8 (Z_to_bv 64 DBZF); C8 (Z_to_bv 64 0)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma RC3 : forall m (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x15f04) (Z_to_bv 64 (usp - 128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 dl) (Z_to_bv 64 (-8))
                                         (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 3) xa2 xa3 xa4 xa5 xa6 xa7
                                         (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                                    F (Z_to_bv 64 0x14528) fc None m (seg_rom s0segs))
      (MS (mkR (Z_to_bv 64 0x15ecc) (Z_to_bv 64 (usp - 128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 dl) (Z_to_bv 64 0)
               (Z_to_bv 64 3) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x15ecc)) fc None m (seg_rom s0segs)).
  Proof.
    intros. prep. rewrite (ret_pc_even 0x15ecc) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wstep; if_cases K1; zify_cond_z K1; [| exfalso; clear -K1; lia].
    wstep. wstep. wstep.
    replace (Z_to_bv 64 18446744073709551608) with (Z_to_bv 64 (-8)) by (rewrite <- (Z_to_bv_mod64 (-8)); reflexivity).
    apply evt_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma RC4 : forall m (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (w0 w1 w2 w3 w4 w5 w7 w8 w9 : word) (avo E : Z),
    mem_inv s0segs m -> (0 <= avo <= nZ)%Z ->
    rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E) -> rw_cells s0segs m dl [C4 (Z_to_bv 64 nZ)] ->
    evt s0segs (fun ms' => exists (xa1' : word) m',
                  ms' = MS (mkR (Z_to_bv 64 0x15f04) (Z_to_bv 64 (usp - 128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 dl) (Z_to_bv 64 0)
                                (Z_to_bv 64 (usp - 128)) xa1' xa2 xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 0x14528) fc None m' (seg_rom s0segs)
                  /\ munch [(dl, dl + 4)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
                  /\ rw_cells s0segs m' (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E) /\ rw_cells s0segs m' dl [C4 (Z_to_bv 64 (nZ - avo))])
      (MS (mkR (Z_to_bv 64 0x15ecc) (Z_to_bv 64 (usp - 128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 dl) (Z_to_bv 64 0)
               (Z_to_bv 64 4) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (ret_pc (Z_to_bv 64 0x15ecc)) fc None m (seg_rom s0segs)).
  Proof.
    intros until E. intros MI AVO SM DLC. prep. unfold STRMX in SM.
    pose proof (rw_cells_bound _ _ _ _ SM) as SMB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SMB.
    pose proof (munch_refl [(dl, dl + 4)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    rewrite (ret_pc_even 0x15ecc) by (first [lia | reflexivity]).
    (* [comment removed for export] *)
    wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1; lia|].
    wstep. wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2; lia|].
    wstep. wstep. wstep. wstep. bz32. wst. wstep. wstep. wstep.
    finish.
    all: try (unfold STRMX; eassumption).
  Qed.

  (* [comment removed for export] *)
  Definition FRE (j8 : list byte) (rc : Z) : list cell := [CB 8 j8; C8 (Z_to_bv 64 rc); C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 0x15f04)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma E1 : forall m (cx : cctx) (g : eg) (e : est) (rc avo : Z) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (w0 w1 w2 w3 w4 w5 w7 w8 w9 : word),
    (c_bz cx + 5016 = usp - 128)%Z -> (0 < c_E cx)%Z -> (c_E cx mod 16 = 0)%Z -> (c_E cx + 55768 <= CEIL)%Z -> (0 < c_A1 cx < 2 ^ 64)%Z ->
    rw_cells s0segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 (c_E cx)) ->
    mem_inv s0segs m -> stk s0segs m lo (usp - 128) ->
    evt s0segs (fun ms' => exists (xa2' : word) m' (j8 : list byte),
                  ms' = MS (mkR (Z_to_bv 64 0x14578) (Z_to_bv 64 (usp - 160)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 (c_E cx))
                                (Z_to_bv 64 (c_A1 cx)) (Z_to_bv 64 (c_A1 cx)) xa2' xa3 xa4 xa5 xa6 xa7
                                (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                           F (Z_to_bv 64 FREE) fc None m' (seg_rom s0segs)
                  /\ munch [(usp - 160, usp - 128)]%Z m m' /\ wmono s0segs m m' /\ mem_inv s0segs m' /\ stk s0segs m' lo (usp - 160)
                  /\ rw_cells s0segs m' (usp - 160) (FRE j8 rc)
                  /\ rw_cells s0segs m' (c_E cx) (EHEAD1 cx g e) /\ rw_cells s0segs m' (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 (c_E cx)))
      (MS (mkR (Z_to_bv 64 0x15f04) (Z_to_bv 64 (usp - 128)) gp tp xt0 xt1 xt2 (Z_to_bv 64 dl) (Z_to_bv 64 rc)
               (Z_to_bv 64 (usp - 128)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x14528) fc None m (seg_rom s0segs)).
  Proof.
    intros until w9. intros SA RE1 RE16 RE2 RA1 EH SM MI ST. prep. unfold EHEAD1 in EH. unfold BZF_STRM in EH. rewrite SA in EH. unfold STRMX, DBZA, DBZF in SM.
    assert (LE7 : Z.land (c_E cx) 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide (c_E cx) 8 ltac:(lia))).
      exists (2 * (c_E cx / 16))%Z. pose proof (Z.div_mod (c_E cx) 16 ltac:(lia)) as DM. lia. }
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl [(usp - 160, usp - 128)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    replace (usp - 128)%Z with (usp + -128)%Z in * by lia.
    carve_frame 32%nat ST.
    (* [comment removed for export] *)
    wstep. wst. wst. wst. wstep. wstep.
    replace (usp + -128 + -32)%Z with (usp - 160)%Z in * by lia. replace (usp + -128)%Z with (usp - 128)%Z in * by lia.
    wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 LONN STK LO; lia|].
    assert (LS7 : Z.land (usp - 128) 7 = 0%Z).
    { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide (usp - 128) 8 ltac:(lia))).
      exists (2 * qsp - 16)%Z. lia. }
    wstep. rewrite LS7. wstep; notrap.
    wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2 RE1; lia|].
    wstep. rewrite LE7. wstep; notrap.
    wstep. wstep; if_cases K3; zify_cond_z K3; [exfalso; clear -K3; lia|].
    (* [comment removed for export] *)
    wstep. wstep; if_cases K4; zify_cond_z K4; [exfalso; clear -K4 RA1; lia|].
    wstep. wstep. wstep. wstep; if_cases K5; zify_cond_z K5; [exfalso; clear -K5 RA1; lia|].
    wstep. wstep.
    replace (usp + -160)%Z with (usp - 160)%Z in * by lia.
    unfold FRE, EHEAD1, STRMX, DBZA, DBZF, FREE. unfold BZF_STRM. rewrite SA. finish. all: eassumption.
  Qed.

  (* [comment removed for export] *)
  Local Notation EST pc ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 E m :=
    (MS (mkR ra0 (Z_to_bv 64 (usp - 160)) gp tp t0 t1 t2 (Z_to_bv 64 (usp - 128)) (Z_to_bv 64 E)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma E2 : forall m (cx : cctx) (g : eg) (e : est) (avo : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (w0 w1 w2 w3 w4 w5 w7 w8 w9 : word),
    (0 < c_E cx)%Z -> (c_E cx + 55768 <= CEIL)%Z -> (0 < c_A2 cx < 2 ^ 64)%Z ->
    rw_cells s0segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 (c_E cx)) -> mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = EST FREE (Z_to_bv 64 0x1458c) xt0 xt1 xt2 (Z_to_bv 64 (c_A2 cx)) (Z_to_bv 64 (c_A2 cx)) (Z_to_bv 64 DBZF) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (c_E cx) m)
      (EST 0x14578 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (c_E cx) m).
  Proof.
    intros until w9. intros RE1 RE2 RA2 EH SM MI. prep. unfold EHEAD1 in EH. unfold STRMX, DBZA, DBZF in SM.
    (* [comment removed for export] *)
    wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; clear -K0 RA2; lia|].
    wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 RA2; lia|].
    wstep. wstep. apply evt_done. unfold DBZF, FREE. reflexivity.
  Qed.
  Lemma E3 : forall m (cx : cctx) (g : eg) (e : est) (avo : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (w0 w1 w2 w3 w4 w5 w7 w8 w9 : word),
    (0 < c_E cx)%Z -> (c_E cx + 55768 <= CEIL)%Z -> (0 < c_FT cx < 2 ^ 64)%Z ->
    rw_cells s0segs m (c_E cx) (EHEAD1 cx g e) -> rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 (c_E cx)) -> mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = EST FREE (Z_to_bv 64 0x145a0) xt0 xt1 xt2 (Z_to_bv 64 (c_FT cx)) (Z_to_bv 64 (c_FT cx)) (Z_to_bv 64 DBZF) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (c_E cx) m)
      (EST 0x1458c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (c_E cx) m).
  Proof.
    intros until w9. intros RE1 RE2 RFT EH SM MI. prep. unfold EHEAD1 in EH. unfold STRMX, DBZA, DBZF in SM.
    wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; clear -K0 RFT; lia|].
    wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 RFT; lia|].
    wstep. wstep. apply evt_done. unfold DBZF, FREE. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma E4 : forall m (E avo : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (w0 w1 w2 w3 w4 w5 w7 w8 w9 : word),
    (0 < E < 2 ^ 64)%Z ->
    rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E) -> mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = EST FREE (Z_to_bv 64 0x145b0) xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 DBZF) xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 E m)
      (EST 0x145a0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 E m).
  Proof.
    intros until w9. intros RE SM MI. prep. unfold STRMX, DBZA, DBZF in SM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1 RE; lia|].
    wstep. wstep. apply evt_done. unfold DBZF, FREE. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma E5 : forall m (E avo rc : Z) (j8 : list byte) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (w0 w1 w2 w3 w4 w5 w7 w8 w9 : word),
    rw_cells s0segs m (usp - 128) (STRMX w0 w1 w2 w3 w4 w5 avo w7 w8 w9 E) -> rw_cells s0segs m (usp - 160) (FRE j8 rc) -> rw_cells s0segs m (usp - 48) FRWR ->
    mem_inv s0segs m -> stk s0segs m lo (usp - 160) -> (- 2 ^ 63 <= rc < 2 ^ 63)%Z ->
    evt s0segs (RETpost rc [(usp - 160, usp)]%Z m)
      (EST 0x145b0 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 E m).
  Proof.
    intros until w9. intros SM FR3 FR MI ST RC. prep. unfold STRMX, DBZA, DBZF in SM. unfold FRE in FR3. unfold S0_b2c_segB.FRWR in FR.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl [(usp - 160, usp)]%Z m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wst. wstep. wstep. wstep. wstep. wstep.
    try rewrite (ret_pc_even 0x15f04) by (first [lia | reflexivity]).
    replace (usp - 160 + 32)%Z with (usp - 128)%Z by lia.
    release_frame FR3 ST (usp - 128)%Z.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells s0segs ?mm (usp - 128)%Z ?cs |- _ =>
      assert (WHOLE : rw_cells s0segs mm (usp - 128)%Z (cs ++ FRWR));
      [ apply (proj2 (DecTac2.rw_cells_app_iff s0segs mm (usp - 128)%Z cs FRWR)); split; [exact H|];
        lazymatch goal with |- rw_cells _ _ ?a _ => replace a with (usp - 48)%Z by (cbn; lia) end; exact FR
      | clear H FR; unfold S0_b2c_segB.FRWR in WHOLE; cbn [app] in WHOLE ] end.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    release_frame WHOLE ST (bv_unsigned sp).
    replace (Z_to_bv 64 (usp - 128 + 128)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    unfold S0_b2c_segA.RETpost. finish. reflexivity.
  Qed.
End WRAP.
End ACeilS1.
