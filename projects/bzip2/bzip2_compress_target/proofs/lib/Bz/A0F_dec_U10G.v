(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasMtf BzDU5 BzDUM BzDU10 DecAuxL DecTacF3 DecAux10F DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU10 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAuxL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux10F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet DecTacSA A0F_decCutsM A0F_decCutsL A0F_dec_U10J A0F_dec_U10R.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_dec_U10J OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_dec_U10R.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac.DecAuxB.   (* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.
  Hypothesis HC : A0F_cut_HMTFC A Q F.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).

  Ltac prep DM MU DP :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    open_dmemF DM; a0img.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac u10_facts MR DP :=
    let AL := fresh "AL" in let GR := fresh "GR" in let TB := fresh "TB" in let BL := fresh "BL" in let CU := fresh "CU" in
    let NST := fresh "NST" in let NBL := fresh "NBL" in let NBM := fresh "NBM" in let BN := fresh "BN" in
    let RP := fresh "RP" in let S0UR := fresh "S0UR" in
    lazymatch type of MR with ml_nomtfF ?L ?d =>
      cps_pose MR as (AL & GR & TB & BL & CU);
      pose proof (alpha_ok_state L d AL) as NST;
      assert (NBL : (0 <= sv_nblock L <= 900000)%Z) by (unfold alpha_ok in AL; tauto);
      assert (NBM : sv_nblockMAX L = (100000 * d_bs100k d)%Z) by (unfold grp_okF in GR; tauto);
      pose proof (dpureF_n _ _ _ _ _ _ DP) as BN; rewrite BN in NBM;
      pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP; unfold drep in RP;
      pose proof (fun i => proj1 (proj2 (proj2 (proj2 RP))) i) as S0UR; cbn beta in S0UR; clear RP
    end.
  (* [comment removed for export] *)
  Ltac fprep DM MU DP MR :=
    u10_facts MR DP; prep DM MU DP; lazymatch goal with D : drest_at _ _ _ _ |- _ => unfold r_of in D end; dr_open.
  (* [comment removed for export] *)
  Ltac mtfa_rdA MA i :=
    let RD := fresh "RD" in let BR := fresh "BR" in
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ =>
      pose proof (MA i ltac:(lia)) as BR;
      pose proof (zb8_read1 a0segs mm _ a 4096 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      repeat rewrite zget_zset_other in RD by lia;
      astep; clear RD; rewrite zxb_lit8 by lia end.
  Ltac mtfa_wrA i :=
    lazymatch goal with AR : u8arr _ ?mm (b_s (a_cx A) + 3724)%Z (zb8 ?a _) |- _ => zb8_sb AR i end.
  (* [comment removed for export] *)
  Ltac mtfb_rdA ROW i :=
    let RD := fresh "RD" in let E := fresh "ROWv" in
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (ROW i ltac:(lia)) as E;
      pose proof (zw32_read a0segs mm _ a 16 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      astep; clear RD end.
  (* [comment removed for export] *)
  Ltac u10_side MR MA ROW :=
    lazymatch goal with
    | |- ml_nomtfF _ _ => repeat first [apply ml_nomtfF_set_mtfa | apply ml_nomtfF_set_mtfbase]; exact MR
    | |- mtfa_ok _ => rewrite ?d_mtfa_set_mtfa, ?d_mtfa_set_mtfbase; repeat (apply mtfa_ok_set; [ | first [ lia | apply MA; lia ] ]); exact MA
    | |- mbrow _ _ => try (repeat apply mbrow_set_mtfa; exact ROW)
    | |- _ => first [ assumption | lia | idtac ]
    end.
  Ltac mtfb_wrA i v :=
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      zw32_sw AR i v ltac:(rewrite unsigned_lit by lia; first [reflexivity | f_equal; lia]) end.
  (* [comment removed for export] *)
  Ltac mtfb_rdZ ROW i :=
    let RD := fresh "RD" in let E := fresh "ROWv" in
    lazymatch goal with AR : u32arr _ ?mm (b_s (a_cx A) + 7820)%Z (zw32 ?a _) |- _ =>
      pose proof (ROW i ltac:(lia)) as E;
      pose proof (zw32_read a0segs mm _ a 16 i _ AR ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD;
      repeat (first [ rewrite zget_zset_same in RD | rewrite zget_zset_other in RD by lia ]);
      astep; clear RD end.

  Let LJ := A0F_U10_LJ A AOK ASH Q F HC.
  Let LRO15 := fun mb lno uc => A0F_U10_LRO_all A AOK ASH Q F HC mb lno uc 15 ltac:(lia).

  (* [comment removed for export] *)
  Lemma A0F_U10_LGD : forall mb lno uc l, ((2 <= l)%Z -> A0F_cut_LGD A Q F mb lno uc (l - 1)) -> A0F_cut_LGD A Q F mb lno uc l.
  Proof.
    intros mb lno uc l NXT. unfold A0F_cut_LGD. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA NB UCR LNO HL MTI ROW FU.
    fprep DM MU DP MR.
    pose proof (mb_mid_range mb lno MTI LNO l l ltac:(lia) ltac:(lia)) as R1.
    pose proof (mb_mid_range mb lno MTI LNO l (l - 1) ltac:(lia) ltac:(lia)) as R2.
    pose proof (mtf_inv_bounds mb MTI (l - 1) ltac:(lia)) as R3. pose proof (mtf_inv_bounds mb MTI l ltac:(lia)) as R4.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5.
    pose proof (mb_mid_val mb lno l ltac:(lia)) as V1. pose proof (mb_mid_below mb lno l (l - 1) ltac:(lia) ltac:(lia)) as V2.
    assert (V1R : (16 <= mb_mid mb lno l l - 1 <= 4081)%Z) by (rewrite V1; destruct (Z.eqb_spec l lno); lia).
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_LGD_step F L d s uc l) in KQ by lia.
    arun_to 0xa621c%Z. mtfb_rdZ ROW l. (* [comment removed for export] *)
    arun_to 0xa622c%Z. mtfb_wrA l (zget (d_mtfbase d) l - 1)%Z. (* [comment removed for export] *)
    arun_to 0xa623c%Z. mtfb_rdZ ROW (l - 1)%Z. (* [comment removed for export] *)
    arun_to 0xa6268%Z. mtfa_rdA MA (zget (d_mtfbase d) (l - 1) + 15)%Z. (* [comment removed for export] *)
    arun_to 0xa6270%Z. mtfa_wrA (zget (d_mtfbase d) l - 1)%Z. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (d_mtfbase d) l (zget (d_mtfbase d) l - 1)) DP) as DP1.
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (zget (d_mtfbase d) l - 1) (zget (d_mtfa d) (zget (d_mtfbase d) (l - 1) + 15)) DP1 ltac:(apply MA; lia)) as DP2.
    assert (ROW1 : forall D, d_mtfbase D = zset (d_mtfbase d) l (zget (d_mtfbase d) l - 1) -> mbrow D (mb_mid mb lno (l - 1))).
    { intros D E. apply (mbrow_ext _ (zfupd (mb_mid mb lno l) l (zget (d_mtfbase d) l - 1))).
      - intros l' Hl'. rewrite (ROW l) by lia. symmetry. apply (mb_mid_step mb lno l). lia.
      - apply (mbrow_set_gen d); [exact ROW| exact E]. }
    (* [comment removed for export] *)
    arun; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_LGD in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP2; u10_side MR MA ROW.
      all: try (apply ROW1; dmodel_cbn; reflexivity).
    - (* [comment removed for export] *)
      assert (L1 : l = 1%Z) by lia. subst l.
      replace (1 - 1)%Z with 0%Z in KQ by lia. rewrite (K_LGD_exit F L) in KQ. rewrite (K_LGT_eq F L) in KQ. cbv zeta in KQ. dmodel_cbn_in KQ.
      replace (zget (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)) 0) with (zget (d_mtfbase d) 0) in KQ by (rewrite zget_zset_other by lia; reflexivity).
      replace (1 - 1)%Z with 0%Z in V2, R3 by lia.
      pose proof (mtf_inv_bounds mb MTI 0 ltac:(lia)) as R0.
      arun_to 0xa62d8%Z. mtfb_rdZ ROW 0%Z. (* [comment removed for export] *)
      arun_to 0xa62e0%Z. mtfb_wrA 0%Z (zget (d_mtfbase d) 0 - 1)%Z. (* [comment removed for export] *)
      arun_to 0xa62fc%Z. mtfa_wrA (zget (d_mtfbase d) 0 - 1)%Z. (* [comment removed for export] *)
      arun_to 0xa6300%Z. mtfb_rdZ ROW 0%Z. (* [comment removed for export] *)
      pose proof (dpureF_set_mtfa _ _ _ _ _ _ (zget (d_mtfbase d) 0 - 1) uc DP2 ltac:(lia)) as DP3.
      pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)) 0 (zget (d_mtfbase d) 0 - 1)) DP3) as DP4.
      assert (A0' : mb_aft mb lno 0 = (mb 0 - 1)%Z) by (unfold mb_aft; cbn [Z.leb andb]; destruct (Z.ltb_spec 0 lno); [reflexivity| lia]).
      assert (ROW0 : forall D, d_mtfbase D = zset (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)) 0 (zget (d_mtfbase d) 0 - 1) -> mbrow D (mb_aft mb lno)).
      { intros D E. apply (mbrow_ext _ (zfupd (mb_mid mb lno 0) 0 (zget (d_mtfbase d) 0 - 1))).
        - intros l' Hl'. rewrite (ROW 0%Z) by lia. rewrite V2. rewrite (mb_aft_of_mid mb lno ltac:(lia) l' ltac:(lia)).
          rewrite (mb_mid_bot mb lno 0) by lia. cbn [Z.eqb]. reflexivity.
        - apply (mbrow_set_gen (d_set_mtfbase d (zset (d_mtfbase d) 1 (zget (d_mtfbase d) 1 - 1)))); [apply ROW1; destruct d; reflexivity| rewrite E; destruct d; reflexivity]. }
      arun; if_cases K0; zify_cond_z K0.
      + (* [comment removed for export] *)
        replace (zget (d_mtfbase d) 0 - 1 =? 0)%Z with false in KQ by (symmetry; apply Z.eqb_neq; lia).
        revive_all MUL WML AOK.
        pose proof (LJ uc (mb_aft mb lno)) as NX. unfold A0F_cut_LJ in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP4; u10_side MR MA ROW.
        all: try (apply (mb_aft_inv mb lno MTI); rewrite A0'; lia).
        all: try (apply ROW0; dmodel_cbn; reflexivity).
      + (* [comment removed for export] *)
        replace (zget (d_mtfbase d) 0 - 1 =? 0)%Z with true in KQ by (symmetry; apply Z.eqb_eq; lia).
        arun_to 0xa6330%Z.
        revive_all MUL WML AOK.
        pose proof (LRO15 mb lno uc) as NX. unfold A0F_cut_LRO in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP4; u10_side MR MA ROW.
        all: try (rewrite A0'; lia).
        all: try (apply (mbrow_ext _ (mb_aft mb lno)); [intros l' Hl'; rewrite mb_reb_top by lia; reflexivity | apply ROW0; dmodel_cbn; reflexivity]).
  Qed.
  Lemma A0F_U10_LGD_all : forall mb lno uc l, (1 <= l)%Z -> A0F_cut_LGD A Q F mb lno uc l.
  Proof.
    intros mb lno uc l Hl.
    assert (G : forall n : nat, A0F_cut_LGD A Q F mb lno uc (1 + Z.of_nat n)%Z).
    { induction n as [|n IH].
      - apply A0F_U10_LGD. intros; exfalso; lia.
      - apply A0F_U10_LGD. intros _. replace (1 + Z.of_nat (Datatypes.S n) - 1)%Z with (1 + Z.of_nat n)%Z by lia. exact IH. }
    replace l with (1 + Z.of_nat (Z.to_nat (l - 1)))%Z by lia. apply G.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U10_LGE : forall mb lno uc, A0F_cut_LGE A Q F mb lno uc.
  Proof.
    intros mb lno uc. unfold A0F_cut_LGE. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA MTI ROW NB UCR LNO FU.
    fprep DM MU DP MR.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5. pose proof (ROW lno ltac:(lia)) as ROWl.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_LGE_eq F L d s lno uc) in KQ.
    (* [comment removed for export] *)
    arun_to 0xa61f0%Z.
    mtfb_wrA lno (zget (d_mtfbase d) lno + 1)%Z.
    arun_to 0xa620c%Z.
    pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (d_mtfbase d) lno (zget (d_mtfbase d) lno + 1)) DP) as DP1.
    assert (ROW1 : forall D, d_mtfbase D = zset (d_mtfbase d) lno (zget (d_mtfbase d) lno + 1) -> mbrow D (mb_mid mb lno lno)).
    { intros D E. apply (mbrow_ext _ (zfupd mb lno (zget (d_mtfbase d) lno + 1))).
      - intros l' Hl'. rewrite ROWl. rewrite mb_mid_top, zfupd_eq. destruct (Z.eqb_spec l' lno); [subst; reflexivity| reflexivity].
      - apply (mbrow_set_gen d); [exact ROW| exact E]. }
    revive_all MUL WML AOK.
    pose proof (A0F_U10_LGD_all mb lno uc lno ltac:(lia)) as NX. unfold A0F_cut_LGD in NX.
    kq_fold. enter_cutF (NX L _ s JK_) DP1; u10_side MR MA ROW.
    all: try (apply ROW1; dmodel_cbn; reflexivity).
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U10_LGC : forall mb lno uc k, ((mb lno + 1 < k)%Z -> A0F_cut_LGC A Q F mb lno uc (k - 1)) -> A0F_cut_LGC A Q F mb lno uc k.
  Proof.
    intros mb lno uc k NXT. unfold A0F_cut_LGC. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA MTI ROW NB UCR LNO K FU.
    fprep DM MU DP MR.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5. pose proof (ROW lno ltac:(lia)) as ROWl.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_LGC_step F L d s lno k uc) in KQ by lia.
    arun_to 0xa6190%Z. mtfa_rdA MA (k - 1)%Z. (* [comment removed for export] *)
    arun_to 0xa6198%Z. mtfa_wrA k. (* [comment removed for export] *)
    arun_to 0xa61a4%Z. mtfb_rdZ ROW lno. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ k (zget (d_mtfa d) (k - 1)) DP ltac:(apply MA; lia)) as DP1.
    (* [comment removed for export] *)
    arun; if_cases K2; zify_cond_z K2.
    - revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_LGC in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP1; u10_side MR MA ROW.
    - astep. revive_all MUL WML AOK.
      pose proof (A0F_U10_LGE mb lno uc) as NX. unfold A0F_cut_LGE in NX.
      rewrite (K_LGC_exit' F L _ s lno (k - 1) uc) in KQ by (rewrite d_mtfbase_set_mtfa; lia).
      kq_fold. enter_cutF (NX L _ s JK_) DP1; u10_side MR MA ROW.
  Qed.
  Lemma A0F_U10_LGC_all : forall mb lno uc k, (mb lno < k <= mb lno + 15)%Z -> A0F_cut_LGC A Q F mb lno uc k.
  Proof.
    intros mb lno uc k Hk.
    assert (G : forall n : nat, A0F_cut_LGC A Q F mb lno uc (mb lno + 1 + Z.of_nat n)%Z).
    { induction n as [|n IH].
      - apply A0F_U10_LGC. intros; exfalso; lia.
      - apply A0F_U10_LGC. intros _. replace (mb lno + 1 + Z.of_nat (Datatypes.S n) - 1)%Z with (mb lno + 1 + Z.of_nat n)%Z by lia. exact IH. }
    replace k with (mb lno + 1 + Z.of_nat (Z.to_nat (k - mb lno - 1)))%Z by lia. apply G.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U10_LGH : forall mb, A0F_cut_LGH A Q F mb.
  Proof.
    intros mb. unfold A0F_cut_LGH. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA MTI ROW NB NSR FU.
    fprep DM MU DP MR.
    cps_pose (lno_off_range (sv_nextSym L - 1) ltac:(lia)) as (LNR & OFR & NNE). unfold MTFL_SIZE in LNR, OFR, NNE.
    set (lno := ((sv_nextSym L - 1) / 16)%Z) in *. set (off := ((sv_nextSym L - 1) mod 16)%Z) in *.
    pose proof (mtf_inv_bounds mb MTI lno ltac:(lia)) as R5. pose proof (ROW lno ltac:(lia)) as ROWl.
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro.
    astep. (* [comment removed for export] *)
    replace ((sv_nextSym L - 1) / 16)%Z with lno by reflexivity.
    arun_to 0xa6100%Z. astep. flagsb. (* [comment removed for export] *)
    replace ((sv_nextSym L - 1) mod 16)%Z with off by reflexivity.
    arun_to 0xa610c%Z. mtfb_rdZ ROW lno. (* [comment removed for export] *)
    arun_to 0xa6134%Z. mtfa_rdA MA (zget (d_mtfbase d) lno + off)%Z. (* [comment removed for export] *)
    arun; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      revive_all MUL WML AOK.
      pose proof (A0F_U10_LGE mb lno (zget (d_mtfa d) (zget (d_mtfbase d) lno + off))) as NX. unfold A0F_cut_LGE in NX.
      rewrite (K_LGC_exit' F L d s lno) in KQ by (unset_Z; lia).
      kq_fold. enter_cutF (NX L _ s JK_) DP; u10_side MR MA ROW.
      all: try (apply MA; unset_Z; lia).
    - (* [comment removed for export] *)
      arun_to 0xa6150%Z. flagsb. replace ((sv_nextSym L - 1) mod 16)%Z with off by reflexivity.
      arun_to 0xa6170%Z.
      revive_all MUL WML AOK.
      pose proof (A0F_U10_LGC_all mb lno (zget (d_mtfa d) (zget (d_mtfbase d) lno + off)) (zget (d_mtfbase d) lno + off)%Z ltac:(unset_Z; lia)) as NX.
      unfold A0F_cut_LGC in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP; u10_side MR MA ROW.
      all: try (apply MA; unset_Z; lia).
  Qed.
End R.
End ACeilS1.
