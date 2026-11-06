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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet DecTacSA A0F_decCutsM A0F_decCutsL A0F_dec_U10J.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsL OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_dec_U10J.
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
(* [comment removed for export] *)
Lemma addiw_m1 : forall x, (-1 <= x <= 2147483646)%Z ->
  bv_swrap 32 (Z.land x 18446744073709551615 + 1) = (x + 1)%Z.
Proof.
  intros x Hx. destruct (Z.eq_dec x (-1)) as [->|NE].
  - vm_compute. reflexivity.
  - rewrite (land64_small x) by lia. rewrite swrap32_small by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma swrap32_add_land_neg : forall a b, (-2147483648 <= a + b < 2147483648)%Z -> (-18446744073709551616 <= b < 0)%Z ->
  bv_swrap 32 (a + Z.land b 18446744073709551615) = (a + b)%Z.
Proof.
  intros a b H1 H2. rewrite (land64_neg b) by lia. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
  replace (a + (b + 18446744073709551616) + 2147483648)%Z with ((a + b + 2147483648) + 4294967296 * 4294967296)%Z by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.
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

  Let LJ := A0F_U10_LJ A AOK ASH Q F HC.

  (* [comment removed for export] *)
  Lemma A0F_U10_LRI : forall mb lno uc ii j,
    ((j < 15)%Z -> A0F_cut_LRI A Q F mb lno uc ii (j + 1)) -> ((1 <= ii)%Z -> A0F_cut_LRO A Q F mb lno uc (ii - 1)) -> A0F_cut_LRI A Q F mb lno uc ii j.
  Proof.
    intros mb lno uc ii j NXT ROWc. unfold A0F_cut_LRI. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA NB UCR LNO HII HJ MTI MA0 ROW FU.
    fprep DM MU DP MR.
    pose proof (mb_reb_range mb lno MTI ii ii ltac:(lia) ltac:(lia)) as R1.
    assert (RV : mb_reb mb lno ii ii = mb_aft mb lno ii) by (unfold mb_reb; rewrite Z.ltb_irrefl; reflexivity).
    hide_all_but_atF [S + 3724; S + 7820; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 3724, S + 7884)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_LRI_step F L d s uc ii j) in KQ by lia.
    arun_to 0xa6364%Z. mtfb_rdA ROW ii. (* [comment removed for export] *)
    arun_to 0xa6394%Z. mtfa_rdA MA (zget (d_mtfbase d) ii + (15 - j))%Z. (* [comment removed for export] *)
    arun_to 0xa63a4%Z. try rewrite (addiw_m1 (j - 1)) by lia.
    mtfa_wrA (3855 + 16 * ii - j)%Z. (* [comment removed for export] *)
    pose proof (dpureF_set_mtfa _ _ _ _ _ _ (3855 + 16 * ii - j) (zget (d_mtfa d) (zget (d_mtfbase d) ii + (15 - j))) DP ltac:(apply MA; lia)) as DP'.
    (* [comment removed for export] *)
    arun. try rewrite (addiw_m1 (j - 1)) by lia.
    if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      revive_all MUL WML AOK.
      pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_LRI in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP'; u10_side MR MA ROW.
    - (* [comment removed for export] *)
      arun_to 0xa63e4%Z.
      rewrite ?(swrap32_add_land_neg (3855 + 16 * ii) (- j + -1)) by lia.
      replace (3855 + 16 * ii - (j - 1 + 1))%Z with (3840 + 16 * ii)%Z by lia.
      mtfb_wrA ii (3840 + 16 * ii)%Z.
      replace (j + 1)%Z with 16%Z in KQ by lia. rewrite (K_LRI_exit F L) in KQ.
      pose proof (dpureF_set_mtfbase _ _ _ _ _ _ (zset (d_mtfbase d) ii (3840 + 16 * ii)) DP') as DP''.
      assert (ROW' : forall D, d_mtfbase D = zset (d_mtfbase d) ii (3840 + 16 * ii) -> mbrow D (mb_reb mb lno (ii - 1))).
      { intros D E. apply (mbrow_ext _ (zfupd (mb_reb mb lno ii) ii (3840 + 16 * ii))).
        - intros l Hl. symmetry. apply (mb_reb_step mb lno ii). lia.
        - apply (mbrow_set_gen d); [exact ROW| exact E]. }
      (* [comment removed for export] *)
      arun; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        revive_all MUL WML AOK.
        pose proof (ROWc ltac:(lia)) as NX. unfold A0F_cut_LRO in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP''; u10_side MR MA ROW.
        all: try (apply ROW'; dmodel_cbn; reflexivity).
      + (* [comment removed for export] *)
        arun_to 0xa64a8%Z. revive_all MUL WML AOK.
        replace (ii - 1)%Z with (-1)%Z in KQ, ROW' by lia. rewrite (K_LRO_exit F L) in KQ.
        pose proof (LJ uc (mb_reb mb lno (-1))) as NX. unfold A0F_cut_LJ in NX.
        kq_fold. enter_cutF (NX L _ s JK_) DP''; u10_side MR MA ROW.
        all: try (apply mtf_home_inv; apply mb_reb_home).
        all: try (apply ROW'; dmodel_cbn; reflexivity).
  Qed.
  Lemma A0F_U10_LRI_all : forall mb lno uc ii, ((1 <= ii)%Z -> A0F_cut_LRO A Q F mb lno uc (ii - 1)) -> forall j, (0 <= j <= 15)%Z -> A0F_cut_LRI A Q F mb lno uc ii j.
  Proof.
    intros mb lno uc ii ROWc j Hj.
    assert (G : forall n : nat, (n <= 15)%nat -> A0F_cut_LRI A Q F mb lno uc ii (15 - Z.of_nat n)%Z).
    { induction n as [|n IH]; intros Hn.
      - apply A0F_U10_LRI; [intros; exfalso; lia| exact ROWc].
      - apply A0F_U10_LRI; [intros _| exact ROWc]. replace (15 - Z.of_nat (Datatypes.S n) + 1)%Z with (15 - Z.of_nat n)%Z by lia. apply IH. lia. }
    replace j with (15 - Z.of_nat (Z.to_nat (15 - j)))%Z by lia. apply G. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U10_LRO : forall mb lno uc ii, ((1 <= ii)%Z -> A0F_cut_LRO A Q F mb lno uc (ii - 1)) -> A0F_cut_LRO A Q F mb lno uc ii.
  Proof.
    intros mb lno uc ii ROWc. unfold A0F_cut_LRO. intros until w720. intros DM FRL FRH AF ST MU WM MI DP MR MA NB UCR LNO HII MTI MA0 ROW FU.
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN.
    kq_intro. rewrite (K_LRO_row F L d s uc ii) in KQ by lia.
    arun_to 0xa635c%Z. rewrite ?(land64_small (S + 7820 + ii * 4)) by (lin_unbox LIN; lia).
    pose proof (A0F_U10_LRI_all mb lno uc ii ROWc 0 ltac:(lia)) as NX. unfold A0F_cut_LRI in NX.
    kq_fold. eapply evt_eq; [ | eapply (NX L d s J) ]; [ st_eq | first [ eassumption | lia ] .. ].
  Qed.
  Lemma A0F_U10_LRO_all : forall mb lno uc ii, (0 <= ii <= 15)%Z -> A0F_cut_LRO A Q F mb lno uc ii.
  Proof.
    intros mb lno uc ii Hii.
    assert (G : forall n : nat, (n <= 15)%nat -> A0F_cut_LRO A Q F mb lno uc (Z.of_nat n)).
    { induction n as [|n IH]; intros Hn.
      - apply A0F_U10_LRO. intros; exfalso; lia.
      - apply A0F_U10_LRO. intros _. replace (Z.of_nat (Datatypes.S n) - 1)%Z with (Z.of_nat n) by lia. apply IH. lia. }
    replace ii with (Z.of_nat (Z.to_nat ii)) by lia. apply G. lia.
  Qed.
End R.
End ACeilS1.
