(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecTac DecTac2 DecTacS DecAux. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzLemmasT BzLemmasT2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 S0_dec_U13 S0_decCuts S0_decCutsM S0_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_decRet.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCutsE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet.S0_indexIntoF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDUM BzDU9 BzDU11 BzDU12F. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF DecTacFR DecTacF3 DecAux12F S0F_decRet S0F_decCuts S0F_decCutsM S0F_decCutsE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacFR OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux12F OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decRet OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCuts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_decCutsE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDU12S. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecAux12S S0F_decCuts12S.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT DecFastS.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
Local Ltac DecTacS.revive_sm H AOK SM0 MUL WML ::= DecFastS.revive_sm_cached H AOK SM0 MUL WML.
Local Ltac DecTacS.revive_all_smL AOK SM0 MUL WML LIN DP ::= DecFastS.revive_all_smL_split AOK SM0 MUL WML LIN DP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacFR BzImg0Tac.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require SasFastF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac simpl_arr_sizes ::= SasFastF.sas6F_all.
Local Ltac StoreFast.tlia ::= RelLia.tlia_r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.

Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok 320 A.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation L16 := (b_ll16 (a_cx A)).
  Notation L4 := (b_ll4 (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold W14, D14, DSTATE_SIZE, blk_ivls in MU; rewrite SM in MU; cbn [Z.eqb app b_s b_strm] in MU; open_dmemF DM; s2img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 DI_S0 cx usp) ma mb)
        by (unfold W14, D14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app b_s b_strm di_segs DI_S0]; exact MU);
      clear MU; rename H into MU end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac small_facts SF DP :=
    let TS := fresh "TS" in let SM1 := fresh "SM1" in let HDR := fresh "HDR" in let ORIG := fresh "ORIG" in
    let NB1 := fresh "NB1" in let NB9 := fresh "NB9" in let HIST := fresh "HIST" in let SYMB := fresh "SYMB" in
    let UNZ := fresh "UNZ" in let CFP := fresh "CFP" in let HL16 := fresh "HL16" in let HL16R := fresh "HL16R" in let HL4R := fresh "HL4R" in
    cps_pose SF as (TS & SM1 & HDR & ORIG & NB1 & NB9 & HIST & SYMB & UNZ & CFP & HL16 & HL16R & HL4R);
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL; rewrite SM1 in SMALL; symmetry in SMALL;
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.

  Section Sm.
  Variables (L : dsv) (s : dstrm) (J : jk) (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation L26cF := (L26cF A F L s J sym unz ll16_0 ll4_0). Notation L27cF := (L27cF A F L s J sym unz ll16_0 ll4_0).

  Lemma S0F_U12_L26 : forall k, (0 <= k <= 256)%Z ->
    ((k < 256)%Z -> L26cF (k + 1)) -> (k = 256%Z -> L27cF 0 ll16_0 ll4_0 (psum unz)) -> L26cF k.
  Proof.
    intros k Hk NXT LAST. unfold S0F_decCuts12S.L26cF. intros until pb. intros DM FR ST MU WM MI DP FU SF V16 V4 CFC KR.
    small_facts SF DP.
    prepS DM MU DP SMALL. unfold r_of in DR. dr_open.
    pose proof (CFP k ltac:(lia)) as CFk. pose proof (psum_range sym unz (Z.to_nat (sv_nblock L)) ltac:(intros; apply SYMB; lia) HIST k ltac:(lia)) as PSk.
    hide_all_but_at [S + 1096; S + 2124]%Z.
    pose proof (munch_refl [(S + 2124, S + 3152)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite (K_L26_step F L d s k) in KQ by lia.
    wstepl; notrap. wstepl; notrap. wstepl.
    pose proof (zw32_read s0segs m (S + 1096) (d_cftab d) 257 k _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstepl. clear RD. (* [comment removed for export] *)
    wstepl. wstepl.
    zw32_sw DRcfc k (zget (d_cftab d) k) ltac:(rewrite unsigned_lit by lia; reflexivity). (* [comment removed for export] *)
    pose proof (dpureF_set_cftabCopy _ _ _ _ _ _ (zset (d_cftabCopy d) k (zget (d_cftab d) k)) DP) as DP'.
    wstepl; if_cases K2; zify_cond_z K2.
    - revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof (NXT ltac:(lia)) as NX. unfold S0F_decCuts12S.L26cF in NX.
      kq_fold. enter_cutF NX DP'.
      all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact V16. all: try exact V4.
      all: try (intros q Hq; dmodel_cbn; rewrite zget_zset; destruct (Z.eqb_spec q k); [subst; exact CFk| apply CFC; lia]).
      all: lia.
    - wstepl; if_cases K0; zify_cond_z K0; [exfalso; lia|].
      wstepl. wstepl.
      replace (k + 1)%Z with 257%Z in KQ by lia. rewrite (K_L26_exit F L) in KQ.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof (LAST ltac:(lia)) as NX. unfold S0F_decCuts12S.L27cF in NX.
      kq_fold. enter_cutF NX DP'.
      all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact V16. all: try exact V4. all: try reflexivity.
      all: try (intros q Hq; dmodel_cbn; rewrite zget_zset; destruct (Z.eqb_spec q k); [subst; exact CFk| apply CFC; lia]).
      all: lia.
  Time Qed.
  Lemma S0F_U12_L26_all : L27cF 0 ll16_0 ll4_0 (psum unz) -> L26cF 0.
  Proof.
    intros LAST.
    assert (G : forall k : nat, (k <= 256)%nat -> L26cF (256 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply S0F_U12_L26; [lia| intros; exfalso; lia| intros _; exact LAST].
      - apply S0F_U12_L26; [lia| intros _| intros; exfalso; lia].
        replace (256 - Z.of_nat (Datatypes.S k) + 1)%Z with (256 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 256%nat ltac:(lia)).
  Qed.
  End Sm.

  (* [comment removed for export] *)
  Lemma S0F_U12_HSMALL :
    (forall L s J sym unz ll16_0 ll4_0, L27cF A F L s J sym unz ll16_0 ll4_0 0 ll16_0 ll4_0 (psum unz)) -> S0F_cut_HSMALL A F.
  Proof.
    intros L27. unfold S0F_cut_HSMALL. intros until pb. intros DM FR ST MU WM MI DP DI FU.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP. unfold drep in RP. pose proof (proj1 (proj2 RP)) as R16. pose proof (proj1 (proj2 (proj2 RP))) as R4. clear RP.
    pose proof (smallF_of_HSMALL L d DI R16 R4) as SF. small_facts SF DP.
    prepS DM MU DP SMALL.
    hide_all_but_at [usp + -336]%Z.
    pose proof (munch_refl [(usp + -336, usp)]%Z m) as MUL. pose proof (wmono_refl s0segs m) as WML.
    kq_intro. rewrite K_HSMALL_L26 in KQ.
    do 5 wstepl.
    revive_all MUL WML AOK. fold_MU MU SMALL.
    pose proof (S0F_U12_L26_all L s J _ _ _ _ (L27 L s J (bsym d) (zget (d_unzftab d)) (zget (d_ll16 d)) (zget (d_ll4 d)))) as NX.
    unfold S0F_decCuts12S.L26cF in NX.
    kq_fold. enter_cutF NX DP.
    all: try exact SF. all: try (intros; reflexivity). all: try (intros; exfalso; lia). all: try lia.
  Time Qed.
End R.
End ACeilS1.
