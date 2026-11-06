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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith3 BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet DecTacSA A0F_decCutsE A0F_decCuts12S.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts12S.
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


Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).

  Ltac prepS DM MU DP SM :=
    pose proof (act_linF _ _ _ _ _ AOK DP) as LIN; cbv zeta in LIN; lin_split LIN; pose proof rnums_words_length as RNL; lin_natZ RNL;
    unfold_W14 MU; open_ash ASH AOK;
    lazymatch goal with H : sanchor (b_s _) (a_shs _) |- _ => pose proof (proj2 H : saddr (b_s (a_cx A)) (a_shs A)) as ANS0 end;
    unfold_blk SM MU; open_shb SM; open_dmemF DM; a0img.
  Ltac fold_MU MU SM :=
    lazymatch type of MU with munch ?W ?ma ?mb =>
      let H := fresh "MUf" in
      assert (H : munch (W14 A) ma mb)
        by (unfold W14, DSTATE_SIZE, blk_ivls; rewrite SM; cbn [Z.eqb app]; exact MU);
      clear MU; rename H into MU end.
  (* [comment removed for export] *)
  Ltac small_facts SF DP :=
    let TS := fresh "TS" in let SM1 := fresh "SM1" in let HDR := fresh "HDR" in let ORIG := fresh "ORIG" in
    let NB1 := fresh "NB1" in let NB9 := fresh "NB9" in let HIST := fresh "HIST" in let SYMB := fresh "SYMB" in
    let UNZ := fresh "UNZ" in let CFP := fresh "CFP" in let HL16 := fresh "HL16" in let HL16R := fresh "HL16R" in let HL4R := fresh "HL4R" in
    cps_pose SF as (TS & SM1 & HDR & ORIG & NB1 & NB9 & HIST & SYMB & UNZ & CFP & HL16 & HL16R & HL4R);
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL; rewrite SM1 in SMALL; symmetry in SMALL;
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.

  Section Sm.
  Variables (sym unz ll16_0 ll4_0 : Z -> Z).
  Notation L26c k := (A0F_cut_L26 A Q F k sym unz ll16_0 ll4_0).
  Notation L27c i fa fb fc := (A0F_cut_L27 A Q F i fa fb fc sym unz ll16_0 ll4_0).

  Lemma A0F_U12_L26 : forall k, (0 <= k <= 256)%Z ->
    ((k < 256)%Z -> L26c (k + 1)%Z) -> (k = 256%Z -> L27c 0%Z ll16_0 ll4_0 (psum unz)) -> L26c k.
  Proof.
    intros k Hk NXT LAST. unfold A0F_cut_L26. intros until w720. intros DM FRL FRH AF ST MU WM MI DP SF V16 V4 CFC KR FU.
    small_facts SF DP.
    prepS DM MU DP SMALL. unfold r_of in DR. dr_open.
    pose proof (CFP k ltac:(lia)) as CFk. pose proof (psum_range sym unz (Z.to_nat (sv_nblock L)) ltac:(intros; apply SYMB; lia) HIST k ltac:(lia)) as PSk.
    hide_all_but_atF [S + 1096; S + 2124; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 2124, S + 3152)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_L26_step F L d s k) in KQ by lia.
    (* [comment removed for export] *)
    arun_to 0xa6b98%Z.
    pose proof (zw32_read a0segs m (S + 1096) (d_cftab d) 257 k _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD.
    arun_to 0xa6ba0%Z.
    zw32_sw DRcfc k (zget (d_cftab d) k) ltac:(rewrite unsigned_lit by lia; reflexivity). (* [comment removed for export] *)
    pose proof (dpureF_set_cftabCopy _ _ _ _ _ _ (zset (d_cftabCopy d) k (zget (d_cftab d) k)) DP) as DP'.
    (* [comment removed for export] *)
    arun; if_cases K2; zify_cond_z K2.
    - (* [comment removed for export] *)
      arun; if_cases K0; zify_cond_z K0; [exfalso; lia|].
      arun_to 0xa6c00%Z. sh_norm.
      replace (k + 1)%Z with 257%Z in KQ by lia. rewrite (K_L26_exit F L) in KQ.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof (LAST ltac:(lia)) as NX. unfold A0F_cut_L27 in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP'.
      all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact V16. all: try exact V4. all: try reflexivity.
      all: try (intros q Hq; dmodel_cbn; rewrite zget_zset; destruct (Z.eqb_spec q k); [subst; exact CFk| apply CFC; lia]).
      all: lia.
    - (* [comment removed for export] *)
      arun_to 0xa6b78%Z.
      revive_all MUL WML AOK. fold_MU MU SMALL.
      pose proof (NXT ltac:(lia)) as NX. unfold A0F_cut_L26 in NX.
      kq_fold. enter_cutF (NX L _ s JK_) DP'.
      all: try (apply (smallF_frame L d _ _ _ _ _ SF); reflexivity). all: try exact V16. all: try exact V4.
      all: try (intros q Hq; dmodel_cbn; rewrite zget_zset; destruct (Z.eqb_spec q k); [subst; exact CFk| apply CFC; lia]).
      all: lia.
  Qed.
  Lemma A0F_U12_L26_all : L27c 0%Z ll16_0 ll4_0 (psum unz) -> L26c 0%Z.
  Proof.
    intros LAST.
    assert (G : forall k : nat, (k <= 256)%nat -> L26c (256 - Z.of_nat k)%Z).
    { induction k as [|k IH]; intros Hk.
      - apply A0F_U12_L26; [lia| intros; exfalso; lia| intros _; exact LAST].
      - apply A0F_U12_L26; [lia| intros _| intros; exfalso; lia].
        replace (256 - Z.of_nat (Datatypes.S k) + 1)%Z with (256 - Z.of_nat k)%Z by lia. apply IH. lia. }
    exact (G 256%nat ltac:(lia)).
  Qed.
  End Sm.

  (* [comment removed for export] *)
  Lemma A0F_U12_HSMALL :
    (forall sym unz ll16_0 ll4_0, A0F_cut_L27 A Q F 0 ll16_0 ll4_0 (psum unz) sym unz ll16_0 ll4_0) -> A0F_cut_HSMALL A Q F.
  Proof.
    intros L27. unfold A0F_cut_HSMALL. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP. unfold drep in RP. pose proof (proj1 (proj2 RP)) as R16. pose proof (proj1 (proj2 (proj2 RP))) as R4. clear RP.
    pose proof (smallF_of_HSMALL L d DI R16 R4) as SF. small_facts SF DP.
    pose proof DM as DM0. prepS DM MU DP SMALL.
    kq_intro. rewrite K_HSMALL_L26 in KQ.
    arun_to 0xa6b78%Z.
    fold_MU MU SMALL.
    pose proof (A0F_U12_L26_all _ _ _ _ (L27 (bsym d) (zget (d_unzftab d)) (zget (d_ll16 d)) (zget (d_ll4 d)))) as NX.
    unfold A0F_cut_L26 in NX.
    kq_fold. eapply evt_eq; [ | eapply (NX L d s J) ]; [ st_eq | first [ exact DM0 | exact SF | eassumption | (intros; reflexivity) | (intros; exfalso; lia) | lia ] .. ].
  Qed.
End R.
End ACeilS1.
