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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith3 BzDU5 BzDUM BzDU11 BzDU12F DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet DecTacSA A0F_decCutsE A0F_decCuts12F.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCuts12F.
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
(* [comment removed for export] *)
Lemma zw32_read_b0 : forall segs m A a n i ad, u32arr segs m A (zw32 a n) -> (0 <= i < n)%Z -> (0 <= zget a i < 2 ^ 32)%Z ->
  ad = wa (A + 4 * i) -> ov_read_bytes segs m ad 1 = Some [Z_to_bv 8 (Z.land (zget a i) 255)].
Proof.
  intros segs m A a n i ad H Hi Hv ->.
  rewrite (u32arr_read_b0 segs m A (zw32 a n) i (Z_to_bv 64 (zget a i)) _ H (zw32_nth a n i Hi) ltac:(lia) eq_refl).
  f_equal. f_equal. rewrite unsigned_lit by lia. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply Z_to_bv8_mod256.
Qed.
Section R.
  Variable A : act14.
  Hypothesis AOK : act_ok AIHI0 A.
  Hypothesis ASH : act_sh DI_A0 A.
  Variable Q : dres -> machine_state -> Prop.
  Variable F : nat.

  Notation usp := (bv_unsigned (a_sp A)).
  Notation cx := (a_cx A).
  Notation S := (b_s (a_cx A)).
  Notation TT := (b_tt (a_cx A)).

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
  Ltac blk_goal D :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let B := fresh "BLK" in assert (B : blk_at a0segs mm cx (blk_of cx D)) end.

  (* [comment removed for export] *)
  Lemma A0F_U12_L29 : forall sym tt0 i,
    A0F_cut_L29 A Q F (i + 1) sym tt0 -> A0F_cut_AFT A Q F sym tt0 -> A0F_cut_L29 A Q F i sym tt0.
  Proof.
    intros sym tt0 i NXT LAST. unfold A0F_cut_L29. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI Hi FU.
    cps_pose DI as (Hi0 & ORIG & NB1 & NB9 & HDR & TS & SM0 & SYMB & HIST & HT0 & HT0R & TTV & CFV).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM0 in SMALL. symmetry in SMALL.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    prepS DM MU DP SMALL.
    unfold blk_of in BLK. rewrite SMALL in BLK. cbn [Z.eqb blk_at] in BLK. cps_destruct BLK as (_ & TTA & TTL).
    pose proof (act_tt_s _ _ AOK SMALL) as [[TT0 TT1] SEPtt].
    cps_pose (l29_facts L d i sym tt0 DI ltac:(lia)) as (EUC & UCR & KR & VR & ALLR & VR2 & _).
    pose proof (ALLR i ltac:(lia)) as TIR. unfold l29_v, l29_k, l29_uc in EUC, UCR, KR, VR, VR2.
    unfold r_of in DR. dr_open. hide_all_but_atF [S + 1096; TT; a_P A; a_P A + 496]%Z.
    pose proof (munch_refl [(S + 1096, S + 2124); (TT, TT + 400000 * b_n cx); (a_P A + 496, a_P A + 728)]%Z m) as MUL. pose proof (wmono_refl a0segs m) as WML.
    kq_intro. rewrite (K_L29_step F L d s i) in KQ by lia.
    remember (Z.land (zget (d_tt d) i) 255) as uc eqn:Euc.
    remember (zget (d_cftab d) uc) as k eqn:Ek.
    remember (Z.lor (zget (d_tt d) k) (Z.shiftl i 8)) as v eqn:Ev.
    assert (Ev' : Z.lor (zget (d_tt d) k) (256 * i) = v) by (rewrite Ev, Z.shiftl_mul_pow2 by lia; f_equal; lia).
    (* [comment removed for export] *)
    arun_to 0xa712c%Z.
    pose proof (zw32_read_b0 a0segs m TT (d_tt d) _ i _ TTA ltac:(lia) ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    rewrite <- Euc in RD.
    astep. clear RD. rewrite zxb_lit8 by lia.
    (* [comment removed for export] *)
    arun_to 0xa7148%Z.
    pose proof (zw32_read a0segs m (S + 1096) (d_cftab d) 257 uc _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    rewrite <- Ek in RD.
    astep. clear RD.
    (* [comment removed for export] *)
    arun_to 0xa7164%Z.
    pose proof (zw32_read a0segs m TT (d_tt d) _ k _ TTA ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    astep. clear RD.
    astep. (* [comment removed for export] *) rewrite ?Ev'.
    zw32_sw TTA k v ltac:(rewrite unsigned_lit by lia; reflexivity). (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read a0segs mm (S + 1096) (d_cftab d) 257 uc _ CF ltac:(lia) ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    rewrite <- Ek in RD. astep. clear RD.
    arun_to 0xa7184%Z.
    zw32_sw CF uc (k + 1)%Z ltac:(rewrite unsigned_lit by lia; reflexivity).
    pose proof (dinv_L29_step L d i sym tt0 DI ltac:(lia)) as DI'. unfold l29_d', l29_v, l29_k, l29_uc in DI'.
    rewrite <- Euc, <- Ek, <- Ev in DI'.
    pose proof (dpureF_set_tt _ _ _ _ _ _ k v DP ltac:(lia)) as DP'.
    (* [comment removed for export] *)
    arun; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      clear SEPtt. revive_all_smA AOK MUL WML.
      blk_goal (d_set_cftab (d_set_tt d (zset (d_tt d) k v)) (zset (d_cftab d) uc (k + 1))).
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SMALL.
      unfold A0F_cut_L29 in NXT.
      subst v. subst k. subst uc.
      kq_fold. enter_cutF (NXT L _ s JK_) DP'; [ exact DI' | lia ].
    - (* [comment removed for export] *)
      arun_to 0xa72c0%Z.
      clear SEPtt. revive_all_smA AOK MUL WML.
      blk_goal (d_set_cftab (d_set_tt d (zset (d_tt d) k v)) (zset (d_cftab d) uc (k + 1))).
      { unfold blk_of. rewrite SMALL. cbn [Z.eqb blk_at]. dmodel_cbn. split; [exact SMALL|]. split; [exact TTA| rewrite zw32_length; lia]. }
      clear TTA. fold_MU MU SMALL.
      unfold A0F_cut_AFT in LAST.
      replace (i + 1)%Z with (sv_nblock L) in KQ by lia. rewrite (K_L29_exit F L) in KQ.
      replace (i + 1)%Z with (sv_nblock L) in DI' by lia.
      subst v. subst k. subst uc.
      kq_fold. enter_cutF (LAST L _ s JK_) DP'.
      exact DI'.
  Qed.
  Lemma A0F_U12_L29_all : forall sym tt0, A0F_cut_AFT A Q F sym tt0 -> forall i, A0F_cut_L29 A Q F i sym tt0.
  Proof.
    intros sym tt0 LAST.
    assert (G : forall k : nat, forall i, (900000 - Z.of_nat k <= i)%Z -> A0F_cut_L29 A Q F i sym tt0).
    { induction k as [|k IH]; intros i Hk.
      - (* [comment removed for export] *)
        unfold A0F_cut_L29. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI Hi FU. exfalso.
        cps_pose DI as (_ & _ & _ & NB9 & _). cbn in Hk. lia.
      - apply A0F_U12_L29; [apply IH; lia | exact LAST]. }
    intros i. destruct (Z_lt_le_dec i 0) as [N|P].
    - unfold A0F_cut_L29. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI Hi FU. exfalso. cps_pose DI as (Hi0 & _). lia.
    - apply (G (Z.to_nat 900000)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A0F_U12_HFAST : (forall sym tt0, A0F_cut_AFT A Q F sym tt0) -> A0F_cut_HFAST A Q F.
  Proof.
    intros AFT. unfold A0F_cut_HFAST. intros until w720. intros DM FRL FRH AF ST MU WM MI DP DI FU.
    cps_pose DI as (EOB & ORIG & CFP & TS & SM0). cps_pose EOB as (NB1 & NB9 & SYMB & HIST & HDR).
    pose proof (dpureF_small _ _ _ _ _ _ DP) as SMALL. rewrite SM0 in SMALL. symmetry in SMALL.
    pose proof (dpureF_n _ _ _ _ _ _ DP) as BN.
    pose proof (dpureF_rep _ _ _ _ _ _ DP) as RP. unfold drep in RP. destruct RP as (TTR & _).
    pose proof (dinv_L29_entry L d DI TTR) as DI0.
    pose proof DM as DM0. prepS DM MU DP SMALL.
    kq_intro. rewrite K_HFAST_L29 in KQ.
    (* [comment removed for export] *)
    arun; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    arun_to 0xa711c%Z.
    fold_MU MU SMALL.
    pose proof (A0F_U12_L29_all (bsym d) (zget (d_tt d)) (AFT _ _) 0%Z) as NX. unfold A0F_cut_L29 in NX.
    kq_fold. eapply evt_eq; [ | eapply (NX L d s J) ]; [ st_eq | first [ exact DM0 | eassumption | lia ] .. ].
  Qed.
End R.
End ACeilS1.
