(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (33 recorded proofs replaced by written proofs (impl_post_evt, implM_post_evt, outsk_app and 30 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SoftFloat FmtFp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Stdio.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import Printf_model Printf_mlib Printf_fmts.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Printf_pieces () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib6Common=Printf_pieces=impl_post_evtC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Common=Printf_pieces5outskC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indI47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib6Common;Printf_mlib>implM_bind_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4mpadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_mlib?implM_ret_l_revC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib6Common<Printf_model:pad_piecesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes3orbK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Prelim7zrepeatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4munrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib6Common5FmtFp8LEFT_ADJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ZERO_PADC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Common=Printf_pieces9outsk_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces:outsk_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces9mpad_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_mlib?implM_assoc_revC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;tail_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9conv_tailC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z3ltbK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subK47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lxorC59OSSVerify5KrLib6Common5FmtFp7INT_MAXC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces>conv_tail_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:int_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8conv_intC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z4lnotc59OSSVerify5KrLib6Common=Printf_pieces=conv_int_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;conv_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4convC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_tyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model4d_flC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_wC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Common<Printf_model4d_xpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:dec_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model3d_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:hex_digitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common9SoftFloat9f128_of_dC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib6Common5FmtFp8MARK_POSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp7PAD_POSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp8ALT_FORMC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model3dir00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Common<Printf_model4parg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_PTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_INTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5FmtFp:INTMAX_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model6T_UINTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model5T_DBLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces9conv_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model;printf_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_modelBprintf_pieces_loopC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Common<Printf_model7lit_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model9parse_dirC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef5skipnI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib6Common=Printf_pieces@printf_loop_outsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model=printf_piecesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model<printf_modelC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib6Common=Printf_pieces?zlength_nonneg'C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z6ltb_geK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z8leb_reflI47Corelib4Init5Peano2le00C46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List;firstn_all2K59OSSVerify5KrLib6Common<Printf_model3dir01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib4Init9Datatypes4bool02K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega:ZMicromega;ZArithProof01c59OSSVerify5KrLib6Common=Printf_pieces:ppl_unfoldC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9Morphisms<PER_morphismC47Corelib7Classes>Morphisms_Prop@all_iff_morphismC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib4Init5Logic3iffC47Corelib7Classes>Morphisms_PropIiff_iff_iff_impl_morphismC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes?RelationClasses=iff_Reflexivec59OSSVerify5KrLib6Common=Printf_piecesDppl_noargs_shift_genC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC56Stdlib6ZArith6BinInt1Z7add_0_lC59OSSVerify5KrLib4Spec5Stdio<pieces_usageC1?~~~~~~~~~~~~~~~K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C59OSSVerify5KrLib4Spec5Stdio3strC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces@ppl_noargs_shiftC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces=conv_pieces_sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts9FMT_usageC1?~~~~~~~~~~~~~~~K46Stdlib7Strings6String6string01C59OSSVerify5KrLib4Spec5StdioBpieces_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts?FMT_cannot_openC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StdioApieces_read_errorC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts>FMT_read_errorC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Common<Printf_model4parg03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts;FMT_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio>pieces_too_bigC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model8pass1_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Common<Printf_model8fp_callsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<Printf_model:digits_auxC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib6Common=Printf_piecesAdigits_aux_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib6Common=Printf_piecesDdigits_aux_length_geC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_piecesAdigits_aux_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio:digits_auxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Stdio5fmt_uC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib6Common=Printf_piecesAtail_pieces_plainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06c59OSSVerify5KrLib6Common=Printf_pieces>dec_digits_posC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_piecesAdec_digits_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z9mod_smallK59OSSVerify5KrLib6Common<Printf_model4parg02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_piecesApct_d_conv_piecesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces>pct_d_conv_lenC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes:comparison00I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01C59OSSVerify5KrLib4Spec5Stdio<pieces_pct_dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces9pct_d_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common=Printf_pieces=conv_pieces_dC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common;Printf_fmts9FMT_pct_dC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Lemma impl_post_evt : forall segs {node R} (atn : node -> machine_state -> Prop) (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  ITree.impl segs atn t Q ms -> (forall r ms', Q r ms' -> evt segs (Q' r) ms') -> ITree.impl segs atn t Q' ms.
Proof.
  intros segs node R atn t. induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. exact (HQ r).
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; [apply Hk | exact HQ].
Qed.
Lemma implM_post_evt : forall segs {St A} (c : M St A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
  Monad.implM segs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt segs (Q' a s') ms') -> Monad.implM segs c s Q' ms.
Proof.
  intros segs St A c s Q Q' ms H HQ. unfold Monad.implM in *. eapply impl_post_evt; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I | apply HQ].
Qed.

Section Outs.
  Variable segs : list Segment.
  Context {St : Type}.
  Variable OUT : list Z -> M St unit.
  Variable OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z.
  Local Notation implM := (Monad.implM segs).

  (* [comment removed for export] *)
  Fixpoint outsk {B} (ps : list (list Z)) (k : M St B) : M St B :=
    match ps with
    | [] => k
    | p :: ps' => OUT p ;;; outsk ps' k
    end.

  Lemma outsk_app : forall {B} ps qs (k : M St B), outsk (ps ++ qs) k = outsk ps (outsk qs k).
  Proof. induction ps as [|p ps IH]; intros qs k; [reflexivity|]. cbn [outsk app]. rewrite IH. reflexivity. Qed.

  Lemma outsk_mono : forall {B} ps (k1 k2 : M St B) Q,
    (forall s ms, implM k1 s Q ms -> implM k2 s Q ms) ->
    forall s ms, implM (outsk ps k1) s Q ms -> implM (outsk ps k2) s Q ms.
  Proof.
    induction ps as [|p ps IH]; intros k1 k2 Q HK s ms H; cbn [outsk] in *; [apply HK; exact H|].
    eapply implM_bind_ext; [|exact H]. intros x s' ms' H'. eapply IH; [exact HK | exact H'].
  Qed.

  Lemma mpad_outs : forall {B} c w l fl pp (K : unit -> M St B) s Q ms,
    pad_pieces c w l fl = Some pp ->
    implM (mbind (mpad OUT c w l fl) K) s Q ms -> implM (outsk pp (K tt)) s Q ms.
  Proof.
    intros B c w l fl pp K s Q ms P H. unfold mpad, pad_pieces in *.
    destruct (negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l))%bool.
    - inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H.
    - destruct (256 <=? w - l); [discriminate|]. inversion P; subst. cbn [outsk].
      eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'.
  Qed.

  Lemma out_outs : forall {B} p (K : unit -> M St B) s Q ms,
    implM (mbind (OUT p) K) s Q ms -> implM (outsk [p] (K tt)) s Q ms.
  Proof. intros B p K s Q ms H. cbn [outsk]. eapply implM_bind_ext; [|exact H]. intros [] s' ms' H'. exact H'. Qed.

  Lemma conv_tail_outs : forall {B} cnt fl w p prefix body ps r (K : Z -> M St B) s Q ms,
    tail_pieces cnt fl w p prefix body = Some (ps, r) ->
    implM (mbind (conv_tail OUT cnt fl w p prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p prefix body ps r K s Q ms T H. unfold conv_tail, tail_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct (INT_MAX - zlength prefix <? Z.max p (zlength body)); [discriminate|].
    destruct (INT_MAX - cnt <? Z.max w (zlength prefix + Z.max p (zlength body))); [discriminate|].
    destruct (pad_pieces 32 _ _ fl) as [p1|] eqn:P1; [|discriminate].
    destruct (pad_pieces 48 _ _ (Z.lxor fl ZERO_PAD)) as [p2|] eqn:P2; [|discriminate].
    destruct (pad_pieces 48 _ _ 0) as [p3|] eqn:P3; [|discriminate].
    destruct (pad_pieces 32 _ _ (Z.lxor fl LEFT_ADJ)) as [p4|] eqn:P4; [|discriminate].
    inversion T; subst. clear T.
    match goal with |- implM (outsk ?L (K ?rr)) _ _ _ =>
      replace (outsk L (K rr)) with (outsk p1 (OUT prefix ;;; outsk p2 (outsk p3 (OUT body ;;; outsk p4 (K rr)))))
        by (rewrite ?outsk_app; cbn [outsk]; rewrite ?outsk_app; cbn [outsk]; reflexivity) end.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P1) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s1 ms1 H.
    apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x2 s2 ms2 H.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P2) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s3 ms3 H.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P3) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s4 ms4 H.
    apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. clear H. cbv beta. intros x5 s5 ms5 H.
    apply implM_assoc_rev in H. apply (mpad_outs _ _ _ _ _ _ _ _ _ P4) in H. cbv beta in H.
    eapply outsk_mono; [|exact H]. clear H. cbv beta. intros s6 ms6 H.
    apply implM_ret_l_rev in H. exact H.
  Qed.

  Lemma conv_int_outs : forall {B} cnt fl w p xp argi prefix body ps r (K : Z -> M St B) s Q ms,
    int_pieces cnt fl w p xp argi prefix body = Some (ps, r) ->
    implM (mbind (conv_int OUT cnt fl w p xp argi prefix body) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt fl w p xp argi prefix body ps r K s Q ms T H. unfold conv_int, int_pieces in *.
    destruct (xp && (p <? 0))%bool; [discriminate|]. cbv zeta in T. cbv zeta in H.
    destruct ((argi =? 0) && (p =? 0))%bool; eapply conv_tail_outs; eassumption.
  Qed.

  Lemma conv_outs : forall {B} cnt d a ps r (K : Z -> M St B) s Q ms,
    conv_pieces cnt d a = Some (ps, r) ->
    implM (mbind (conv OUT OUTFP cnt d a) K) s Q ms -> implM (outsk ps (K r)) s Q ms.
  Proof.
    intros B cnt d a ps r K s Q ms T H. unfold conv, conv_pieces in *. cbv zeta in T. cbv zeta in H.
    destruct a as [str|i|u|dd].
    - destruct (negb (d_ty d =? T_PTR)); [discriminate|].
      destruct ((d_p d <? 0) && (INT_MAX <=? zlength str))%bool; [discriminate|].
      eapply conv_tail_outs; eassumption.
    - destruct (negb (d_ty d =? T_INT)); [discriminate|].
      destruct (INTMAX_MAX <? i mod 2 ^ 64);
        [|destruct (negb (Z.land _ MARK_POS =? 0)); [|destruct (negb (Z.land _ PAD_POS =? 0))]];
        eapply conv_int_outs; eassumption.
    - destruct (negb (d_ty d =? T_UINT)); [discriminate|].
      destruct (d_t d =? 117); eapply conv_int_outs; eassumption.
    - discriminate.
  Qed.

  Lemma printf_loop_outs : forall {B} fuel s args cnt ps r (k : Z -> M St B) st Q ms,
    printf_pieces_loop fuel s args cnt = Some (ps, r) ->
    implM (mbind (printf_loop OUT OUTFP fuel s args cnt) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof.
    induction fuel as [|fuel IH]; intros s args cnt ps r k st Q ms P H; [discriminate|].
    cbn [printf_pieces_loop] in P. cbn [printf_loop] in H.
    destruct s as [|c s1]; [discriminate|].
    destruct (c =? 0). { inversion P; subst. cbn [outsk]. apply implM_ret_l_rev in H. exact H. }
    cbv zeta in P. cbv zeta in H. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
    destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
    destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
    destruct (0 <? zlength lit).
    - destruct (INT_MAX - cnt <? zlength lit); [discriminate|].
      destruct (printf_pieces_loop fuel (c1 :: s2) args (cnt + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
      inversion P; subst. clear P. cbn [outsk].
      apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      eapply IH; [exact R | exact H'].
    - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct args as [|a args']; [discriminate|].
      destruct (conv_pieces cnt d a) as [[ps1 cnt']|] eqn:C; [|discriminate].
      destruct (printf_pieces_loop fuel s3 args' cnt') as [[ps2 r2]|] eqn:R; [|discriminate].
      inversion P; subst. clear P.
      match goal with |- implM (outsk ?L (k ?rr)) _ _ _ =>
        replace (outsk L (k rr)) with (outsk [[]] (outsk ps1 (outsk ps2 (k rr)))) by (rewrite <- !outsk_app; reflexivity) end.
      cbn [outsk].
      apply implM_assoc_rev in H. eapply implM_bind_ext; [|exact H]. cbv beta. intros x s' ms' H'.
      apply implM_assoc_rev in H'. apply (conv_outs _ _ _ _ _ _ _ _ _ C) in H'.
      eapply outsk_mono; [|exact H']. cbv beta. intros s'' ms'' H''. eapply IH; [exact R | exact H''].
  Qed.

  Theorem printf_model_outs : forall {B} fmt args ps r (k : Z -> M St B) st Q ms,
    printf_pieces fmt args = Some (ps, r) ->
    implM (mbind (printf_model OUT OUTFP fmt args) k) st Q ms -> implM (outsk ps (k r)) st Q ms.
  Proof. intros B fmt args ps r k st Q ms P H. eapply printf_loop_outs; [exact P | exact H]. Qed.
End Outs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lhs_cbvs := match goal with |- ?l = _ => let l' := eval cbv -[conv_pieces] in l in change l with l' end.
Lemma zlength_nonneg' : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

(* [comment removed for export] *)
Lemma conv_pieces_s : forall cnt s, 0 <= cnt -> zlength s < INT_MAX - cnt ->
  conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |} (PA_s s)
  = Some ([[]; s], cnt + zlength s).
Proof.
  intros cnt s Hc Hs. pose proof (zlength_nonneg' s) as H0.
  unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_PTR Pos.eqb andb Z.ltb Z.compare].
  replace (INT_MAX <=? zlength s) with false by (symmetry; apply Z.leb_gt; lia).
  unfold tail_pieces. cbv zeta. rewrite firstn_all2 by (unfold zlength; lia).
  change (zlength (@nil Z)) with 0.
  replace (Z.max (zlength s) (zlength s)) with (zlength s) by lia.
  replace (INT_MAX - 0 <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.max 0 (0 + zlength s)) with (zlength s) by lia.
  replace (INT_MAX - cnt <? zlength s) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces.
  replace (zlength s <=? 0 + zlength s) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ].
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ppl_unfold : forall fuel s args cnt,
  printf_pieces_loop (S fuel) s args cnt =
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then Some ([], cnt) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if INT_MAX - cnt <? l then None
           else match printf_pieces_loop fuel s1 args (cnt + l) with Some (ps, r) => Some (lit :: ps, r) | None => None end)
        else
          match parse_dir s2, args with
          | Some (d, s3), a :: args' =>
              match conv_pieces cnt d a with
              | Some (ps1, cnt') =>
                  match printf_pieces_loop fuel s3 args' cnt' with Some (ps, r) => Some ([] :: ps1 ++ ps, r) | None => None end
              | None => None
              end
          | _, _ => None
          end
      end
    end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ppl_noargs_shift_gen : forall fuel s c0 ps r,
  printf_pieces_loop fuel s [] c0 = Some (ps, r) ->
  c0 <= r /\ (forall k, 0 <= k -> r + k <= INT_MAX -> printf_pieces_loop fuel s [] (c0 + k) = Some (ps, r + k)).
Proof.
  induction fuel as [|fuel IH]; intros s c0 ps r P; [discriminate|].
  rewrite ppl_unfold in P. setoid_rewrite ppl_unfold.
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0). { inversion P; subst. split; [lia|]. intros k _ _. reflexivity. }
  cbv zeta in P. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg' lit).
  destruct (0 <? zlength lit).
  - destruct (Z.ltb_spec (INT_MAX - c0) (zlength lit)); [discriminate|].
    destruct (printf_pieces_loop fuel (c1 :: s2) [] (c0 + zlength lit)) as [[ps' r']|] eqn:R; [|discriminate].
    inversion P; subst. clear P. destruct (IH _ _ _ _ R) as [LE SH].
    split; [lia|]. intros k Hk Hr.
    replace (INT_MAX - (c0 + k) <? zlength lit) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (c0 + k + zlength lit) with (c0 + zlength lit + k) by lia. rewrite (SH k Hk Hr). reflexivity.
  - destruct (parse_dir s2) as [[d s3]|]; discriminate.
Qed.

Lemma ppl_noargs_shift : forall fuel s cnt ps r,
  printf_pieces_loop fuel s [] 0 = Some (ps, r) -> 0 <= cnt -> cnt + r <= INT_MAX ->
  printf_pieces_loop fuel s [] cnt = Some (ps, cnt + r).
Proof.
  intros fuel s cnt ps r P Hc Hr. destruct (ppl_noargs_shift_gen _ _ _ _ _ P) as [_ SH].
  rewrite <- (Z.add_0_l cnt). rewrite (SH cnt Hc ltac:(lia)). f_equal. f_equal. lia.
Qed.

Ltac ppl_step := rewrite ppl_unfold; match goal with |- ?l = _ => let l' := eval cbv -[printf_pieces_loop conv_pieces] in l in change l with l' end.

Lemma printf_pieces_usage : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_usage [PA_s s] = Some (pieces_usage s, 14 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_usage) with 17%nat.
  ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 15 [32; 73; 78; 80; 85; 84; 10; 0] (7 + zlength s) [[32; 73; 78; 80; 85; 84; 10]] 7 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_usage. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_cannot_open : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_cannot_open [PA_s s] = Some (pieces_cannot_open s, 18 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_cannot_open) with 21%nat.
  ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 19 [10; 0] (17 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_cannot_open. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_read_error : forall s, zlength s < INT_MAX - 256 ->
  printf_pieces FMT_read_error [PA_s s] = Some (pieces_read_error s, 20 + zlength s).
Proof.
  intros s Hs. pose proof (zlength_nonneg' s) as H0. unfold printf_pieces.
  change (Datatypes.length FMT_read_error) with 23%nat.
  ppl_step. ppl_step. change Printf_model.T_PTR with T_PTR. rewrite conv_pieces_s by lia.
  rewrite (ppl_noargs_shift 21 [10; 0] (19 + zlength s) [[10]] 1 ltac:(vm_compute; reflexivity)) by lia.
  unfold pieces_read_error. cbv -[zlength Z.add]. do 2 f_equal; try lia.
Qed.

Lemma printf_pieces_too_big : printf_pieces FMT_too_big [PA_u 67108864] = Some (pieces_too_big, 38).
Proof. vm_compute. reflexivity. Qed.

Lemma pass1_ok_usage : pass1_ok FMT_usage = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_pieces ()) [] "p;2p;1p;3g00N;j22Tg02UXj11Tg00MAj30Tg00`FR0g01RoR1'2g02Lf#1=001do"). Qed.
Lemma pass1_ok_cannot_open : pass1_ok FMT_cannot_open = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_pieces ()) [] "p;2p;1p;3g00N;j22Tg02UXj11Tg00MAj30Tg00`FR0g01RoR1'2g02OJ#1=001do"). Qed.
Lemma pass1_ok_read_error : pass1_ok FMT_read_error = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_pieces ()) [] "p;2p;1p;3g00N;j22Tg02UXj11Tg00MAj30Tg00`FR0g01RoR1'2g02QR#1=001do"). Qed.
Lemma pass1_ok_too_big : pass1_ok FMT_too_big = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_pieces ()) [] "p;2p;1p;3g00N;j22Tg02UXj11Tg00MAj30Tg00`FR0g01RoR1'2g02SW#1=001do"). Qed.
Lemma fp_calls_s : forall fmt s, In fmt [FMT_usage; FMT_cannot_open; FMT_read_error] ->
  fp_calls (Datatypes.length fmt) fmt [PA_s s] = [].
Proof. intros fmt s [<-|[<-|[<-|[]]]]; vm_compute; reflexivity. Qed.
Lemma fp_calls_too_big : fp_calls (Datatypes.length FMT_too_big) FMT_too_big [PA_u 67108864] = [].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digits_aux_length : forall fuel b dig x acc, (length (Printf_model.digits_aux fuel b dig x acc) <= fuel + length acc)%nat.
Proof. induction fuel as [|fuel IH]; intros; cbn [Printf_model.digits_aux]; [lia|]. destruct (x =? 0); [cbn; lia|]. specialize (IH b dig (x / b) (dig (x mod b) :: acc)). cbn [length] in IH. lia. Qed.
Lemma digits_aux_length_ge : forall fuel b dig x acc, (length acc <= length (Printf_model.digits_aux fuel b dig x acc))%nat.
Proof. induction fuel as [|fuel IH]; intros; cbn [Printf_model.digits_aux]; [lia|]. destruct (x =? 0); [lia|]. specialize (IH b dig (x / b) (dig (x mod b) :: acc)). cbn [length] in IH. lia. Qed.
Lemma dec_digits_length : forall x, zlength (dec_digits x) <= 20.
Proof. intros x. unfold zlength, dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v) x []) as H. cbn [length Nat.add] in H. lia. Qed.
Lemma digits_aux_unfold : forall f b dig x acc,
  Printf_model.digits_aux (S f) b dig x acc = if x =? 0 then acc else Printf_model.digits_aux f b dig (x / b) (dig (x mod b) :: acc).
Proof. reflexivity. Qed.
Lemma dec_digits_pos : forall x, 0 < x -> 1 <= zlength (dec_digits x).
Proof.
  intros x Hx. unfold zlength, dec_digits. change 20%nat with (S 19). rewrite digits_aux_unfold.
  replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  pose proof (digits_aux_length_ge 19 10 (fun v => 48 + v) (x / 10) [48 + x mod 10]) as H. cbn [length] in H. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.
Lemma dec_digits_fmt_u : forall x, dec_digits x = fmt_u x.
Proof.
  intros x. unfold dec_digits, fmt_u.
  assert (G : forall fuel y acc, Printf_model.digits_aux fuel 10 (fun v => 48 + v) y acc = Stdio.digits_aux fuel y acc).
  { induction fuel as [|fuel IH]; intros; cbn [Printf_model.digits_aux Stdio.digits_aux]; [reflexivity|]. destruct (y =? 0); [reflexivity|]. apply IH. }
  apply G.
Qed.

Definition pct_d_conv_pieces (v : Z) : list (list Z) :=
  if v =? 0 then [[]; [48]; []] else if v <? 0 then [[45]; dec_digits (- v)] else [[]; dec_digits v].
Definition pct_d_conv_len (v : Z) : Z :=
  if v =? 0 then 1 else if v <? 0 then 1 + zlength (dec_digits (- v)) else zlength (dec_digits v).

(* [comment removed for export] *)
Lemma tail_pieces_plain : forall cnt p prefix body,
  0 <= cnt -> zlength prefix <= 2 -> zlength body <= 20 -> -1 <= p <= 21 -> cnt + 24 <= INT_MAX ->
  tail_pieces cnt 0 0 p prefix body =
    Some ([prefix] ++ (if Z.max p (zlength body) <=? zlength body then [] else [zrepeat 48 (Z.max p (zlength body) - zlength body)]) ++ [body],
          cnt + (zlength prefix + Z.max p (zlength body))).
Proof.
  intros cnt p prefix body Hc Hpl Hn Hp Hi.
  pose proof (zlength_nonneg' prefix) as P0. pose proof (zlength_nonneg' body) as B0.
  unfold tail_pieces. cbv zeta.
  replace (INT_MAX - zlength prefix <? Z.max p (zlength body)) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
  replace (Z.max 0 (zlength prefix + Z.max p (zlength body))) with (zlength prefix + Z.max p (zlength body)) by lia.
  match goal with |- context [if ?c then None else _] => replace c with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX in *; lia) end.
  unfold pad_pieces. rewrite !Z.leb_refl. cbn [Z.land Z.lxor Z.lor LEFT_ADJ ZERO_PAD Z.eqb negb orb].
  destruct (Z.leb_spec0 (Z.max p (zlength body)) (zlength body)) as [LE|GT].
  - cbn [app]. reflexivity.
  - replace (256 <=? Z.max p (zlength body) - zlength body) with false by (symmetry; apply Z.leb_gt; lia). cbn [app]. reflexivity.
Qed.

Lemma conv_pieces_d : forall cnt v, 0 <= cnt -> cnt + 24 <= INT_MAX -> -2^31 <= v < 2^31 ->
  conv_pieces cnt {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |} (PA_i v)
  = Some (pct_d_conv_pieces v, cnt + pct_d_conv_len v).
Proof.
  intros cnt v Hc Hi Hv.
  unfold conv_pieces, pct_d_conv_pieces, pct_d_conv_len, int_pieces.
  destruct (Z.eq_dec v 0) as [->|NZ].
  - cbv -[tail_pieces].
    rewrite tail_pieces_plain by (try change (zlength (@nil Z)) with 0; lia).
    change (zlength (@nil Z)) with 0. cbn. reflexivity.
  - destruct (Z.lt_ge_cases v 0) as [NEG|POS].
    + replace (v <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbv -[tail_pieces dec_digits Z.modulo Z.ltb Z.opp Z.pow zlength Z.add Z.max Z.eqb].
      change (10 =? 10) with true. change (0 =? 0) with true. cbv iota.
      assert (M1 : v mod 2^64 = v + 2^64) by (Z.div_mod_to_equations; nia).
      rewrite M1.
      replace (9223372036854775807 <? v + 2^64) with true by (symmetry; apply Z.ltb_lt; lia).
      replace ((- (v + 2^64)) mod 2^64) with (- v) by (Z.div_mod_to_equations; nia).
      replace (- v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      pose proof (dec_digits_pos (- v) ltac:(lia)) as DP. pose proof (dec_digits_length (- v)) as DL.
      rewrite Z.add_0_r.
      rewrite tail_pieces_plain by (try change (zlength [45]) with 1; lia).
      replace (Z.max (Z.max (-1) (zlength (dec_digits (- v)))) (zlength (dec_digits (- v)))) with (zlength (dec_digits (- v))) by lia.
      rewrite Z.leb_refl. change (zlength [45]) with 1. cbn [app]. reflexivity.
    + replace (v <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbv -[tail_pieces dec_digits Z.modulo Z.ltb Z.opp Z.pow zlength Z.add Z.max Z.eqb].
      change (10 =? 10) with true. change (0 =? 0) with true. cbv iota.
      rewrite (Z.mod_small v (2^64)) by lia.
      replace (9223372036854775807 <? v) with false by (symmetry; apply Z.ltb_ge; lia).
      change (0 =? 0) with true. cbv beta iota zeta.
      replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta.
      pose proof (dec_digits_pos v ltac:(lia)) as DP. pose proof (dec_digits_length v) as DL.
      rewrite ?Z.add_0_r.
      rewrite tail_pieces_plain by (try change (zlength (@nil Z)) with 0; lia).
      replace (Z.max (Z.max (-1) (zlength (dec_digits v))) (zlength (dec_digits v))) with (zlength (dec_digits v)) by lia.
      rewrite Z.leb_refl. change (zlength (@nil Z)) with 0. cbn [app]. rewrite ?Z.add_0_l. reflexivity.
Qed.

Definition pct_d_len (v : Z) : Z := pct_d_conv_len v + 1.

Lemma printf_pieces_pct_d : forall v, -2^31 <= v < 2^31 ->
  printf_pieces FMT_pct_d [PA_i v] = Some (pieces_pct_d v, pct_d_len v).
Proof.
  intros v Hv. unfold printf_pieces.
  change (Datatypes.length FMT_pct_d) with 4%nat.
  ppl_step. change 10 with T_INT at 1. fold (@app (list Z)).
  pose proof (zlength_nonneg' (dec_digits v)). pose proof (zlength_nonneg' (dec_digits (- v))).
  pose proof (dec_digits_length v). pose proof (dec_digits_length (- v)).
  rewrite conv_pieces_d by (unfold INT_MAX; lia).
  rewrite (ppl_noargs_shift 3 [10; 0] (0 + pct_d_conv_len v) [[10]] 1 ltac:(vm_compute; reflexivity))
    by (unfold pct_d_conv_len, INT_MAX; destruct (v =? 0); [lia|]; destruct (v <? 0); lia).
  unfold pieces_pct_d, pct_d_conv_pieces, pct_d_len, pct_d_conv_len.
  rewrite <- ?dec_digits_fmt_u.
  destruct (v =? 0); [cbn; reflexivity|]. destruct (v <? 0); cbn -[zlength Z.add dec_digits]; do 2 f_equal; lia.
Qed.


Lemma pass1_ok_pct_d : pass1_ok FMT_pct_d = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Printf_pieces ()) [] "p;2p;1p;3g00N;j22Tg02UXj11Tg00MAj30Tg00`FR0g01RoR1'2g03<c#1=001do"). Qed.
Lemma fp_calls_pct_d : forall v, fp_calls (Datatypes.length FMT_pct_d) FMT_pct_d [PA_i v] = [].
Proof. intros v. reflexivity. Qed.
