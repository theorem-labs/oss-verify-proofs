(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV DecTacSB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB.
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

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0_glue10K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_g10A.

Section ACeilS1. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition W10r (A : act14) : list ivl :=
  [(b_s (a_cx A) + 64036, b_s (a_cx A) + 64144)%Z; (a_fb A, a_fb A + 8)%Z; (a_shf A, a_shf A + 8)%Z].
Section R.
  Variable A : act14.
  Variable Q : machine_state -> Prop.
  Variable m0 : word -> option byte.
  Notation S := (b_s (a_cx A)).
  Notation P := (a_P A).
  Notation usp := (bv_unsigned (a_sp A)).
  Hypothesis GL : g10_lin A.
  Hypothesis ANS : sanchor S (a_shs A).
  Hypothesis ANF : sanchor (a_fb A) (a_shf A).
  Hypothesis SEPfs : (a_fb A + 64 <= S \/ S + 64144 <= a_fb A)%Z.
  Hypothesis SEPfsh : (a_fb A + 64 <= a_shf A \/ a_shf A + 8 <= a_fb A)%Z.
  Hypothesis SEPshs : (a_shf A + 8 <= S \/ S + 64144 <= a_shf A)%Z.
  Hypothesis SHS : shzW b0segs (W10 A) m0 S (S + 64144).

  Lemma B0F_g10_R : forall (rv : Z) (x1 x2 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 : word)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
      (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w520 w528 w712 w720 w728 w736 w744 w752 : word),
    munch (W10 A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m (S + 64036) [C4 c0; C4 c1; C4 c2; C4 c3; C4 c4; C4 c5; C4 c6; C4 c7; C4 c8; C4 c9; C4 c10; C4 c11; C4 c12; C4 c13; C4 c14; C4 c15; C4 c16; C4 c17; C4 c18; C4 c19; C4 c20; C8 c21; C8 c22; C8 c23] ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
    aframe A m ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    (forall (m' : word -> option byte) (fl : Z) (zt : word) (ng : nat) (jg j24 pos j38 : list byte)
            (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       rw_cells b0segs m' (S + 64036) [C4 w720; C4 w504; C4 w448; C4 w432; C4 w464; C4 w368; C4 w352; C4 w416; C4 w424; C4 w376; C4 w344; C4 w488; C4 w480; C4 w360; C4 w440; C4 zt; C4 w728; C4 w528; C4 w456; C4 w400; C4 w384; C8 w496; C8 w408; C8 w472] ->
       B0FL A m' w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
       B0FH A m' w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 (Z_to_bv 64 (a_fb A)) w520 w528 w712 w720 w728 w736 w744 w752 ->
       (P + 760 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
       ro_cells b0segs m' (a_fb A + 56) [C8 (Z_to_bv 64 fl)] ->
       rw_cells b0segs m' (P + 128) (FM_CELLS A zt) ->
       rw_cells b0segs m' (P + 760) (CB ng jg :: FT_REGS A) ->
       rw_cells b0segs m' (a_fb A) [C8 (Z_to_bv 64 1172321806); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 693392); CB 8 j24; CB 6 pos; CB 18 j38] ->
       rw_cells b0segs m' (a_shf A) [C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b] ->
       stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10r A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
       evt b0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 rv) (Z_to_bv 64 fl) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        Fr (Z_to_bv 64 0xafe0c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31)
          Fr (Z_to_bv 64 0xafb90) fc None m (seg_rom b0segs)).
  Proof.
    intros until w752. intros MU WM SAV FRL FRH AF ST MI K.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold W10 in MU, SHS.
    pose proof (SEPfs : id _) as BXfs. pose proof (SEPfsh : id _) as BXfsh. pose proof (SEPshs : id _) as BXshs.
    pose proof (munch_refl (W10r A) m) as MUL. pose proof (wmono_refl b0segs m) as WML. unfold W10r in MUL.
    open_aframe AF.
    (* [comment removed for export] *)
    brun. if_false_z.
    brun_to 0xafe0c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUf : munch (W10 A) m0 mm) by (unfold W10; exact MU) end.
    eapply evt_eq; [ | eapply (K _ fl zt ng jg j24 pos j38) ];
      [ st_eq | exact SAV | exact FRL | exact FRH | exact GEO | exact NG | exact FLP | unfold FM_CELLS; exact FRM | exact FRT | exact FF
      | unfold df5b; exact FS | exact ST | exact MUf | exact WM | exact MUL | exact WML | assumption ].
  Qed.
End R.
End ACeilS1.
