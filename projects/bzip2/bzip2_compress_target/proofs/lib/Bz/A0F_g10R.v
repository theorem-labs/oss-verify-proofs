(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet A0F_decRet3 DecTacSA A0F_decCutsA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decCutsA.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0_glue10K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0F_g10A.

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
  Hypothesis SHS : shzW a0segs (W10 A) m0 S (S + 64144).

  Lemma A0F_g10_R : forall (rv : Z) (x1 x2 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 : word)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
      (w496 w504 w512 w520 w528 w536 w544 w552 w560 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w680 w688 w696 w704 w712 w720 : word),
    munch (W10 A) m0 m -> wmono a0segs m0 m ->
    rw_cells a0segs m (S + 64036) [C4 c0; C4 c1; C4 c2; C4 c3; C4 c4; C4 c5; C4 c6; C4 c7; C4 c8; C4 c9; C4 c10; C4 c11; C4 c12; C4 c13; C4 c14; C4 c15; C4 c16; C4 c17; C4 c18; C4 c19; C4 c20; C8 c21; C8 c22; C8 c23] ->
    rw_cells a0segs m P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88] ->
    rw_cells a0segs m (P + 496) [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 w560; C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 w648; C8 w656; C8 w664; C8 (Z_to_bv 64 (a_fb A)); C8 w680; C8 w688; C8 w696; C8 w704; C8 w712; C8 w720] ->
    aframe A m ->
    stk a0segs m (a_lo A) P -> mem_inv a0segs m ->
    (forall (m' : word -> option byte) (fl : Z) (zt : word) (ng : nat) (jg j24 pos j38 : list byte)
            (y1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       rw_cells a0segs m' (S + 64036) [C4 w680; C4 w640; C4 w544; C4 w600; C4 w616; C4 w584; C4 w512; C4 w520; C4 w592; C4 w576; C4 w504; C4 w648; C4 w656; C4 w552; C4 w608; C4 zt; C4 w696; C4 w664; C4 w632; C4 w496; C4 w568; C8 w624; C8 w536; C8 w528] ->
       rw_cells a0segs m' P [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88] ->
       rw_cells a0segs m' (P + 496) [C8 w496; C8 w504; C8 w512; C8 w520; C8 w528; C8 w536; C8 w544; C8 w552; C8 w560; C8 w568; C8 w576; C8 w584; C8 w592; C8 w600; C8 w608; C8 w616; C8 w624; C8 w632; C8 w640; C8 w648; C8 w656; C8 w664; C8 (Z_to_bv 64 (a_fb A)); C8 w680; C8 w688; C8 w696; C8 w704; C8 w712; C8 w720] ->
       (P + 728 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
       ro_cells a0segs m' (a_fb A + 56) [C8 (Z_to_bv 64 fl)] ->
       rw_cells a0segs m' (P + 96) (FM_CELLS A zt) ->
       rw_cells a0segs m' (P + 728) (CB ng jg :: FT_REGS A) ->
       rw_cells a0segs m' (a_fb A) [C8 (Z_to_bv 64 1172321806); C8 (Z_to_bv 64 132751); C8 (Z_to_bv 64 648040); CB 8 j24; CB 6 pos; CB 18 j38] ->
       rw_cells a0segs m' (a_shf A) [C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b; C1 df5b] ->
       stk a0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono a0segs m0 m' -> munch (W10r A) m m' -> wmono a0segs m m' -> mem_inv a0segs m' ->
       evt a0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 rv) (Z_to_bv 64 fl) y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        Fr (Z_to_bv 64 0x9ee18) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 rv) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + 64036)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Fr (Z_to_bv 64 0x9eb38) fc None m (seg_rom a0segs)).
  Proof.
    intros until w720. intros MU WM SAV FRL FRH AF ST MI K.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0.
    unfold W10 in MU, SHS.
    pose proof (SEPfs : id _) as BXfs. pose proof (SEPfsh : id _) as BXfsh. pose proof (SEPshs : id _) as BXshs.
    pose proof (munch_refl (W10r A) m) as MUL. pose proof (wmono_refl a0segs m) as WML. unfold W10r in MUL.
    open_aframe AF.
    (* [comment removed for export] *)
    arun. if_false_z.
    arun_to 0x9ee18%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUf : munch (W10 A) m0 mm) by (unfold W10; exact MU) end.
    eapply evt_eq; [ | eapply (K _ fl zt ng jg j24 pos j38) ];
      [ st_eq | exact SAV | exact FRL | exact FRH | exact GEO | exact NG | exact FLP | unfold FM_CELLS; exact FRM | exact FRT | exact FF
      | unfold df5b; exact FS | exact ST | exact MUf | exact WM | exact MUL | exact WML | assumption ].
  Qed.
End R.
End ACeilS1.
