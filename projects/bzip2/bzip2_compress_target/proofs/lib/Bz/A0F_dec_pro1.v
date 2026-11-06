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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_dec_U13.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5 BzDU2 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFA DecTacFA DecTacFRA A0F_decV A0F_decRet.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decRet.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
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

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanCut.
Section ACeilS1. Context {ACEIL__ : ACeil}.

Lemma land_m32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (32 * (x / 32))%Z.
Proof.
  intros x Hx. change 18446744073709551584%Z with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5)%Z with 32%Z. lia.
Qed.
Lemma rw_cells_nilCB : forall segs m A cs, rw_cells segs m A cs -> rw_cells segs m A (CB 0 [] :: cs).
Proof.
  intros segs m A cs [[W B] Wr]. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity| exact W].
  - exact B.
  - exact Wr.
Qed.
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.

Section P1.
  Variable A : act14. Variable P : Z. Variable Q : machine_state -> Prop.
  Notation usp := (bv_unsigned (a_sp A)).
  Hypothesis YPl : (a_lo A <= P)%Z. Hypothesis YPh : (P + 832 <= usp)%Z. Hypothesis YPa : (usp <= P + 848)%Z.
  Hypothesis ALS : (usp mod 16 = 0)%Z. Hypothesis LOP : (6414336 <= a_lo A)%Z.   (* [comment removed for export] *)
  Notation cSB := (Z_to_bv 64 2147450880).

  Lemma A0F_pro1 : forall (qP : Z) (m : word -> option byte) (Fr : bvmap 5 word) (fc : bv 32)
      (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (P = 32 * qP)%Z ->
    stk a0segs m (a_lo A) usp -> mem_inv a0segs m -> aconsts A0C m -> aconsts_uar A0C m ->
    (forall m' (jb : list byte) (ng : nat) (jg : list byte) (b1 b2 : word),
      rw_cells a0segs m' P [CB 728 jb] ->
      rw_cells a0segs m' (P + 728) (CB ng jg :: FT_REGS A) -> (P + 728 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat ->
      stk a0segs m' (a_lo A) P -> mem_inv a0segs m' -> munch [(P, usp)]%Z m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x9e3d8) (Z_to_bv 64 P) gp tp t0 t1 t2 (a_sp A) (Z_to_bv 64 P) (Z_to_bv 64 64) b1 b2 a3 a4 a5 a6 a7
                            (a_s2 A) (a_s3 A) a0 cSB (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
                       Fr (Z_to_bv 64 0x3ddac) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (a_ra A) (a_sp A) gp tp t0 t1 t2 (a_s0 A) (a_s1 A) a0 a1 a2 a3 a4 a5 a6 a7
                          (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x9e368) fc None m (seg_rom a0segs)).
  Proof.
    intros qP m Fr fc gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EqP ST MI AC AU K.
    pose proof (bv_unsigned_in_range _ (a_sp A)) as UR. unfold bv_modulus in UR.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar A0C CmpCut.ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    assert (CASE : (P = usp - 832 \/ P = usp - 848)%Z) by lia.
    assert (ELAND : Z.land (usp + -832) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - CASE EqP ALS. Z.div_mod_to_equations. lia. }
    destruct CASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 832%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 832 _ [] [8; 720; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -832)%Z with P in FR, ST by lia.
      replace (Z_to_bv 64 (usp + -832 + 832)) with (a_sp A) by (rewrite <- (Z_to_bv_bv_unsigned (a_sp A)) at 1; f_equal; lia).
      (* [comment removed for export] *)
      arun_to 0x3ddac%Z.
      lazymatch type of FR with rw_cells _ ?mm _ (?c0 :: ?c1 :: ?rest) =>
        pose proof (rw_cells_merge a0segs mm P [] [c0; c1] rest FR) as FRm end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRm. clear FR.
      lazymatch type of FRm with rw_cells _ ?mm _ (CB 728 ?jb :: ?rest) =>
        pose proof (proj1 (DecTac2.rw_cells_app_iff a0segs mm P [CB 728 jb] rest) FRm) as [FRa FRb] end.
      cbn [cells_size csize Nat.add] in FRb. change (Z.of_nat 728) with 728%Z in FRb.
      apply rw_cells_nilCB in FRb.
      eapply (K _ _ 0%nat []); [exact FRa| exact FRb| cbn; lia| left; reflexivity| exact ST| assumption| exact MU| exact WM].
    - (* [comment removed for export] *)
      carve_frame 848%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 848 _ [] [16; 8; 704; 16; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -848)%Z with P in FR, ST by lia.
      replace (Z_to_bv 64 (usp + -832 + 832)) with (a_sp A) by (rewrite <- (Z_to_bv_bv_unsigned (a_sp A)) at 1; f_equal; lia).
      arun_to 0x3ddac%Z.
      lazymatch type of FR with rw_cells _ ?mm _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
        pose proof (rw_cells_merge a0segs mm P [] [c0; c1; c2] rest FR) as FRm end.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRm. clear FR.
      lazymatch type of FRm with rw_cells _ ?mm _ (CB 728 ?jb :: ?rest) =>
        pose proof (proj1 (DecTac2.rw_cells_app_iff a0segs mm P [CB 728 jb] rest) FRm) as [FRa FRb] end.
      cbn [cells_size csize Nat.add] in FRb. change (Z.of_nat 728) with 728%Z in FRb.
      eapply (K _ _ 16%nat _); [exact FRa| exact FRb| cbn; lia| right; reflexivity| exact ST| assumption| exact MU| exact WM].
  Qed.
End P1.
End ACeilS1.
