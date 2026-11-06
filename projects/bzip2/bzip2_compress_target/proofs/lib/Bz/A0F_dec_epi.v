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
Section ACeilS1. Context {ACEIL__ : ACeil}.
Section R.
  Variable A : act14.
  Variable Q : machine_state -> Prop.
  Notation usp := (bv_unsigned (a_sp A)).

  Lemma A0F_rel_flag : forall (m : word -> option byte) (fl : Z) (b1 : byte) (Fr : bvmap 5 word) (fc : bv 32)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m fl [C1 b1] -> mem_inv a0segs m ->
    (forall m', rw_cells a0segs m' fl [C1 z8] -> mem_inv a0segs m' -> munch [(fl, fl + 1)]%Z m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        Fr (Z_to_bv 64 0x9ee1c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 fl) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x9ee18) fc None m (seg_rom a0segs)).
  Proof.
    intros m fl b1 Fr fc ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLC MI K.
    pose proof (munch_refl [(fl, fl + 1)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    wstep. change (le1 (Z_to_bv 64 0)) with [z8]. mem_after_store.
    eapply K; [exact FLC| exact MI| exact MU| exact WM].
  Qed.

  Lemma stk_join8 : forall segs m a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> (a <= b <= c)%Z -> stk segs m a c.
  Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
  Ltac stk_add8 ST K :=
    lazymatch type of K with stk _ _ ?b' ?c =>
    lazymatch type of ST with stk ?segs ?m ?lo ?b =>
      let H := fresh in pose proof (stk_join8 segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.

  Lemma A0F_epi : forall (m : word -> option byte) (Fr : bvmap 5 word) (fc : bv 32) (zt : word) (ng : nat) (jg : list byte)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word)
      (w496 w504 w512 w520 w528 w536 w544 w552 w560 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w672 w680 w688 w696 w704 w712 w720 : word)
      (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (a_P A + 728 + Z.of_nat ng + 104 = usp)%Z -> (ng = 0 \/ ng = 16)%nat -> (a_lo A <= a_P A)%Z ->
    A0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 ->
    rw_cells a0segs m (a_P A + 96) (FM_CELLS A zt) ->
    A0FH A m w496 w504 w512 w520 w528 w536 w544 w552 w560 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w672 w680 w688 w696 w704 w712 w720 ->
    rw_cells a0segs m (a_P A + 728) (CB ng jg :: FT_REGS A) ->
    stk a0segs m (a_lo A) (a_P A) ->
    (stk a0segs m (a_lo A) usp ->
      evt a0segs Q (MS (mkR (a_ra A) (a_sp A) gp tp t0 t1 t2 (a_s0 A) (a_s1 A) a0 a1 a2 a3 a4 a5 a6 a7
                            (a_s2 A) (a_s3 A) (a_s4 A) (a_s5 A) (a_s6 A) (a_s7 A) (a_s8 A) (a_s9 A) (a_s10 A) (a_s11 A) t3 t4 t5 t6)
                       Fr (ret_pc (a_ra A)) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (a_sp A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x9ee1c) fc None m (seg_rom a0segs)).
  Proof.
    intros m Fr fc zt ng jg w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88
           w496 w504 w512 w520 w528 w536 w544 w552 w560 w568 w576 w584 w592 w600 w608 w616 w624 w632 w640 w648 w656 w664 w672 w680 w688 w696 w704 w712 w720
           ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 GEO NG PP FRL FRM FRH FRT ST K.
    pose proof (bv_unsigned_in_range _ (a_sp A)) as UR. unfold bv_modulus in UR.
    (* [comment removed for export] *)
    assert (SAV : rw_cells a0segs m (usp + -104) (FT_REGS A)).
    { pose proof (proj2 (proj1 (DecTac2.rw_cells_app_iff a0segs m (a_P A + 728) [CB ng jg] (FT_REGS A)) FRT)) as X.
      cbn [cells_size csize] in X. replace (usp + -104)%Z with (a_P A + 728 + Z.of_nat (ng + 0))%Z by lia. exact X. }
    unfold FT_REGS in SAV.
    (* [comment removed for export] *)
    wstep. wstep. do 13 wstep. wstep.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells a0segs _ _ _ FRL) as K0. cbn [cells_size csize Nat.add] in K0.
    pose proof (stk_of_rw_cells a0segs _ _ _ FRM) as K1. unfold FM_CELLS in K1. cbn [cells_size csize Nat.add] in K1.
    pose proof (stk_of_rw_cells a0segs _ _ _ FRH) as K2. cbn [cells_size csize Nat.add] in K2.
    pose proof (stk_of_rw_cells a0segs _ _ _ FRT) as K3. unfold FT_REGS in K3. cbn [cells_size csize Nat.add] in K3.
    change (Z.of_nat 96) with 96%Z in K0. change (Z.of_nat 400) with 400%Z in K1. change (Z.of_nat 232) with 232%Z in K2.
    stk_add8 ST K0. stk_add8 ST K1. stk_add8 ST K2. stk_add8 ST K3.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with usp in ST by lia end.
    replace (Z_to_bv 64 (usp + -832 + 832)) with (a_sp A) by (rewrite <- (Z_to_bv_bv_unsigned (a_sp A)) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep.
    exact (K ST).
  Qed.
End R.
End ACeilS1.
