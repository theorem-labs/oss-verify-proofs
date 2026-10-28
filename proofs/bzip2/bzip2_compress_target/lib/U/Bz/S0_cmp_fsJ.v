(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCFactsFs BzCFactsFs2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_fsB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).

  Lemma S0_fs_eclass : forall (r : nat) (i j Hh : Z) (fm ec bh : zarr) (me m : word -> option byte)
      (ra t0 t2 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = nb)%Z -> (0 <= i)%Z -> (1 <= r)%nat -> (0 <= j < nb)%Z -> (1 <= Hh <= nb)%Z ->
    zbok fm -> zbok ec -> bh_w32 bh -> (forall x, 0 <= x < nb -> 0 <= rd32 fm x < nb)%Z ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    munch [(A2, A2 + ARR2_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x10 x11 x12 x13 x14 x15 x16 x17 : word), let ec' := fs_eclass r ec fm bh Hh nb i j in
      u8arr s0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 bh 65537) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE)]%Z me m' -> wmono s0segs me m' -> zbok ec' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2)
                            x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) s5 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22790) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2)
                          (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (nb - i)) (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 (A1 + 4 * i)) a5 a6 a7
                          (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) s5 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x226e8) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i j Hh fm ec bh me m ra t0 t2 a5 a6 a7 s5 s8 t3 t4 t5 t6 Hi Hi0 Hr Hj HH FMOK' ECOK' BW FMR AR1 AR2 FTB MI MU WM K.
    fsenv_open XOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    assert (Hw : (0 <= i / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    pose proof (FMR i ltac:(lia)) as Fv.
    (* [comment removed for export] *)
    urun_to 0x2270c%Z.
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m FT bh 65537 (i / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (BW (i / 32)%Z) as Bw.
    (* [comment removed for export] *)
    wstep. wstep.
    try (replace (Z.land i 31) with (i mod 32)%Z by (change 31%Z with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity)). try rewrite (Z.mod_mod i 32) by lia.
    rewrite (isset_test_val (zget bh (i / 32)) i) by lia.
    rewrite fs_eclass_S in K. rewrite (isset_bh_testbit bh i) in K by lia.
    (* [comment removed for export] *)
    assert (TAIL : forall j' (x15 x16 x17 : word), (0 <= j' < nb)%Z -> j' = (if Z.testbit (zget bh (i / 32)) (i mod 32) then i else j) ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2)
                            (Z_to_bv 64 i) (Z_to_bv 64 j') (Z_to_bv 64 (nb - i)) (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 (A1 + 4 * i)) x15 x16 x17
                            (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) s5 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22720) fc None m (seg_rom s0segs))).
    { intros j' x15 x16 x17 Hj' Ej'. rewrite <- Ej' in K.
      (* [comment removed for export] *)
      urun_to 0x22730%Z.
      pose proof (zb8_read4 s0segs m A1 fm ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) FMOK' ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD.
      (* [comment removed for export] *)
      urun_to 0x22748%Z.
      rewrite (sign_sel (rd32 fm i - Hh) nb) by lia.
      set (sel := (if (rd32 fm i - Hh <? 0)%Z then nb else 0%Z)).
      assert (SEL : ((rd32 fm i - Hh < 0)%Z /\ sel = nb) \/ ((0 <= rd32 fm i - Hh)%Z /\ sel = 0%Z)) by (subst sel; destruct (Z.ltb_spec (rd32 fm i - Hh) 0); lia).
      assert (Esel : (rd32 fm i - Hh + sel)%Z = (if (rd32 fm i - Hh <? 0)%Z then (rd32 fm i - Hh + nb)%Z else (rd32 fm i - Hh)%Z)) by (subst sel; destruct (Z.ltb_spec (rd32 fm i - Hh) 0); lia).
      clearbody sel.
      (* [comment removed for export] *)
      urun_to 0x22778%Z.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u8arr_storeN_ok s0segs mm A2 _ (4 * (rd32 fm i - Hh + sel)) 4 _ AR2 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(f_equal; lia)) as SO end.
      wstep. zb8_store4 AR2 (rd32 fm i - Hh + sel)%Z. rewrite (unsigned_lit j') in AR2 by lia. rewrite Esel in AR2.
      (* [comment removed for export] *)
      urun_to 0x2278c%Z.
      wstep; if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z j' Hh fm _ bh me); [st_eq| lia| lia| lia| lia| lia| exact FMOK'| | exact BW| exact FMR| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM| ].
        + apply zbok_wr32. exact ECOK'.
        + intros m' x5 x10 x11 x12 x13 x14 y15 y16 y17. exact (K m' x5 x10 x11 x12 x13 x14 y15 y16 y17).
      - assert (r = 0)%nat by lia. subst r. cbn [fs_eclass] in K.
        enter_with (K _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM| apply zbok_wr32; exact ECOK']. }
    (* [comment removed for export] *)
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      destruct (Z.testbit (zget bh (i / 32)) (i mod 32)) eqn:Eb; [cbn in Kb; lia|].
      apply (TAIL j _ _ _); [lia| reflexivity].
    - destruct (Z.testbit (zget bh (i / 32)) (i mod 32)) eqn:Eb; [|cbn in Kb; lia].
      (* [comment removed for export] *)
      wstep. apply (TAIL i _ _ _); [lia| reflexivity].
  Qed.
End S0FS.

End ACeilS1.
End S0_cmp_fsB.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsD S0_cmp_fsF S0_cmp_fsI.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsJ.S0_cmp_fsB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsI.
From Stdlib Require Lia. 
Module S0_cmp_fsA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation ec0 := (fe_ec X). Notation fm0 := (fe_fm X).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fs_count : forall (r : nat) (i : Z) (ft : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = nb)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    (forall b, 0 <= zget ft b <= i)%Z ->
    u8arr s0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr s0segs m (p + 1124) (zw32 ft 257) -> mem_inv s0segs m ->
    munch [(p + 1124, p + 2152)]%Z me m -> wmono s0segs me m ->
    (forall m' (x12 x13 x14 x15 x16 x17 : word), let ft' := fs_count r ft ec0 i in
      u8arr s0segs m' A2 (zb8 ec0 ARR2_SIZE) -> u32arr s0segs m' (p + 1124) (zw32 ft' 257) -> mem_inv s0segs m' ->
      munch [(p + 1124, p + 2152)]%Z me m' -> wmono s0segs me m' ->
      (forall b, 0 <= zget ft' b <= nb)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 1) (Z_to_bv 64 (p + 1124)) x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x223c0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 1) (Z_to_bv 64 (p + 1124))
                          (Z_to_bv 64 (nb - i)) (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 (A2 + i)) a5 a6 a7
                          (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22370) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft me m ra t0 t1 t2 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr Hft AR2 FTL MI MU WM K.
    fsenv_open XOK. bz_params.
    pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    (* [comment removed for export] *)
    urun_to 0x22390%Z.
    pose proof (zb8_read1 s0segs m A2 ec0 ARR2_SIZE i _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. pose proof (ECOK i) as Bi. rewrite (unsigned_lit8 (zget ec0 i)) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m (p + 1124) ft 257 (zget ec0 i) _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (Hft (zget ec0 i)) as Fb. try rewrite (sx32_of_Z (zget ft (zget ec0 i))) by lia.
    (* [comment removed for export] *)
    urun_to 0x223ac%Z.
    pose proof (u32arr_store_ok s0segs m (p + 1124) _ (zget ec0 i) _ FTL ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTL (zget ec0 i) (zget ft (zget ec0 i) + 1)%Z wval_lit.
    rewrite fs_count_S in K.
    (* [comment removed for export] *)
    urun_to 0x223bc%Z.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zincr ft (rd8 ec0 i)) me); [st_eq| lia| lia| lia| | exact AR2| | exact MI| exact MU| exact WM| ].
      + intros b'. unfold zincr, rd8. rewrite zget_zset. pose proof (Hft b'). destruct (Z.eqb_spec b' (zget ec0 i)); [subst b'; lia| lia].
      + unfold zincr, rd8. exact FTL.
      + intros m' x12 x13 x14 x15 x16 x17. exact (K m' x12 x13 x14 x15 x16 x17).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_count] in K.
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact AR2| | exact MI| exact MU| exact WM|].
      + unfold zincr, rd8. exact FTL.
      + intros b'. unfold zincr, rd8. rewrite zget_zset. pose proof (Hft b'). destruct (Z.eqb_spec b' (zget ec0 i)); [subst b'; lia| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fs_accum : forall (r : nat) (i : Z) (ft : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 257)%Z -> (1 <= i)%Z -> (1 <= r)%nat ->
    (forall b, i <= b -> 0 <= zget ft b <= nb)%Z -> (0 <= zget ft (i - 1) <= i * nb)%Z ->
    u32arr s0segs m (p + 1124) (zw32 ft 257) -> mem_inv s0segs m ->
    munch [(p + 1124, p + 2152)]%Z me m -> wmono s0segs me m ->
    (forall m' (x10 x11 x12 x13 x14 : word), let ft' := fs_accum r ft i in
      u32arr s0segs m' (p + 1124) (zw32 ft' 257) -> mem_inv s0segs m' ->
      munch [(p + 1124, p + 2152)]%Z me m' -> wmono s0segs me m' ->
      (forall b, 0 <= b < 257 -> 0 <= zget ft' b <= (b + 1) * nb)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) x10 x11 x12 x13 x14 a5 a6 a7
                            (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22410) fc None m' (seg_rom s0segs))) ->
    (forall b, 0 <= b < i -> 0 <= zget ft b <= (b + 1) * nb)%Z ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 (257 - i)) (Z_to_bv 64 (p + 1124 + 4 * i)) a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x223e8) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft me m ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi1 Hr Hft Hacc FTL MI MU WM K Hdone.
    fsenv_open XOK.
    pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m (p + 1124) ft 257 (i - 1) _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget ft (i - 1))) by lia.
    pose proof (zw32_read s0segs m (p + 1124) ft 257 i _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (Hft i ltac:(lia)) as Fi. try rewrite (sx32_of_Z (zget ft i)) by lia.
    (* [comment removed for export] *)
    assert (HS : (zget ft i + zget ft (i - 1) <= 257 * nb)%Z) by nia.
    urun_to 0x22400%Z.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 1124) _ i _ FTL ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTL i (zget ft i + zget ft (i - 1))%Z wval_lit.
    rewrite fs_accum_S in K.
    (* [comment removed for export] *)
    urun_to 0x2240c%Z.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset ft i (zget ft i + zget ft (i - 1))) me); [st_eq| lia| lia| lia| | | exact FTL| exact MI| exact MU| exact WM| |].
      + intros b' Hb'. rewrite zget_zset. destruct (Z.eqb_spec b' i); [lia|]. apply Hft. lia.
      + rewrite zget_zset. replace (i + 1 - 1 =? i)%Z with true by (symmetry; apply Z.eqb_eq; lia). lia.
      + intros m' x10 x11 x12 x13 x14. exact (K m' x10 x11 x12 x13 x14).
      + intros b' Hb'. rewrite zget_zset. destruct (Z.eqb_spec b' i); [subst b'; lia|]. apply Hdone. lia.
    - assert (r = 0)%nat by lia. subst r. cbn [fs_accum] in K.
      enter_with (K _ _ _ _ _ _); [st_eq| exact FTL| exact MI| exact MU| exact WM|].
      intros b' Hb'. rewrite zget_zset. destruct (Z.eqb_spec b' i); [subst b'; lia|]. apply Hdone. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fs_distrib : forall (r : nat) (i : Z) (ft fm : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = nb)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    fsf_distrib fm0 ec0 nb -> fp_dist fm0 ec0 nb (Z.to_nat i) = (ft, fm) ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec0 ARR2_SIZE) -> u32arr s0segs m (p + 1124) (zw32 ft 257) -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 1124, p + 2152)]%Z me m -> wmono s0segs me m ->
    (forall m' (x5 x6 x7 x10 x15 x16 x17 x28 : word), let r' := fs_distrib r ft fm ec0 i in
      u8arr s0segs m' A1 (zb8 (snd r') ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec0 ARR2_SIZE) -> u32arr s0segs m' (p + 1124) (zw32 (fst r') 257) -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 1124, p + 2152)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 nb) (Z_to_bv 64 A2) x10 (Z_to_bv 64 (p + 1124)) (Z_to_bv 64 1) (Z_to_bv 64 (18446744073709551615 - (p + 1124))) (Z_to_bv 64 1) x15 x16 x17
                            (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 x28 t4 t5 t6)
                       F (Z_to_bv 64 0x224d4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 i) (Z_to_bv 64 (p + 1124)) (Z_to_bv 64 1) (Z_to_bv 64 (18446744073709551615 - (p + 1124))) (Z_to_bv 64 1)
                          (Z_to_bv 64 (nb - i)) (Z_to_bv 64 (A2 + i)) (Z_to_bv 64 (A2 + i))
                          (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22434) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft fm me m ra t0 t1 t2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr FD CUR AR1 AR2 FTL MI MU WM K.
    fsenv_open XOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & _ & _). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec0 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 257 ltac:(lia)) as LF.
    pose proof (FD i ltac:(lia)) as Fk. rewrite CUR in Fk. cbn [fst] in Fk.
    (* [comment removed for export] *)
    urun_to 0x22454%Z.
    pose proof (zb8_read1 s0segs m A2 ec0 ARR2_SIZE i _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. pose proof (ECOK i) as Bi. rewrite (unsigned_lit8 (zget ec0 i)) by lia.
    change (rd8 ec0 i) with (zget ec0 i) in Fk.
    (* [comment removed for export] *)
    urun_to 0x22468%Z.
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m (p + 1124) ft 257 (zget ec0 i) _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget ft (zget ec0 i))) by lia.
    (* [comment removed for export] *)
    urun_to 0x22484%Z.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 1124) _ (zget ec0 i) _ FTL ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTL (zget ec0 i) (zget ft (zget ec0 i) - 1)%Z wval_lit.
    (* [comment removed for export] *)
    urun_to 0x224bc%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok s0segs mm A1 _ (4 * (zget ft (zget ec0 i) - 1)) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(f_equal; lia)) as SO2
    end.
    wstep. zb8_store4 AR1 (zget ft (zget ec0 i) - 1)%Z. rewrite (unsigned_lit i) in AR1 by lia.
    rewrite fs_distrib_S in K. cbv zeta in K. change (rd8 ec0 i) with (zget ec0 i) in K.
    (* [comment removed for export] *)
    urun_to 0x224d0%Z.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z (zset ft (zget ec0 i) (zget ft (zget ec0 i) - 1)) (wr32 fm (zget ft (zget ec0 i) - 1) i) me);
        [st_eq| lia| lia| lia| exact FD| | exact AR1| exact AR2| exact FTL| exact MI| exact MU| exact WM| ].
      + rewrite fp_dist_step, CUR by lia. reflexivity.
      + intros m' x5 x6 x7 x10 x15 x16 x17 x28. exact (K m' x5 x6 x7 x10 x15 x16 x17 x28).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_distrib] in K.
      enter_with (K _ _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact FTL| exact MI| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fs_bhinit : forall (r : nat) (i : Z) (ft bh : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 256)%Z -> (0 <= i)%Z -> (1 <= r)%nat ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft b <= nb)%Z -> bh_w32 bh ->
    u32arr s0segs m (p + 1124) (zw32 ft 257) -> u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x10 x11 x14 x15 x16 x17 : word), let bh' := fs_bh_init r bh ft i in
      u32arr s0segs m' (p + 1124) (zw32 ft 257) -> u32arr s0segs m' FT (zw32 bh' 65537) -> mem_inv s0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' -> bh_w32 bh' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) x10 x11 (Z_to_bv 64 1) (Z_to_bv 64 1) x14 x15 x16 x17
                            (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x225b8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1124 + 4 * i)) (Z_to_bv 64 (256 - i)) (Z_to_bv 64 1) (Z_to_bv 64 1) a4 a5 a6 a7
                          (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x22554) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i ft bh me m ra t0 t1 t2 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr Hft BW FTL FTB MI MU WM K.
    fsenv_open XOK.
    pose proof (zw32_length ft 257 ltac:(lia)) as LF. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    pose proof (Hft i ltac:(lia)) as Fi.
    assert (Hw : (0 <= zget ft i / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m (p + 1124) ft 257 i _ FTL ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (zx32_of_Z (zget ft i)) by lia.
    (* [comment removed for export] *)
    urun_to 0x2259c%Z.
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m FT bh 65537 (zget ft i / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (BW (zget ft i / 32)%Z) as Bw.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m FT _ (zget ft i / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTB (zget ft i / 32)%Z (Z.lor (zget bh (zget ft i / 32)) (Z.shiftl 1 (Z.land (zget ft i) 31)))%Z (first [apply set_bh_store_b| apply set_bh_store_a]).
    rewrite fs_bh_init_S in K. unfold set_bh, bh_word in K. rewrite shiftr5_div in K.
    assert (BW' : bh_w32 (zset bh (zget ft i / 32) (Z.lor (zget bh (zget ft i / 32)) (Z.shiftl 1 (Z.land (zget ft i) 31))))).
    { pose proof (set_bh_w32 bh (zget ft i) BW) as Y. unfold set_bh, bh_word in Y. rewrite shiftr5_div in Y. exact Y. }
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ft _ me); [st_eq| lia| lia| lia| exact Hft| exact BW'| exact FTL| exact FTB| exact MI| exact MU| exact WM| ].
      intros m' x10 x11 x14 x15 x16 x17. exact (K m' x10 x11 x14 x15 x16 x17).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_bh_init] in K.
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact FTL| exact FTB| exact MI| exact MU| exact WM| exact BW'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_fs_sentinel : forall (r : nat) (i : Z) (bh : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = 32)%Z -> (0 <= i)%Z -> (1 <= r)%nat -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x10 x13 x14 x15 x16 : word), let bh' := fs_sentinel r bh nb i in
      u32arr s0segs m' FT (zw32 bh' 65537) -> mem_inv s0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' -> bh_w32 bh' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) x10 (Z_to_bv 64 1) (Z_to_bv 64 64) x13 x14 x15 x16 a7
                            (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22650) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 (2 * i)) (Z_to_bv 64 1) (Z_to_bv 64 64) a3 a4 a5 a6 a7
                          (Z_to_bv 64 A1) s3 (Z_to_bv 64 FT) s5 s6 (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x225c4) fc None m (seg_rom s0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i bh me m ra t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Hi Hi0 Hr BW FTB MI MU WM K.
    fsenv_open XOK.
    pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    assert (Hw1 : (0 <= (nb + 2 * i) / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    assert (Hw2 : (0 <= (nb + 2 * i + 1) / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    urun_to 0x225f4%Z.
    (* [comment removed for export] *)
    pose proof (zw32_read s0segs m FT bh 65537 ((nb + 2 * i) / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (BW ((nb + 2 * i) / 32)%Z) as Bw1.
    (* [comment removed for export] *)
    urun_to 0x22608%Z.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m FT _ ((nb + 2 * i) / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store FTB ((nb + 2 * i) / 32)%Z (Z.lor (zget bh ((nb + 2 * i) / 32)) (Z.shiftl 1 (Z.land (nb + 2 * i) 31)))%Z (first [apply set_bh_store_b| apply set_bh_store_a]).
    set (bh1 := zset bh _ _) in FTB.
    assert (BW1 : bh_w32 bh1).
    { pose proof (set_bh_w32 bh (nb + 2 * i) BW) as Y. unfold set_bh, bh_word in Y. rewrite shiftr5_div in Y. exact Y. }
    (* [comment removed for export] *)
    urun_to 0x22634%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read s0segs mm FT bh1 65537 ((nb + 2 * i + 1) / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. pose proof (BW1 ((nb + 2 * i + 1) / 32)%Z) as Bw2.
    (* [comment removed for export] *)
    urun_to 0x22648%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm FT _ ((nb + 2 * i + 1) / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO2 end.
    wstep. zw32_store FTB ((nb + 2 * i + 1) / 32)%Z (Z.land (zget bh1 ((nb + 2 * i + 1) / 32)) (Z.lxor (Z.shiftl 1 (Z.land (nb + 2 * i + 1) 31)) 4294967295))%Z (apply clear_bh_store_b).
    assert (BW2 : bh_w32 (zset bh1 ((nb + 2 * i + 1) / 32) (Z.land (zget bh1 ((nb + 2 * i + 1) / 32)) (Z.lxor (Z.shiftl 1 (Z.land (nb + 2 * i + 1) 31)) 4294967295)))).
    { pose proof (clear_bh_w32 bh1 (nb + 2 * i + 1) BW1) as Y. unfold clear_bh, bh_word in Y. rewrite shiftr5_div in Y. exact Y. }
    rewrite fs_sentinel_S in K. unfold clear_bh, set_bh, bh_word in K. rewrite !shiftr5_div in K. subst bh1.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z _ me); [st_eq| lia| lia| lia| exact BW2| exact FTB| exact MI| exact MU| exact WM| ].
      intros m' x10 x13 x14 x15 x16. exact (K m' x10 x13 x14 x15 x16).
    - assert (r = 0)%nat by lia. subst r. cbn [fs_sentinel] in K.
      enter_with (K _ _ _ _ _ _); [st_eq| exact FTB| exact MI| exact MU| exact WM| exact BW2].
  Qed.
End S0FS.

End ACeilS1.
End S0_cmp_fsA.

Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop.
  Variables (str sv : word) (Jlo Jhi : list byte).
  (* [comment removed for export] *)
  Variables (fm0 ec0 bh0 : zarr).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  Hypothesis FEC : fsf_ec fm0 ec0 bh0 nb. Hypothesis FBK : fsf_bucket fm0 ec0 bh0 nb.
  (* [comment removed for export] *)
  Notation HH Hh ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) s5 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).
  Notation Wh := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_A2 X, fe_A2 X + ARR2_SIZE); (fe_FT X, fe_FT X + 262148);
                  (bv_unsigned (fe_sp X) - 3056 + 40, bv_unsigned (fe_sp X) - 3056 + 72);
                  (bv_unsigned (fe_sp X) - 3056 + 2152, bv_unsigned (fe_sp X) - 3056 + 2952)]%Z.
  Definition hmem (fm ec bh slo shi : zarr) (hc nd rr tv : Z) (m : word -> option byte) : Prop :=
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) /\ u8arr s0segs m A2 (zb8 ec ARR2_SIZE) /\ u32arr s0segs m FT (zw32 bh 65537) /\
    rw_cells s0segs m (p + 8) (SCq X hc str sv nd rr tv) /\
    u32arr s0segs m (p + 2152) (ovw shi Jhi 100) /\ u32arr s0segs m (p + 2552) (ovw slo Jlo 100) /\ mem_inv s0segs m.
  Definition hinv (fm ec bh : zarr) (Hh : Z) : Prop := fm_range fm nb /\ zbok fm /\ zbok ec /\ bh_w32 bh /\ (1 <= Hh <= nb)%Z.

  Ltac hmem_i AR1 AR2 FTB SC SHI SLO MI :=
    split; [exact AR1| split; [exact AR2| split; [exact FTB| split; [exact SC| split; [exact SHI| split; [exact SLO| exact MI]]]]]].

  Lemma S0_hloop : forall (f t : nat) (hfin : fhs) (hc nd rr tv : Z) (me m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    let h := fp_hs fm0 ec0 bh0 nb t in
    fh_done h = false -> fs_H_loop f nb h = hfin -> fh_done hfin = true ->
    hinv (fh_fm h) (fh_ec h) (fh_bh h) (fh_H h) -> hmem (fh_fm h) (fh_ec h) (fh_bh h) (fh_slo h) (fh_shi h) hc nd rr tv m ->
    munch Wh me m -> wmono s0segs me m ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31 : word),
      hmem (fh_fm hfin) (fh_ec hfin) (fh_bh hfin) (fh_slo hfin) (fh_shi hfin) hc' nd' rr' tv' m' -> munch Wh me m' -> wmono s0segs me m' ->
      fm_range (fh_fm hfin) nb -> zbok (fh_fm hfin) -> zbok (fh_ec hfin) -> bh_w32 (fh_bh hfin) ->
      evt s0segs Q (MS (HH (fh_H hfin) x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x28 x29 x30 x31) F (Z_to_bv 64 0x234c0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (HH (fh_H h) ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x226c8) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros t hfin hc nd rr tv me m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 h Hd RES FIN HI HM MU WM K.
    { cbn [fs_H_loop] in RES. subst hfin. rewrite Hd in FIN. discriminate. }
    rewrite fs_H_loop_S, Hd in RES.
    cps_destruct HI as (FMR & FMOK' & ECOK' & BW & HHh). cps_destruct HM as (AR1 & AR2 & FTB & SC & SHI & SLO & MI).
    fsenv_open XOK. bz_params.
    pose proof (zb8_length (fh_fm h) ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length (fh_ec h) ARR2_SIZE ltac:(lia)) as L2.
    pose proof (zw32_length (fh_bh h) 65537 ltac:(lia)) as LB.
    pose proof (ovw_length (fh_shi h) Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length (fh_slo h) Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    urun_to 0x226d0%Z. wstep; if_cases Knb; zify_cond_z Knb; [exfalso; lia|].
    (* [comment removed for export] *)
    urun_to 0x226e8%Z.
    enter_with (S0_fs_eclass X Q XOK XSEP (Z.to_nat nb) 0 0 (fh_H h) (fh_fm h) (fh_ec h) (fh_bh h) m m);
      [st_eq| lia| lia| lia| lia| exact HHh| exact FMOK'| exact ECOK'| exact BW| exact (proj2 FMR)| exact AR1| exact AR2| exact FTB| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1 y5 y10 y11 y12 y13 y14 y15 y16 y17. cbv zeta. intros AR1_1 AR2_1 FTB1 MI1 MU1 WM1 ECOK1.
    bz_params. clear AR1 AR2 FTB MI. transport_after_call s0segs m m1 MU1 WM1.
    set (ec' := fs_eclass (Z.to_nat nb) (fh_ec h) (fh_fm h) (fh_bh h) (fh_H h) nb 0 0) in *.
    assert (Eec : ec' = fp_ecT fm0 ec0 bh0 nb t) by reflexivity.
    assert (ECR1 : ec_range ec' nb). { rewrite Eec. exact (FEC t Hd). }
    (* [comment removed for export] *)
    wstep. wstep.
    set (s0 := FBS (fh_fm h) ec' (fh_bh h) (fh_slo h) (fh_shi h) (-1) 0 false).
    set (sfin := fs_bucket_loop (Z.to_nat (nb + 2)) nb s0).
    assert (BF : forall v, fb_done (fs_bucket_loop v nb s0) = false -> bucket_ok nb (fs_bucket_loop v nb s0)).
    { intros v Hv. exact (FBK t v Hd Hv). }
    enter_with (S0_bloop X Q (fh_H h) str sv ec' Jlo Jhi XOK XSEP ECR1 ECOK1 LJlo LJhi (Z.to_nat (nb + 2)) s0 sfin hc nd rr tv m1 m1);
      [st_eq| reflexivity| reflexivity| exact BF| reflexivity| | | | apply munch_refl| apply wmono_refl|].
    { apply fs_bucket_loop_term; [lia| reflexivity| reflexivity| exact BF]. }
    { split; [exact FMR| split; [exact FMOK'| split; [exact BW| cbn; lia]]]. }
    { split; [exact AR1_1| split; [exact AR2_1| split; [exact FTB1| split; [exact SC| split; [exact SHI| split; [exact SLO| exact MI1]]]]]]. }
    intros m2 hc2 nd2 rr2 tv2 z1 z5 z7 z10 z11 z12 z13 z14 z15 z16 z21 z24 z28 z29 z30 z31 Hec2 BI2 BM2 MU2 WM2.
    cps_destruct BI2 as (FMR2 & FMOK2 & BW2 & Hnnd2). cps_destruct BM2 as (AR1_2 & AR2_2 & FTB2 & SC2 & SHI2 & SLO2 & MI2). bz_params.
    clear AR1_1 AR2_1 FTB1 SC SHI SLO MI1 MU1 WM1. transport_after_call s0segs m1 m2 MU2 WM2.
    pose proof AR2_2 as AR2_3. rewrite <- Hec2 in AR2_3.
    (* [comment removed for export] *)
    urun_to 0x23470%Z. try rewrite (sx32_of_Z (fb_nnd sfin)) by lia.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z (fh_H h * 2)) by lia.
    assert (NXT : fs_H_iter nb h = FHS (fb_fm sfin) (fb_ec sfin) (fb_bh sfin) (fb_slo sfin) (fb_shi sfin) (fh_H h * 2) ((nb <? fh_H h * 2) || (fb_nnd sfin =? 0))%Z) by reflexivity.
    (* [comment removed for export] *)
    wstep; if_cases KH; zify_cond_z KH.
    - (* [comment removed for export] *)
      rewrite NXT in RES. cbn [fh_done] in RES. replace (nb <? fh_H h * 2)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in RES.
      rewrite fs_H_loop_done in RES by reflexivity. subst hfin.
      enter_with (K m2 hc2 nd2 rr2 tv2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fh_fm fh_ec fh_bh fh_slo fh_shi fh_H];
        [st_eq| hmem_i AR1_2 AR2_3 FTB2 SC2 SHI2 SLO2 MI2| exact MU| exact WM| exact FMR2| exact FMOK2| rewrite Hec2; exact ECOK1| exact BW2].
    - replace (nb <? fh_H h * 2)%Z with false in NXT by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in NXT.
      (* [comment removed for export] *)
      wstep; if_cases KN; zify_cond_z KN.
      + (* [comment removed for export] *)
        replace (fb_nnd sfin =? 0)%Z with false in NXT by (symmetry; apply Z.eqb_neq; lia).
        pose proof (fp_hs_S fm0 ec0 bh0 nb t Hd) as HS. fold h in HS. rewrite NXT in HS.
        specialize (IH (S t) hfin hc2 nd2 rr2 tv2 me m2). rewrite HS in IH. cbn [fh_fm fh_ec fh_bh fh_slo fh_shi fh_H fh_done] in IH.
        rewrite NXT in RES.
        eapply IH; [reflexivity| exact RES| exact FIN| | hmem_i AR1_2 AR2_3 FTB2 SC2 SHI2 SLO2 MI2| exact MU| exact WM| exact K].
        split; [exact FMR2| split; [exact FMOK2| split; [rewrite Hec2; exact ECOK1| split; [exact BW2| lia]]]].
      + (* [comment removed for export] *)
        replace (fb_nnd sfin =? 0)%Z with true in NXT by (symmetry; apply Z.eqb_eq; lia).
        rewrite NXT in RES. rewrite fs_H_loop_done in RES by reflexivity. subst hfin.
        wstep.
        enter_with (K m2 hc2 nd2 rr2 tv2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fh_fm fh_ec fh_bh fh_slo fh_shi fh_H];
          [st_eq| hmem_i AR1_2 AR2_3 FTB2 SC2 SHI2 SLO2 MI2| exact MU| exact WM| exact FMR2| exact FMOK2| rewrite Hec2; exact ECOK1| exact BW2].
  Qed.
End S0FS.

End ACeilS1.
