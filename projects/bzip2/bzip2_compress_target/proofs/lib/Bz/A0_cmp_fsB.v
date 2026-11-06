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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WE := [(A2, A2 + ARR2_SIZE)]%Z.

  Lemma A0_fs_eclass : forall (r : nat) (i j Hh : Z) (fm ec bh : zarr) (me m : word -> option byte)
      (ra t1 t2 a1 a6 a7 s2 s7 s9 s11 t3 t4 t5 t6 : word),
    (i + Z.of_nat r = nb)%Z -> (0 <= i)%Z -> (1 <= r)%nat -> (0 <= j < nb)%Z -> (1 <= Hh <= nb)%Z ->
    zbok fm -> zbok ec -> bh_w32 bh -> (forall x, 0 <= x < nb -> 0 <= rd32 fm x < nb)%Z ->
    u8arr a0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m A2 (zb8 ec ARR2_SIZE) -> u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m ->
    munch WE me m -> wmono a0segs me m ->
    shzW a0segs WE me A1 (A1 + ARR1_SIZE) -> shzW a0segs WE me A2 (A2 + ARR2_SIZE) -> shzW a0segs WE me FT (FT + 262144) ->
    (forall m' (x10 x11 x12 x13 x14 x15 x16 : word), let ec' := fs_eclass r ec fm bh Hh nb i j in
      u8arr a0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 ec' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 bh 65537) -> mem_inv a0segs m' ->
      munch WE me m' -> wmono a0segs me m' -> zbok ec' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 a7
                            s2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 (Z_to_bv 64 FT) s9 (Z_to_bv 64 Hh) s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b154) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A1 + 4 * i)) a1 (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * i)) a6 a7
                          s2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 (Z_to_bv 64 FT) s9 (Z_to_bv 64 Hh) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9b070) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]. { intros; lia. }
    intros i j Hh fm ec bh me m ra t1 t2 a1 a6 a7 s2 s7 s9 s11 t3 t4 t5 t6 Hi Hi0 Hr Hj HH FMOK' ECOK' BW FMR AR1 AR2 FTB MI MU WM SH1 SH2 SHF K.
    fsenv_open XOK. afenv_open YOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    assert (Hw : (0 <= i / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    pose proof (FMR i ltac:(lia)) as Fv.
    (* [comment removed for export] *)
    arun.
    pose proof (zw32_read a0segs m FT bh 65537 (i / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. pose proof (BW (i / 32)%Z) as Bw.
    (* [comment removed for export] *)
    wstep. wstep. rewrite (isset_test_val (zget bh (i / 32)) i) by lia.
    rewrite fs_eclass_S in K. rewrite (isset_bh_testbit bh i) in K by lia.
    (* [comment removed for export] *)
    assert (TAIL : forall j', (0 <= j' < nb)%Z -> j' = (if Z.testbit (zget bh (i / 32)) (i mod 32) then i else j) ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 (A1 + 4 * i))
                            (Z_to_bv 64 (Z.b2z (Z.testbit (zget bh (i / 32)) (i mod 32)))) (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 j') (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 0) a7
                            s2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 (Z_to_bv 64 FT) s9 (Z_to_bv 64 Hh) s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b0a0) fc None m (seg_rom a0segs))).
    { intros j' Hj' Ej'. rewrite <- Ej' in K.
      (* [comment removed for export] *)
      arun.
      pose proof (zb8_read4 a0segs m A1 fm ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) FMOK' ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      rewrite (sign_sel (rd32 fm i - Hh) nb) by lia.
      set (sel := (if (rd32 fm i - Hh <? 0)%Z then nb else 0%Z)).
      assert (SEL : ((rd32 fm i - Hh < 0)%Z /\ sel = nb) \/ ((0 <= rd32 fm i - Hh)%Z /\ sel = 0%Z)) by (subst sel; destruct (Z.ltb_spec (rd32 fm i - Hh) 0); lia).
      assert (Esel : (sel + (rd32 fm i - Hh))%Z = (if (rd32 fm i - Hh <? 0)%Z then (rd32 fm i - Hh + nb)%Z else (rd32 fm i - Hh)%Z)) by (subst sel; destruct (Z.ltb_spec (rd32 fm i - Hh) 0); lia).
      clearbody sel.
      (* [comment removed for export] *)
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u8arr_storeN_ok a0segs mm A2 _ (4 * (sel + (rd32 fm i - Hh))) 4 _ AR2 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end.
      wstep. zb8_store4 AR2 (sel + (rd32 fm i - Hh))%Z. rewrite (unsigned_lit j') in AR2 by lia. rewrite Esel in AR2.
      (* [comment removed for export] *)
      arun. if_cases Ke; zify_cond_z Ke.
      - enter_with (IH (i + 1)%Z j' Hh fm _ bh me); [st_eq| lia| lia| lia| lia| lia| exact FMOK'| | exact BW| exact FMR| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM| exact SH1| exact SH2| exact SHF| ].
        + apply zbok_wr32. exact ECOK'.
        + intros m' x10 x11 x12 x13 x14 x15 x16. exact (K m' x10 x11 x12 x13 x14 x15 x16).
      - assert (r = 0)%nat by lia. subst r. cbn [fs_eclass] in K.
        wstep.
        enter_with (K _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM| apply zbok_wr32; exact ECOK']. }
    (* [comment removed for export] *)
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      destruct (Z.testbit (zget bh (i / 32)) (i mod 32)) eqn:Eb; [cbn in Kb; lia|].
      apply (TAIL j); [lia| reflexivity].
    - destruct (Z.testbit (zget bh (i / 32)) (i mod 32)) eqn:Eb; [|cbn in Kb; lia].
      (* [comment removed for export] *)
      wstep. apply (TAIL i); [lia| reflexivity].
  Qed.
End A0FS.

End ACeilS1.
