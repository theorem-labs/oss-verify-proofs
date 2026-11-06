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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCPermM BzCSewH CmpCutMS CmpMsKit CmpMsKit2.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msA B0_cmp_msB B0_cmp_msW B0_cmp_msX B0_cmp_msC BzCFactsBs.
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable sv : slv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation RO := (am_RO Y). Notation BD := (am_BD Y).
  Notation SL := (slb_cells X Y SHF SHn sv).
  Notation WRB := [(RO, RO + 1024); (BD, BD + 256)]%Z.
  (* [comment removed for export] *)
  Ltac sub_shz SH MU := eapply (shzW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac sub_shp SH MU := eapply (shpW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].

  Ltac shell_pass h h3 roX ftX RKX MONO ROX FTB SLB MIX SHR SHFz SHFp MU :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_shell_iter X Y SHF SHn sv Q XOK YOK YSX h h3 roX ftX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| reflexivity| exact RKX| exact MONO| exact ROX| exact FTB| exact SLB| exact MIX| apply munch_refl| apply wmono_refl
      | sub_shz SHR MU| sub_shz SHFz MU| sub_shp SHFp MU|].

  Lemma B0_bs_shell : forall (ft : zarr) (jro jbd : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let ro5 := snd (ms_ro_init 256 znew znew 0) in let ro6 := ms_shell 8 ro5 ft 364 in
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    Z.of_nat (length jro) = 1024%Z -> Z.of_nat (length jbd) = 256%Z ->
    u32arr b0segs m RO (ovw znew jro 256) -> u8arr b0segs m BD (ovb znew jbd 256) -> u32arr b0segs m FT (zw32 ft 65537) ->
    rw_cells b0segs m P SL -> mem_inv b0segs m ->
    munch WRB me m -> wmono b0segs me m ->
    shzW b0segs WRB me RO (RO + 1024) -> shzW b0segs WRB me FT (FT + 262144) -> shpW b0segs WRB me FT (FT + 262148) ->
    (forall m', rook ro6 ->
      u32arr b0segs m' RO (zw32 ro6 256) -> u8arr b0segs m' BD (zb8 bp_bd5 256) -> u32arr b0segs m' FT (zw32 ft 65537) ->
      rw_cells b0segs m' P SL -> mem_inv b0segs m' ->
      munch WRB me m' -> wmono b0segs me m' ->
      bmfree_at X Y Q 0xa2020 m') ->
    evt b0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa1cf8) fc None m (seg_rom b0segs)).
  Proof.
    intros ft jro jbd x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 me m
           ro5 ro6 MONO Ljro Ljbd ROB BDB FTB SLB MI MU WM SHR SHFz SHFp K.
    msenv_open XOK. amenv_open YOK. pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    pose proof (amsx_F_RO X Y YSX) as ASFr. pose proof (amsx_F_BD X Y YSX) as ASFb. box_ors.
    pose proof SLB as SLBo. open_slb_in SLBo.
    (* [comment removed for export] *)
    do 4 wstep. clear SLBo.
    enter_with (B0_ro_init X Y SHF SHn sv Q XOK YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 256%nat 0%Z znew znew jro jbd m m);
      [st_eq| reflexivity| lia| intros; lia| intros; lia| exact Ljro| exact Ljbd| exact ROB| exact BDB| exact SLB| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1. cbv zeta. fold ro5. intros RO1 BD1 SLB1 MI1 MU1 WM1 ROK BOK.
    clear ROB BDB SLB MI. transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
    rewrite (ovw_defined_zw32 ro5 jro 256) in RO1 by (intros i Hi; apply (proj1 (ROK i Hi))).
    rewrite (ovb_defined_zb8 _ jbd 256) in BD1 by (intros i Hi; apply (proj1 (BOK i Hi))).
    change (fst (ms_ro_init 256 znew znew 0)) with bp_bd5 in BD1.
    assert (RK5 : rook ro5) by (intros k Hk; rewrite (proj2 (ROK k Hk)); lia).
    (* [comment removed for export] *)
    pose proof SLB1 as SLBo. open_slb_in SLBo. brun_to 0xa1d38%Z. clear SLBo.
    (* [comment removed for export] *)
    shell_pass 364%Z 121%Z ro5 ft RK5 MONO RO1 FTB SLB1 MI1 SHR SHFz SHFp MU.
    intros m2 ura u6 u11 u12 u13 u16 u18 u19 u20 u21 u22 u23 u24 u25 u26 u30 u31. cbv zeta. intros RO2 FTB2 SLB2 MI2 MU2 WM2 RK2.
    clear RO1 FTB SLB1 MI1. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
    wstep. wstep. wstep. wstep; if_true.
    set (ro6a := ms_sh_pass (Z.to_nat (256 - 121)) ro5 ft 121 121) in *.
    shell_pass 121%Z 40%Z ro6a ft RK2 MONO RO2 FTB2 SLB2 MI2 SHR SHFz SHFp MU.
    intros m3 vra v6 v11 v12 v13 v16 v18 v19 v20 v21 v22 v23 v24 v25 v26 v30 v31. cbv zeta. intros RO3 FTB3 SLB3 MI3 MU3 WM3 RK3.
    clear RO2 FTB2 SLB2 MI2. transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
    wstep. wstep. wstep. wstep; if_true.
    set (ro6b := ms_sh_pass (Z.to_nat (256 - 40)) ro6a ft 40 40) in *.
    shell_pass 40%Z 13%Z ro6b ft RK3 MONO RO3 FTB3 SLB3 MI3 SHR SHFz SHFp MU.
    intros m4 wra w6 w11 w12 w13 w16 w18 w19 w20 w21 w22 w23 w24 w25 w26 w30 w31. cbv zeta. intros RO4 FTB4 SLB4 MI4 MU4 WM4 RK4.
    clear RO3 FTB3 SLB3 MI3. transport_after_call b0segs m3 m4 MU4 WM4. clear MU4 WM4.
    wstep. wstep. wstep. wstep; if_true.
    set (ro6c := ms_sh_pass (Z.to_nat (256 - 13)) ro6b ft 13 13) in *.
    shell_pass 13%Z 4%Z ro6c ft RK4 MONO RO4 FTB4 SLB4 MI4 SHR SHFz SHFp MU.
    intros m5 tra t6' t11' t12' t13' t16' t18' t19' t20' t21' t22' t23' t24' t25' t26' t30' t31'. cbv zeta. intros RO5 FTB5 SLB5 MI5 MU5 WM5 RK5'.
    clear RO4 FTB4 SLB4 MI4. transport_after_call b0segs m4 m5 MU5 WM5. clear MU5 WM5.
    wstep. wstep. wstep. wstep; if_true.
    set (ro6d := ms_sh_pass (Z.to_nat (256 - 4)) ro6c ft 4 4) in *.
    shell_pass 4%Z 1%Z ro6d ft RK5' MONO RO5 FTB5 SLB5 MI5 SHR SHFz SHFp MU.
    intros m6 sra s6' s11' s12' s13' s16' s18' s19' s20' s21' s22' s23' s24' s25' s26' s30' s31'. cbv zeta. intros RO6 FTB6 SLB6 MI6 MU6 WM6 RK6.
    clear RO5 FTB5 SLB5 MI5. transport_after_call b0segs m5 m6 MU6 WM6. clear MU6 WM6.
    wstep. wstep. wstep. wstep; if_false.
    assert (E6 : ro6 = ms_sh_pass (Z.to_nat (256 - 1)) ro6d ft 1 1).
    { cbv delta [ro6 ro6a ro6b ro6c ro6d].
      rewrite ms_shell_S. cbv zeta. change (364 / 3)%Z with 121%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (121 / 3)%Z with 40%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (40 / 3)%Z with 13%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (13 / 3)%Z with 4%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (4 / 3)%Z with 1%Z. cbn [Z.eqb Pos.eqb]. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (K mm ltac:(rewrite E6; exact RK6) ltac:(rewrite E6; exact RO6) BD1 FTB6 SLB6 MI6 MU WM) as KK end.
    unfold bmfree_at in KK. enter_with KK. st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
