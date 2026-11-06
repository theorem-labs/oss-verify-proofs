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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msC.
Strategy 1000 [ms_ro_init ms_sh_shift ms_sh_pass ms_shell].

Ltac shell_pass X Y Q XOK YOK YSX h h3 roX ftX RKX MONO ROX FTB MIX SHR SHF SHP MUr me :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (A0_shell_iter X Y Q XOK YOK YSX _ _ _ _ _ _ _ h h3 roX ftX _ _ _ _ _ _ _ _ _ _ _ _ mm mm);
    [st_eq| lia| reflexivity| exact RKX| exact MONO| exact ROX| exact FTB| exact MIX| apply munch_refl| apply wmono_refl
    | eapply (shzW_sub a0segs _ _ me mm); [exact SHR| exact MUr| sub_fp_solve| lia| lia]
    | eapply (shzW_sub a0segs _ _ me mm); [exact SHF| exact MUr| sub_fp_solve| lia| lia]
    | eapply (shpW_sub a0segs _ _ me mm); [exact SHP| exact MUr| sub_fp_solve| lia| lia] |] end.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation RO := (am_RO Y).
  Notation WRO := [(RO, RO + 1024)]%Z.

  (* [comment removed for export] *)
  Lemma A0_bs_shell : forall (ft : zarr) (jro : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let ro5 := snd (ms_ro_init 256 znew znew 0) in let ro6 := ms_shell 8 ro5 ft 364 in
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    Z.of_nat (length jro) = 1024%Z ->
    u32arr a0segs m RO (ovw znew jro 256) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch WRO me m -> wmono a0segs me m ->
    frdW a0segs WRO me (P + 408) [C8 (Z_to_bv 64 A1)] ->
    shzW a0segs WRO me RO (RO + 1024) -> shzW a0segs WRO me FT (FT + 262144) -> shpW a0segs WRO me FT (FT + 262148) ->
    (forall m' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word), rook ro6 ->
      u32arr a0segs m' RO (zw32 ro6 256) -> u32arr a0segs m' FT (zw32 ft 65537) -> mem_inv a0segs m' ->
      munch WRO me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB x20 x21 x22 (Z_to_bv 64 FT) x24 x25 x26 (Z_to_bv 64 RO) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x986ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 x22 (Z_to_bv 64 FT) x24 x25 x26 (Z_to_bv 64 RO) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x984d4) fc None m (seg_rom a0segs)).
  Proof.
    intros ft jro x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 me m ro5 ro6 MONO Ljro ROB FTB MI MU WM V408 SHR SHF SHP K.
    msenv_open XOK. amenv_open YOK. pose proof (amsx_F_RO X Y YSX) as APFR. box_ors.
    pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    (* [comment removed for export] *)
    do 3 wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (A0_ro_init X Y Q XOK YOK _ _ _ _ _ _ _ 256%nat 0%Z znew znew jro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
      [st_eq| reflexivity| lia| intros; lia| exact Ljro| exact ROB| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1. cbv zeta. fold ro5. intros RO1 MI1 MU1 WM1 ROK.
    clear ROB MI. transport_after_call a0segs mq m1 MU1 WM1. clear MU1 WM1.
    rewrite (ovw_defined_zw32 ro5 jro 256) in RO1 by (intros i Hi; apply (proj1 (ROK i Hi))).
    assert (RK5 : rook ro5) by (intros k Hk; rewrite (proj2 (ROK k Hk)); lia).
    (* [comment removed for export] *)
    do 5 wstep.
    pose proof (V408 m1 MU) as RO_. wstep. clear RO_.
    (* [comment removed for export] *)
    shell_pass X Y Q XOK YOK YSX 364%Z 121%Z ro5 ft RK5 MONO RO1 FTB MI1 SHR SHF SHP MU me.
    intros m2 u7 u10 u11 u18 u28 u29 u30 u31. cbv zeta. intros RO2 FTB2 MI2 MU2 WM2 RK2.
    clear RO1 FTB MI1. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2. rename FTB2 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6a := ms_sh_pass (Z.to_nat (256 - 121)) ro5 ft 121 121) in *.
    shell_pass X Y Q XOK YOK YSX 121%Z 40%Z ro6a ft RK2 MONO RO2 FTB MI2 SHR SHF SHP MU me.
    intros m3 v7 v10 v11 v18 v28 v29 v30 v31. cbv zeta. intros RO3 FTB3 MI3 MU3 WM3 RK3.
    clear RO2 FTB MI2. transport_after_call a0segs m2 m3 MU3 WM3. clear MU3 WM3. rename FTB3 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6b := ms_sh_pass (Z.to_nat (256 - 40)) ro6a ft 40 40) in *.
    shell_pass X Y Q XOK YOK YSX 40%Z 13%Z ro6b ft RK3 MONO RO3 FTB MI3 SHR SHF SHP MU me.
    intros m4 w7 w10 w11 w18 w28 w29 w30 w31. cbv zeta. intros RO4 FTB4 MI4 MU4 WM4 RK4.
    clear RO3 FTB MI3. transport_after_call a0segs m3 m4 MU4 WM4. clear MU4 WM4. rename FTB4 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6c := ms_sh_pass (Z.to_nat (256 - 13)) ro6b ft 13 13) in *.
    shell_pass X Y Q XOK YOK YSX 13%Z 4%Z ro6c ft RK4 MONO RO4 FTB MI4 SHR SHF SHP MU me.
    intros m5 t7' t10' t11' t18' t28' t29' t30' t31'. cbv zeta. intros RO5 FTB5 MI5 MU5 WM5 RK5'.
    clear RO4 FTB MI4. transport_after_call a0segs m4 m5 MU5 WM5. clear MU5 WM5. rename FTB5 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6d := ms_sh_pass (Z.to_nat (256 - 4)) ro6c ft 4 4) in *.
    shell_pass X Y Q XOK YOK YSX 4%Z 1%Z ro6d ft RK5' MONO RO5 FTB MI5 SHR SHF SHP MU me.
    intros m6 s7' s10' s11' s18' s28' s29' s30' s31'. cbv zeta. intros RO6 FTB6 MI6 MU6 WM6 RK6.
    clear RO5 FTB MI5. transport_after_call a0segs m5 m6 MU6 WM6. clear MU6 WM6.
    wstep. wstep. wstep; if_false.
    assert (E6 : ro6 = ms_sh_pass (Z.to_nat (256 - 1)) ro6d ft 1 1).
    { cbv delta [ro6 ro6a ro6b ro6c ro6d].
      rewrite ms_shell_S. cbv zeta. change (364 / 3)%Z with 121%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (121 / 3)%Z with 40%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (40 / 3)%Z with 13%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (13 / 3)%Z with 4%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (4 / 3)%Z with 1%Z. cbn [Z.eqb Pos.eqb]. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| rewrite E6; exact RK6| rewrite E6; exact RO6| exact FTB6| exact MI6| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
