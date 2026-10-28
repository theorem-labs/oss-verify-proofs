(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 DecTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV S0_cmp_msC.
From Stdlib Require Lia. Unset Lia Cache.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.   (* [comment removed for export] *)
Strategy 1000 [ms_ro_init ms_sh_shift ms_sh_pass ms_shell].

Ltac shell_pass SI h h3 roX ftX RKX MONO ROX FTB MIX FVX FAX FFX :=
  enter_with (SI h h3 roX ftX);
    [st_eq| lia| reflexivity| exact RKX| exact MONO| exact ROX| exact FTB| exact MIX| exact FVX| exact FAX| exact FFX| apply munch_refl| apply wmono_refl|].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation NRO := (18446744073709551615 - (p + 2644))%Z.
  Notation FRV m := (rw_cells s0segs m (p + 56) [C8 (Z_to_bv 64 0)]).
  Notation FRA m := (rw_cells s0segs m (p + 224) [C8 (Z_to_bv 64 (18446744073709551615 - A2))]).
  Notation FRF m := (rw_cells s0segs m (p + 304) [C8 (Z_to_bv 64 FT); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 (18446744073709551615 - FT))]).

  Let S0_ro_init := S0_cmp_msC.S0_ro_init X Q XOK XSEP.
  Let S0_shell_iter := S0_cmp_msC.S0_shell_iter X Q XOK XSEP.

  (* [comment removed for export] *)
  Lemma S0_bs_shell : forall (ft : zarr) (jro jbd : list byte)
      (x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let ro5 := snd (ms_ro_init 256 znew znew 0) in let ro6 := ms_shell 8 ro5 ft 364 in
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    Z.of_nat (length jro) = 1024%Z -> Z.of_nat (length jbd) = 256%Z ->
    u32arr s0segs m (p + 2644) (ovw znew jro 256) -> rw_cells s0segs m (p + 2388) [CB (Z.to_nat 256) jbd] ->
    u32arr s0segs m FT (zw32 ft 65537) -> FRV m -> FRA m -> FRF m -> mem_inv s0segs m ->
    munch [(p + 2388, p + 3668)]%Z me m -> wmono s0segs me m ->
    (forall m' (y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word), rook ro6 ->
      u32arr s0segs m' (p + 2644) (zw32 ro6 256) -> u8arr s0segs m' (p + 2388) (zb8 znew 256) -> u32arr s0segs m' FT (zw32 ft 65537) ->
      FRV m' -> FRA m' -> FRF m' -> mem_inv s0segs m' ->
      munch [(p + 2388, p + 3668)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x20d24) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          x9 x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20b04) fc None m (seg_rom s0segs)).
  Proof.
    intros ft jro jbd x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m ro5 ro6 MONO Ljro Ljbd RO BD FTB FV FA FF MI MU WM K.
    msenv_open XOK. pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    do 7 wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (S0_ro_init jro jbd);
      [st_eq| exact Ljro| exact Ljbd| exact RO| exact BD| exact MI| exact FV| exact FA| exact FF| apply munch_refl| apply wmono_refl|].
    intros m1. cbv zeta. fold ro5. intros RO1 BD1 MI1 FV1 FA1 FF1 MU1 WM1 ROK.
    clear RO BD MI FV1 FA1 FF1. transport_after_call s0segs mq m1 MU1 WM1. clear MU1 WM1.
    rewrite (ovw_defined_zw32 ro5 jro 256) in RO1 by (intros i Hi; apply (proj1 (ROK i Hi))).
    assert (RK5 : rook ro5) by (intros k Hk; rewrite (proj2 (ROK k Hk)); lia).
    (* [comment removed for export] *)
    do 8 wstep.
    (* [comment removed for export] *)
    shell_pass S0_shell_iter 364%Z 121%Z ro5 ft RK5 MONO RO1 FTB MI1 FV FA FF.
    intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?. cbv zeta. intros RO2 FTB2 MI2 FV2 FA2 FF2 MU2 WM2 RK2.
    clear RO1 FTB MI1 FV2 FA2 FF2. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2. rename FTB2 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6a := ms_sh_pass (Z.to_nat (256 - 121)) ro5 ft 121 121) in *.
    shell_pass S0_shell_iter 121%Z 40%Z ro6a ft RK2 MONO RO2 FTB MI2 FV FA FF.
    intros m3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?. cbv zeta. intros RO3 FTB3 MI3 FV3 FA3 FF3 MU3 WM3 RK3.
    clear RO2 FTB MI2 FV3 FA3 FF3. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3. rename FTB3 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6b := ms_sh_pass (Z.to_nat (256 - 40)) ro6a ft 40 40) in *.
    shell_pass S0_shell_iter 40%Z 13%Z ro6b ft RK3 MONO RO3 FTB MI3 FV FA FF.
    intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?. cbv zeta. intros RO4 FTB4 MI4 FV4 FA4 FF4 MU4 WM4 RK4.
    clear RO3 FTB MI3 FV4 FA4 FF4. transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4. rename FTB4 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6c := ms_sh_pass (Z.to_nat (256 - 13)) ro6b ft 13 13) in *.
    shell_pass S0_shell_iter 13%Z 4%Z ro6c ft RK4 MONO RO4 FTB MI4 FV FA FF.
    intros m5 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?. cbv zeta. intros RO5 FTB5 MI5 FV5 FA5 FF5 MU5 WM5 RK5'.
    clear RO4 FTB MI4 FV5 FA5 FF5. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5. rename FTB5 into FTB.
    wstep. wstep. wstep; if_true.
    set (ro6d := ms_sh_pass (Z.to_nat (256 - 4)) ro6c ft 4 4) in *.
    shell_pass S0_shell_iter 4%Z 1%Z ro6d ft RK5' MONO RO5 FTB MI5 FV FA FF.
    intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?. cbv zeta. intros RO6 FTB6 MI6 FV6 FA6 FF6 MU6 WM6 RK6.
    clear RO5 FTB MI5 FV6 FA6 FF6. transport_after_call s0segs m5 m6 MU6 WM6. clear MU6 WM6.
    wstep. wstep. wstep; if_false.
    assert (E6 : ro6 = ms_sh_pass (Z.to_nat (256 - 1)) ro6d ft 1 1).
    { cbv delta [ro6 ro6a ro6b ro6c ro6d].
      rewrite ms_shell_S. cbv zeta. change (364 / 3)%Z with 121%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (121 / 3)%Z with 40%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (40 / 3)%Z with 13%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (13 / 3)%Z with 4%Z. cbn [Z.eqb Pos.eqb].
      rewrite ms_shell_S. cbv zeta. change (4 / 3)%Z with 1%Z. cbn [Z.eqb Pos.eqb]. reflexivity. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [st_eq| rewrite E6; exact RK6| rewrite E6; exact RO6| exact BD1| exact FTB6| exact FV| exact FA| exact FF| exact MI6| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
