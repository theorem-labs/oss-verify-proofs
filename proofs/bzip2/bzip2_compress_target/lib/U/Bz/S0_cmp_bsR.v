(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 DecTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0 BzCPermM BzCSewH.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV S0_cmp_msA S0_cmp_msB.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzSepTac.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation NQ := (18446744073709551615 - (A2 + qo))%Z.
  Notation FRV m := (rw_cells s0segs m (p + 56) [C8 (Z_to_bv 64 0)]).
  Notation FRA m := (rw_cells s0segs m (p + 224) [C8 (Z_to_bv 64 (18446744073709551615 - A2))]).
  Notation FRF m := (rw_cells s0segs m (p + 304) [C8 (Z_to_bv 64 FT); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 (18446744073709551615 - FT))]).

  Let S0_radix1x4 := S0_cmp_msA.S0_radix1x4 X Q XOK XSEP.
  Let S0_radix1x1 := S0_cmp_msA.S0_radix1x1 X Q XOK XSEP.
  Let S0_overshoot := S0_cmp_msA.S0_overshoot X Q XOK XSEP.
  Let S0_accum := S0_cmp_msA.S0_accum X Q XOK XSEP.

  Let S0_radix2x4 := S0_cmp_msB.S0_radix2x4 X Q XOK XSEP.
  Let S0_radix2x1 := S0_cmp_msB.S0_radix2x1 X Q XOK XSEP.

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.

  Definition WR : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z.

  (* [comment removed for export] *)
  Lemma S0_bs_radix : forall (q r : nat) (a1 a2 ft : zarr)
      (x0 x4 x5 x6 x7 x8 x12 x13 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let j0 := Z.shiftl (rd8 a2 0) 8 in
    let r1 := ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 in let a2r := fst (fst r1) in let ft1 := snd (fst r1) in
    let a2o := ms_overshoot 34 a2r qo n 0 in let ft3 := ms_accum 65536 ft1 1 in let s0 := Z.shiftl (rd8 a2o 0) 8 in
    let r4 := ms_radix2 (Z.to_nat n) a1 a2o ft3 (n - 1) s0 in let a1r := fst (fst r4) in let ft4 := snd (fst r4) in
    (Z.of_nat q = n / 4)%Z -> (Z.of_nat r = n mod 4)%Z ->
    zbok a1 -> zbok a2 -> (forall v, 0 <= v <= 65536 -> zget ft v = 0)%Z -> (forall v, 0 <= zget ft v < 4294967296)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft3 v <= n)%Z -> r2ok n (Z.to_nat n) a1 a2o ft3 (n - 1) s0 ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    FRV m -> FRA m -> FRF m -> mem_inv s0segs m -> munch WR me m -> wmono s0segs me m ->
    (forall m' (a2b ftb a1c ftc : zarr) (jb sc : Z) (y4 y9 y10 y11 y12 y13 y14 y15 y16 : word),
      ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 = (a2b, ftb, jb) ->
      let a2o' := ms_overshoot 34 a2b qo n 0 in
      ms_radix2 (Z.to_nat n) a1 a2o' (ms_accum 65536 ftb 1) (n - 1) (Z.shiftl (rd8 a2o' 0) 8) = (a1c, ftc, sc) ->
      zbok a1c -> zbok a2o' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftc v <= n)%Z -> (forall k, 0 <= k < n -> zget a2o' k = zget a2 k)%Z ->
      u8arr s0segs m' A1 (zb8 a1c ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2o' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ftc 65537) ->
      FRV m' -> FRA m' -> FRF m' -> mem_inv s0segs m' -> munch WR me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp y4 x5 x6 x7 x8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x20b04) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 NQ) (Z_to_bv 64 n) (Z_to_bv 64 6) x12 x13 (Z_to_bv 64 (rd8 a2 0)) x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20560) fc None m (seg_rom s0segs)).
  Proof.
    intros q r a1 a2 ft x0 x4 x5 x6 x7 x8 x12 x13 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m.
    intros j0 r1 a2r ft1 a2o ft3 s0 r4 a1r ft4 Hq Hr A1OK A2OK FT0 FTNN FACC FR2 AR1 AR2 FTB FV FA FF MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WR in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    assert (Hn4 : (Z.to_nat n = 4 * q + r)%nat) by (Z.div_mod_to_equations; lia).
    pose proof (A2OK 0%Z) as B0. unfold rd8 in j0.
    assert (Hj0 : (0 <= j0 < 65536)%Z) by (subst j0; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8)%Z with 256%Z; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (S0_radix1x4 q (n - 1)%Z j0 a2 ft 0%Z);
      [st_eq| lia| lia| lia| exact Hj0| exact A2OK| intros v Hv; rewrite (FT0 v Hv); lia| lia| lia| exact AR2| exact FTB| exact MI| exact FV| exact FA| exact FF| apply munch_refl| apply wmono_refl|].
    { subst j0. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8)%Z with 256%Z. rewrite Z.div_mul by lia. reflexivity. }
    intros m1 y4 y15 y16. cbv zeta. intros AR2a FTBa MI1 FVa FAa FFa MU1 WM1 OKa FTCa Ja LOWa. bz_params.
    clear AR2 FTB MI FVa FAa FFa. transport_after_call s0segs mq m1 MU1 WM1. clear MU1 WM1.
    destruct (ms_radix1 (4 * q) a2 ft qo (n - 1) j0) as [[a2a fta] ja] eqn:Er4. cbn [fst snd] in *.
    pose proof (zb8_length a2a ARR2_SIZE ltac:(lia)) as L2a. pose proof (zw32_length fta 65537 ltac:(lia)) as LFa.
    (* [comment removed for export] *)
    assert (Er1 : r1 = ms_radix1 r a2a fta qo (n - 1 - 4 * Z.of_nat q)%Z ja).
    { subst r1. rewrite Hn4, ms_radix1_app, Er4. f_equal. lia. }
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    assert (REST : forall m2 (a2b ftb : zarr) (jb : Z) (z4 z9 z10 z11 z12 z13 z14 z15 z16 : word),
      r1 = (a2b, ftb, jb) -> zbok a2b -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftb v <= n)%Z -> (forall v, 0 <= zget ftb v < 4294967296 + n)%Z ->
      (forall k, 0 <= k < qo -> zget a2b k = zget a2 k)%Z ->
      u8arr s0segs m2 A2 (zb8 a2b ARR2_SIZE) -> u32arr s0segs m2 FT (zw32 ftb 65537) -> mem_inv s0segs m2 ->
      u8arr s0segs m2 A1 (zb8 a1 ARR1_SIZE) -> FRV m2 -> FRA m2 -> FRF m2 ->
      munch [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m2 -> wmono s0segs me m2 ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp z4 x5 x6 x7 x8
                            z9 z10 z11 z12 z13 z14 z15 z16
                            (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x20750) fc None m2 (seg_rom s0segs))).
    2:{ wstep; if_cases Kr; zify_cond_z Kr.
        - (* [comment removed for export] *) assert (r = 0%nat) as -> by lia.
          cbn [ms_radix1] in Er1.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST mm a2a fta ja _ _ _ _ _ _ _ _ _) end;
            [st_eq| first [exact Er1| rewrite Er1; reflexivity]| exact OKa| intros v Hv; pose proof (FTCa v Hv); lia| | exact LOWa| exact AR2a| exact FTBa| exact MI1| exact AR1| exact FV| exact FA| exact FF| exact MU| exact WM].
          intros v. pose proof (ms_radix1_ft_bound (4 * q) a2 ft qo (n - 1) j0 4294967295 ltac:(intros w; pose proof (FTNN w); lia) v) as B.
          rewrite Er4 in B. cbn [fst snd] in B. lia.
        - (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq1 end.
          enter_with (S0_radix1x1 r (n - 1 - 4 * Z.of_nat q)%Z ja a2a fta (4 * Z.of_nat q)%Z);
            [st_eq| lia| lia| exact Ja| exact OKa| intros v Hv; pose proof (FTCa v Hv); lia| lia| lia| exact AR2a| exact FTBa| exact MI1| exact FV| exact FA| exact FF| apply munch_refl| apply wmono_refl|].
          intros m2 z11 z12 z13. cbv zeta. intros AR2b FTBb MI2 FVc FAc FFc MU2 WM2 OKb FTCb LOWb. bz_params.
          clear AR2a FTBa MI1 FVc FAc FFc. transport_after_call s0segs mq1 m2 MU2 WM2. clear MU2 WM2.
          destruct (ms_radix1 r a2a fta qo (n - 1 - 4 * Z.of_nat q) ja) as [[a2b ftb] jb] eqn:Er5. cbn [fst snd] in *.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST mm a2b ftb jb _ _ _ _ _ _ _ _ _) end;
            [st_eq| first [exact Er1| rewrite Er1; reflexivity| rewrite Er1, Er5; reflexivity]| exact OKb| intros v Hv; pose proof (FTCb v Hv); lia| | | exact AR2b| exact FTBb| exact MI2| exact AR1| exact FV| exact FA| exact FF| exact MU| exact WM].
          + assert (Ba : forall w, (0 <= zget fta w <= 4294967295 + 4 * Z.of_nat q)%Z).
            { intros w. pose proof (ms_radix1_ft_bound (4 * q) a2 ft qo (n - 1) j0 4294967295 ltac:(intros u; pose proof (FTNN u); lia) w) as C. rewrite Er4 in C. cbn [fst snd] in C. lia. }
            intros v. pose proof (ms_radix1_ft_bound r a2a fta qo (n - 1 - 4 * Z.of_nat q) ja (4294967295 + 4 * Z.of_nat q) Ba v) as B.
            rewrite Er5 in B. cbn [fst snd] in B. lia.
          + intros k Hk. rewrite (LOWb k Hk). apply LOWa. exact Hk. }
    intros m2 a2b ftb jb z4 z9 z10 z11 z12 z13 z14 z15 z16 Er1b OKb FTCb FTNb LOWb AR2b FTBb MI2 AR1b FVb FAb FFb MUb WMb.
    clear AR1 FV FA FF MU WM. try clear AR2a FTBa MI1.
    assert (Er : ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 = (a2b, ftb, jb)) by (rewrite <- Er1b; reflexivity).
    unfold s0 in FR2. unfold ft3, ft1, a2o, a2r in FACC, FR2. fold r1 in Er. rewrite Er1b in FACC, FR2. cbn [fst snd] in FACC, FR2.
    set (a2o' := ms_overshoot 34 a2b qo n 0) in *. set (ft3' := ms_accum 65536 ftb 1) in *.
    pose proof (zb8_length a2b ARR2_SIZE ltac:(lia)) as L2b. pose proof (zw32_length ftb 65537 ltac:(lia)) as LFb.
    (* [comment removed for export] *)
    do 4 wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq2 end.
    enter_with (S0_overshoot 34%nat 0%Z a2b);
      [st_eq| reflexivity| lia| exact OKb| exact AR2b| exact MI2| exact FVb| exact FAb| exact FFb| apply munch_refl| apply wmono_refl|].
    intros m3 w12 w13 w14 w15. cbv zeta. fold a2o'. intros AR2c MI3 FVd FAd FFd MU3 WM3 OKc. bz_params.
    clear AR2b MI2 FVd FAd FFd. transport_after_call s0segs mq2 m3 MU3 WM3. clear MU3 WM3.
    pose proof (zb8_length a2o' ARR2_SIZE ltac:(lia)) as L2o.
    pose proof (FTCb 0%Z ltac:(lia)) as F0b.
    (* [comment removed for export] *)
    assert (FTL : Z.land FT 3 = 0%Z) by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2)%Z with 4%Z; Z.div_mod_to_equations; lia).
    wstep. wstep. wstep; if_true. wstep. wstep. rewrite ?FTL. flags. wstep. nt. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq3 end.
    enter_with (S0_accum 65536%nat 1%Z ftb);
      [st_eq| vm_compute; reflexivity| lia| exact FACC| intros v; pose proof (FTNb v); lia| exact FTBb| exact MI3| exact FVb| exact FAb| exact FFb| apply munch_refl| apply wmono_refl|].
    intros m4 w11 w12' w13'. cbv zeta. fold ft3'. intros FTBd MI4 FVe FAe FFe MU4 WM4 NNd.
    clear FTBb MI3 FVe FAe FFe. transport_after_call s0segs mq3 m4 MU4 WM4. clear MU4 WM4.
    pose proof (zw32_length ft3' 65537 ltac:(lia)) as LF3.
    (* [comment removed for export] *)
    rdblk AR2c OKc 0%Z. wstep. flags. wstep. wstep. wstep.
    set (s0' := Z.shiftl (zget a2o' 0) 8).
    assert (Hs0 : (0 <= s0' < 65536)%Z) by (subst s0'; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8)%Z with 256%Z; lia).
    unfold rd8 in FR2. fold s0' in FR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq4 end.
    enter_with (S0_radix2x4 q (n - 1)%Z s0' a1b ft3' a2o') ||
    enter_with (S0_radix2x4 q (n - 1)%Z s0' a1 ft3' a2o');
      [st_eq| lia| lia| lia| exact Hs0| exact OKc| exact FACC| replace (Z.to_nat (n - 1 + 1)) with (Z.to_nat n) by lia; exact FR2
      | exact AR1b| exact AR2c| exact FTBd| exact MI4| exact FVb| exact FAb| exact FFb| apply munch_refl| apply wmono_refl|].
    { subst s0'. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8)%Z with 256%Z. lia. }
    intros m5 e4 e14 e15 e16. cbv zeta. intros AR1e AR2e FTBe MI5 FVf FAf FFf MU5 WM5 FTCe Se R2e. bz_params.
    clear AR1b AR2c FTBd MI4 FVf FAf FFf. transport_after_call s0segs mq4 m5 MU5 WM5. clear MU5 WM5.
    destruct (ms_radix2 (4 * q) a1 a2o' ft3' (n - 1) s0') as [[a1e fte] se] eqn:Eq4. cbn [fst snd] in *.
    pose proof (zb8_length a1e ARR1_SIZE ltac:(lia)) as L1e. pose proof (zw32_length fte 65537 ltac:(lia)) as LFe.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    assert (REST2 : forall m6 (a1c ftc : zarr) (sc : Z) (u4 u9 u10 u11 u12 u13 u14 u15 u16 : word),
      ms_radix2 (Z.to_nat n) a1 a2o' ft3' (n - 1) s0' = (a1c, ftc, sc) -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftc v <= n)%Z ->
      u8arr s0segs m6 A1 (zb8 a1c ARR1_SIZE) -> u8arr s0segs m6 A2 (zb8 a2o' ARR2_SIZE) -> u32arr s0segs m6 FT (zw32 ftc 65537) ->
      FRV m6 -> FRA m6 -> FRF m6 -> mem_inv s0segs m6 ->
      munch [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m6 -> wmono s0segs me m6 ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp u4 x5 x6 x7 x8
                            u9 u10 u11 u12 u13 u14 u15 u16
                            (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x20b04) fc None m6 (seg_rom s0segs))).
    { intros m6 a1c ftc sc u4 u9 u10 u11 u12 u13 u14 u15 u16 Eqn FTCc AR1c AR2f FTBc FV6 FA6 FF6 MI6 MU6 WM6.
      clear AR1e AR2e FTBe MI5 FVb FAb FFb MUb WMb.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm a2b ftb a1c ftc jb sc _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact Er| fold a2o'; fold s0'; fold ft3'; exact Eqn| | exact OKc| exact FTCc| | exact AR1c| exact AR2f| exact FTBc| exact FV6| exact FA6| exact FF6| exact MI6| exact MU6| exact WM6].
      - pose proof (zbok_radix2 (Z.to_nat n) a1 a2o' ft3' (n - 1) s0' A1OK) as Z1. rewrite Eqn in Z1. exact Z1.
      - intros k Hk. subst a2o'. pose proof (ms_overshoot_low n qo ltac:(lia) 34 a2b 0 ltac:(lia) ltac:(cbn; lia) k Hk) as OL. unfold rd8 in OL. rewrite OL.
        pose proof (ms_radix1_low (Z.to_nat n) a2 ft qo (n - 1) j0 k ltac:(lia) ltac:(lia)) as LW. fold r1 in LW. rewrite Er1b in LW. cbn [fst] in LW. exact LW. }
    wstep; if_cases Kr2; zify_cond_z Kr2.
    - (* [comment removed for export] *) assert (r = 0%nat) as -> by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST2 mm a1e fte se _ _ _ _ _ _ _ _ _) end;
        [st_eq| rewrite Hn4, Nat.add_0_r; exact Eq4| exact FTCe| exact AR1e| exact AR2e| exact FTBe| exact FVb| exact FAb| exact FFb| exact MI5| exact MUb| exact WMb].
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq5 end.
      enter_with (S0_radix2x1 r (n - 1 - 4 * Z.of_nat q)%Z se a1e fte a2o');
        [st_eq| lia| lia| exact Se| exact OKc| exact FTCe| replace r with (Z.to_nat (n - 1 + 1) - 4 * q)%nat by lia; exact R2e
        | exact AR1e| exact AR2e| exact FTBe| exact MI5| exact FVb| exact FAb| exact FFb| apply munch_refl| apply wmono_refl|].
      intros m6 v10 v11 v12 v13. cbv zeta. intros AR1f AR2g FTBf MI6 FVg FAg FFg MU6 WM6 FTCf. bz_params.
      clear AR1e AR2e FTBe MI5 FVg FAg FFg. transport_after_call s0segs mq5 m6 MU6 WM6. clear MU6 WM6.
      destruct (ms_radix2 r a1e a2o' fte (n - 1 - 4 * Z.of_nat q) se) as [[a1f ftf] sf] eqn:Eq5. cbn [fst snd] in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST2 mm a1f ftf sf _ _ _ _ _ _ _ _ _) end;
        [st_eq| | exact FTCf| exact AR1f| exact AR2g| exact FTBf| exact FVb| exact FAb| exact FFb| exact MI6| exact MUb| exact WMb].
      rewrite Hn4, ms_radix2_app, Eq4. replace (n - 1 - Z.of_nat (4 * q))%Z with (n - 1 - 4 * Z.of_nat q)%Z by lia. exact Eq5.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
