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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msA A0_cmp_msB.
Strategy 1000 [ms_ftab_zero ms_radix1 ms_overshoot ms_accum ms_radix2].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation BD := (am_BD Y).
  Variable SH2 : Z. Hypothesis ASH2 : saddr A2 SH2.

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

  Definition WR : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z.

  Lemma A0_bs_radix : forall (q r : nat) (a1 a2 ft : zarr)
      (x1 x6 x7 x10 x11 x17 x21 x25 x26 x27 x29 x30 x31 : word) (me m : word -> option byte),
    let j0 := Z.shiftl (rd8 a2 0) 8 in
    let r1 := ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 in let a2r := fst (fst r1) in let ft1 := snd (fst r1) in
    let a2o := ms_overshoot 34 a2r qo n 0 in let ft3 := ms_accum 65536 ft1 1 in let s0 := Z.shiftl (rd8 a2o 0) 8 in
    let r4 := ms_radix2 (Z.to_nat n) a1 a2o ft3 (n - 1) s0 in let a1r := fst (fst r4) in let ft4 := snd (fst r4) in
    (Z.of_nat q = n / 4)%Z -> (Z.of_nat r = n mod 4)%Z ->
    zbok a1 -> zbok a2 -> (forall v, 0 <= v <= 65536 -> zget ft v = 0)%Z -> (forall v, 0 <= zget ft v < 4294967296)%Z ->
    (forall v, 0 <= v <= 65536 -> 0 <= zget ft3 v <= n)%Z -> r2ok n (Z.to_nat n) a1 a2o ft3 (n - 1) s0 ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr a0segs m FT (zw32 ft 65537) ->
    mem_inv a0segs m -> munch WR me m -> wmono a0segs me m ->
    frdW a0segs WR me (P + 248) [C8 (Z_to_bv 64 0)] -> frdW a0segs WR me (P + 280) [C8 (Z_to_bv 64 BD)] -> frdW a0segs WR me (P + 400) [C8 (Z_to_bv 64 n)] ->
    shzW a0segs WR me A1 (A1 + ARR1_SIZE) -> shzW a0segs WR me A2 (A2 + ARR2_SIZE) -> shzW a0segs WR me FT (FT + 262144) -> shpW a0segs WR me FT (FT + 262148) ->
    (forall m' (a2b ftb a1c ftc : zarr) (jb sc : Z) (y5 y6 y13 y14 y15 y16 y17 y24 : word),
      ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 = (a2b, ftb, jb) ->
      let a2o' := ms_overshoot 34 a2b qo n 0 in
      ms_radix2 (Z.to_nat n) a1 a2o' (ms_accum 65536 ftb 1) (n - 1) (Z.shiftl (rd8 a2o' 0) 8) = (a1c, ftc, sc) ->
      zbok a1c -> zbok a2o' -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftc v <= n)%Z -> (forall k, 0 <= k < n -> zget a2o' k = zget a2 k)%Z ->
      u8arr a0segs m' A1 (zb8 a1c ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2o' ARR2_SIZE) -> u32arr a0segs m' FT (zw32 ftc 65537) ->
      mem_inv a0segs m' -> munch WR me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp y5 y6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 BD) (Z_to_bv 64 0) (Z_to_bv 64 256) y13 y14 y15 y16 y17
                            (Z_to_bv 64 A2) cSB (Z_to_bv 64 (A2 + n)) x21 (Z_to_bv 64 SH2) (Z_to_bv 64 FT) y24 x25 x26 x27 (Z_to_bv 64 A1) x29 x30 x31)
                       F (Z_to_bv 64 0x984d0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp (Z_to_bv 64 (rd8 a2 0)) x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 (Z_to_bv 64 (n - 1 + 4)) (Z_to_bv 64 qo) (Z_to_bv 64 (A2 + (qo + 2 * (n - 1)))) (Z_to_bv 64 (qo + 2 * (n - 1))) (Z_to_bv 64 6) x17
                          (Z_to_bv 64 A2) cSB (Z_to_bv 64 n) x21 (Z_to_bv 64 SH2) (Z_to_bv 64 FT) (Z_to_bv 64 (n - 1)) x25 x26 x27 (Z_to_bv 64 A1) x29 x30 x31)
                     F (Z_to_bv 64 0x97d58) fc None m (seg_rom a0segs)).
  Proof.
    intros q r a1 a2 ft x1 x6 x7 x10 x11 x17 x21 x25 x26 x27 x29 x30 x31 me m.
    intros j0 r1 a2r ft1 a2o ft3 s0 r4 a1r ft4 Hq Hr A1OK A2OK FT0 FTNN FACC FR2 AR1 AR2 FTB MI MU WM V248 V280 V400 SH1r SH2r SHFr SHPr K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    unfold WR in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ft 65537 ltac:(lia)) as LFT.
    assert (Hn4 : (Z.to_nat n = 4 * q + r)%nat) by (Z.div_mod_to_equations; lia).
    pose proof (A2OK 0%Z) as B0. unfold rd8 in j0.
    assert (Hj0 : (0 <= j0 < 65536)%Z) by (subst j0; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8)%Z with 256%Z; lia).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    enter_with (A0_radix1x4 X Y Q XOK XSEP _ _ _ _ _ _ _ _ _ _ _ _ _ q (n - 1)%Z j0 a2 ft 0%Z _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| exact Hj0| exact A2OK| intros v Hv; rewrite (FT0 v Hv); lia| lia| lia| exact AR2| exact FTB| exact MI| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub a0segs _ _ me mq); [exact SH2r| exact MU| sub_fp_solve| lia| lia]
      | eapply (shzW_sub a0segs _ _ me mq); [exact SHFr| exact MU| sub_fp_solve| lia| lia] |].
    { unfold rd8. subst j0. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8)%Z with 256%Z. rewrite Z.div_mul by lia. reflexivity. }
    intros m1 y6 y10 y11. cbv zeta. intros AR2a FTBa MI1 MU1 WM1 OKa FTCa Ja LOWa. bz_params.
    clear AR2 FTB MI. transport_after_call a0segs mq m1 MU1 WM1. clear MU1 WM1.
    destruct (ms_radix1 (4 * q) a2 ft qo (n - 1) j0) as [[a2a fta] ja] eqn:Er4. cbn [fst snd] in *.
    pose proof (zb8_length a2a ARR2_SIZE ltac:(lia)) as L2a. pose proof (zw32_length fta 65537 ltac:(lia)) as LFa.
    (* [comment removed for export] *)
    assert (Er1 : r1 = ms_radix1 r a2a fta qo (n - 1 - 4 * Z.of_nat q)%Z ja).
    { subst r1. rewrite Hn4, ms_radix1_app, Er4. f_equal. lia. }
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    assert (REST : forall m2 (a2b ftb : zarr) (jb : Z) (z5 z6 z10 z11 z12 z14 z15 z16 z17 : word),
      r1 = (a2b, ftb, jb) -> zbok a2b -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftb v <= n)%Z -> (forall v, 0 <= zget ftb v < 4294967296 + n)%Z ->
      (forall k, 0 <= k < qo -> zget a2b k = zget a2 k)%Z ->
      u8arr a0segs m2 A2 (zb8 a2b ARR2_SIZE) -> u32arr a0segs m2 FT (zw32 ftb 65537) -> mem_inv a0segs m2 ->
      u8arr a0segs m2 A1 (zb8 a1 ARR1_SIZE) ->
      munch [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m2 -> wmono a0segs me m2 ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp z5 z6 x7 (me_sp X) (Z_to_bv 64 P)
                            z10 z11 z12 (Z_to_bv 64 qo) z14 z15 z16 z17
                            (Z_to_bv 64 A2) cSB (Z_to_bv 64 n) x21 (Z_to_bv 64 SH2) (Z_to_bv 64 FT) (Z_to_bv 64 (n - 1)) x25 x26 x27 (Z_to_bv 64 A1) x29 x30 x31)
                       F (Z_to_bv 64 0x98050) fc None m2 (seg_rom a0segs))).
    2:{ wstep; if_cases Kr; zify_cond_z Kr.
        - (* [comment removed for export] *) assert (r = 0%nat) as -> by lia.
          cbn [ms_radix1] in Er1.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST mm a2a fta ja _ _ _ _ _ _ _ _ _) end;
            [st_eq| first [exact Er1| rewrite Er1; reflexivity]| exact OKa| intros v Hv; pose proof (FTCa v Hv); lia| | exact LOWa| exact AR2a| exact FTBa| exact MI1| exact AR1| exact MU| exact WM].
          intros v. pose proof (ms_radix1_ft_bound (4 * q) a2 ft qo (n - 1) j0 4294967295 ltac:(intros w; pose proof (FTNN w); lia) v) as B.
          rewrite Er4 in B. cbn [fst snd] in B. lia.
        - (* [comment removed for export] *)
          do 5 wstep.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq1 end.
          enter_with (A0_radix1x1 X Y Q XOK XSEP _ _ _ _ _ _ _ _ _ _ _ _ _ r (n - 1 - 4 * Z.of_nat q)%Z ja a2a fta (4 * Z.of_nat q)%Z _ _ _ _ mq1 mq1);
            [st_eq| lia| lia| exact Ja| exact OKa| intros v Hv; pose proof (FTCa v Hv); lia| lia| lia| exact AR2a| exact FTBa| exact MI1| apply munch_refl| apply wmono_refl
            | eapply (shzW_sub a0segs _ _ me mq1); [exact SH2r| exact MU| sub_fp_solve| lia| lia]
            | eapply (shzW_sub a0segs _ _ me mq1); [exact SHFr| exact MU| sub_fp_solve| lia| lia] |].
          intros m2 y5' y12' y17'. cbv zeta. intros AR2b FTBb MI2 MU2 WM2 OKb FTCb LOWb. bz_params.
          clear AR2a FTBa MI1. transport_after_call a0segs mq1 m2 MU2 WM2. clear MU2 WM2.
          destruct (ms_radix1 r a2a fta qo (n - 1 - 4 * Z.of_nat q) ja) as [[a2b ftb] jb] eqn:Er5. cbn [fst snd] in *.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST mm a2b ftb jb _ _ _ _ _ _ _ _ _) end;
            [st_eq| first [exact Er1| rewrite Er1; reflexivity| rewrite Er1, Er5; reflexivity]| exact OKb| intros v Hv; pose proof (FTCb v Hv); lia| | | exact AR2b| exact FTBb| exact MI2| exact AR1| exact MU| exact WM].
          + assert (Ba : forall w, (0 <= zget fta w <= 4294967295 + 4 * Z.of_nat q)%Z).
            { intros w. pose proof (ms_radix1_ft_bound (4 * q) a2 ft qo (n - 1) j0 4294967295 ltac:(intros u; pose proof (FTNN u); lia) w) as C. rewrite Er4 in C. cbn [fst snd] in C. lia. }
            intros v. pose proof (ms_radix1_ft_bound r a2a fta qo (n - 1 - 4 * Z.of_nat q) ja (4294967295 + 4 * Z.of_nat q) Ba v) as B.
            rewrite Er5 in B. cbn [fst snd] in B. lia.
          + intros k Hk. rewrite (LOWb k Hk). apply LOWa. exact Hk. }
    intros m2 a2b ftb jb z5 z6 z10 z11 z12 z14 z15 z16 z17 Er1b OKb FTCb FTNb LOWb AR2b FTBb MI2 AR1b MUb WMb.
    clear AR1 MU WM. try clear AR2a FTBa MI1.
    assert (Er : ms_radix1 (Z.to_nat n) a2 ft qo (n - 1) j0 = (a2b, ftb, jb)) by (rewrite <- Er1b; reflexivity).
    unfold s0 in FR2. unfold ft3, ft1, a2o, a2r in FACC, FR2. fold r1 in Er. rewrite Er1b in FACC, FR2. cbn [fst snd] in FACC, FR2.
    set (a2o' := ms_overshoot 34 a2b qo n 0) in *. set (ft3' := ms_accum 65536 ftb 1) in *.
    pose proof (zb8_length a2b ARR2_SIZE ltac:(lia)) as L2b. pose proof (zw32_length ftb 65537 ltac:(lia)) as LFb.
    (* [comment removed for export] *)
    do 7 wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq2 end.
    enter_with (A0_overshoot X Y Q XOK XSEP _ _ _ _ _ _ _ _ _ _ _ _ 34%nat 0%Z a2b _ _ _ _ _ _ mq2 mq2);
      [st_eq| reflexivity| lia| exact OKb| exact AR2b| exact MI2| | apply wmono_refl
      | eapply (shzW_sub a0segs _ _ me mq2); [exact SH2r| exact MUb| sub_fp_solve| lia| lia] |].
    { apply munch_refl. }
    intros m3 w11 w12 w16. cbv zeta. fold a2o'. intros AR2c MI3 MU3 WM3 OKc. bz_params.
    clear AR2b MI2. transport_after_call a0segs mq2 m3 MU3 WM3. clear MU3 WM3.
    pose proof (zb8_length a2o' ARR2_SIZE ltac:(lia)) as L2o.
    pose proof (FTCb 0%Z ltac:(lia)) as F0b.
    (* [comment removed for export] *)
    wstep.
    lazymatch goal with MUc : munch _ me ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V248 mm MUc) as RO end. wstep. clear RO.
    arun. rd32_at FTBb 0%Z. arun_to 0x98120%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq3 end.
    enter_with (A0_accum X Y Q XOK XSEP _ _ _ _ _ _ _ _ _ _ _ _ _ 65536%nat 1%Z ftb _ _ _ _ _ _ _ mq3 mq3);
      [st_eq| vm_compute; reflexivity| lia| exact FACC| intros v; pose proof (FTNb v); lia| exact FTBb| exact MI3| apply munch_refl| apply wmono_refl
      | eapply (shpW_sub a0segs _ _ me mq3); [exact SHPr| exact MUb| sub_fp_solve| lia| lia] |].
    intros m4 w11' w14 w15. cbv zeta. fold ft3'. intros FTBd MI4 MU4 WM4 NNd.
    clear FTBb MI3. transport_after_call a0segs mq3 m4 MU4 WM4. clear MU4 WM4.
    pose proof (zw32_length ft3' 65537 ltac:(lia)) as LF3.
    (* [comment removed for export] *)
    arun. rdblk AR2c OKc 0%Z. wstep.
    lazymatch goal with MUc : munch _ me ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V400 mm MUc) as RO end. wstep. clear RO.
    do 3 wstep.
    set (s0' := Z.shiftl (zget a2o' 0) 8).
    assert (Hs0 : (0 <= s0' < 65536)%Z) by (subst s0'; rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8)%Z with 256%Z; lia).
    unfold rd8 in FR2. fold s0' in FR2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq4 end.
    enter_with (A0_radix2x4 X Y Q XOK XSEP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q (n - 1)%Z s0' a1 ft3' a2o' _ _ _ mq4 mq4);
      [st_eq| lia| lia| lia| exact Hs0| exact OKc| exact FACC| replace (Z.to_nat (n - 1 + 1)) with (Z.to_nat n) by lia; exact FR2
      | exact AR1b| exact AR2c| exact FTBd| exact MI4| apply munch_refl| apply wmono_refl
      | eapply (shzW_sub a0segs _ _ me mq4); [exact SH1r| exact MUb| sub_fp_solve| lia| lia]
      | eapply (shzW_sub a0segs _ _ me mq4); [exact SH2r| exact MUb| sub_fp_solve| lia| lia]
      | eapply (shzW_sub a0segs _ _ me mq4); [exact SHFr| exact MUb| sub_fp_solve| lia| lia] |].
    { subst s0'. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8)%Z with 256%Z. lia. }
    intros m5 w10 w13 w15'. cbv zeta. intros AR1e AR2e FTBe MI5 MU5 WM5 FTCe Se R2e. bz_params.
    clear AR1b AR2c FTBd MI4. transport_after_call a0segs mq4 m5 MU5 WM5. clear MU5 WM5.
    destruct (ms_radix2 (4 * q) a1 a2o' ft3' (n - 1) s0') as [[a1e fte] se] eqn:Eq4. cbn [fst snd] in *.
    pose proof (zb8_length a1e ARR1_SIZE ltac:(lia)) as L1e. pose proof (zw32_length fte 65537 ltac:(lia)) as LFe.
    (* [comment removed for export] *)
    wstep.
    (* [comment removed for export] *)
    assert (REST2 : forall m6 (a1c ftc : zarr) (sc : Z) (u10 u11 u12 u13 u14 u15 u24 : word),
      ms_radix2 (Z.to_nat n) a1 a2o' ft3' (n - 1) s0' = (a1c, ftc, sc) -> (forall v, 0 <= v <= 65536 -> 0 <= zget ftc v <= n)%Z ->
      u8arr a0segs m6 A1 (zb8 a1c ARR1_SIZE) -> u8arr a0segs m6 A2 (zb8 a2o' ARR2_SIZE) -> u32arr a0segs m6 FT (zw32 ftc 65537) -> mem_inv a0segs m6 ->
      munch [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148)]%Z me m6 -> wmono a0segs me m6 ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp z5 z6 x7 (me_sp X) (Z_to_bv 64 P)
                            u10 u11 u12 u13 u14 u15 w16 z17
                            (Z_to_bv 64 A2) cSB (Z_to_bv 64 (A2 + n)) x21 (Z_to_bv 64 SH2) (Z_to_bv 64 FT) u24 x25 x26 x27 (Z_to_bv 64 A1) x29 x30 x31)
                       F (Z_to_bv 64 0x984c4) fc None m6 (seg_rom a0segs))).
    { intros m6 a1c ftc sc u10 u11 u12 u13 u14 u15 u24 Eqn FTCc AR1c AR2f FTBc MI6 MU6 WM6.
      clear AR1e AR2e FTBe MI5 MUb WMb.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V280 mm MU6) as RO end. wstep. clear RO.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm a2b ftb a1c ftc jb sc _ _ _ _ _ _ _ _) end;
        [st_eq| exact Er| fold a2o'; fold s0'; fold ft3'; exact Eqn| | exact OKc| exact FTCc| | exact AR1c| exact AR2f| exact FTBc| exact MI6| exact MU6| exact WM6].
      - pose proof (zbok_radix2 (Z.to_nat n) a1 a2o' ft3' (n - 1) s0' A1OK) as Z1. rewrite Eqn in Z1. exact Z1.
      - intros k Hk. subst a2o'. pose proof (ms_overshoot_low n qo ltac:(lia) 34 a2b 0 ltac:(lia) ltac:(cbn; lia) k Hk) as OL. unfold rd8 in OL. rewrite OL.
        pose proof (ms_radix1_low (Z.to_nat n) a2 ft qo (n - 1) j0 k ltac:(lia) ltac:(lia)) as LW. fold r1 in LW. rewrite Er1b in LW. cbn [fst] in LW. exact LW. }
    wstep; if_cases Kr2; zify_cond_z Kr2.
    - (* [comment removed for export] *) assert (r = 0%nat) as -> by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST2 mm a1e fte se _ _ _ _ _ _ _) end;
        [st_eq| rewrite Hn4, Nat.add_0_r; exact Eq4| exact FTCe| exact AR1e| exact AR2e| exact FTBe| exact MI5| exact MUb| exact WMb].
    - (* [comment removed for export] *)
      do 5 wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq5 end.
      enter_with (A0_radix2x1 X Y Q XOK XSEP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (n - 1 - 4 * Z.of_nat q)%Z se a1e fte a2o' _ _ mq5 mq5);
        [st_eq| lia| lia| exact Se| exact OKc| exact FTCe| replace r with (Z.to_nat (n - 1 + 1) - 4 * q)%nat by lia; exact R2e
        | exact AR1e| exact AR2e| exact FTBe| exact MI5| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub a0segs _ _ me mq5); [exact SH1r| exact MUb| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs _ _ me mq5); [exact SH2r| exact MUb| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs _ _ me mq5); [exact SHFr| exact MUb| sub_fp_solve| lia| lia] |].
      intros m6 v11 v14 v15. cbv zeta. intros AR1f AR2g FTBf MI6 MU6 WM6 FTCf. bz_params.
      clear AR1e AR2e FTBe MI5. transport_after_call a0segs mq5 m6 MU6 WM6. clear MU6 WM6.
      destruct (ms_radix2 r a1e a2o' fte (n - 1 - 4 * Z.of_nat q) se) as [[a1f ftf] sf] eqn:Eq5. cbn [fst snd] in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST2 mm a1f ftf sf _ _ _ _ _ _ _) end;
        [st_eq| | exact FTCf| exact AR1f| exact AR2g| exact FTBf| exact MI6| exact MUb| exact WMb].
      rewrite Hn4, ms_radix2_app, Eq4. replace (n - 1 - Z.of_nat (4 * q))%Z with (n - 1 - 4 * Z.of_nat q)%Z by lia. exact Eq5.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
