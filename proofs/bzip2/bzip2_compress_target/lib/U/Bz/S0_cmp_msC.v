(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
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

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.


  Notation BF ft v := (zget ft ((v + 1) * 256) - zget ft (v * 256))%Z.

  Notation MONO ft := (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z.
  Notation RW ra a2 s6 s7 s8 s9 s10 s11 i h h3 vv j x17 x19 :=
    (mkR ra (Z_to_bv 64 p) gp tp (Z_to_bv 64 256) (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 0) (Z_to_bv 64 ((vv + 1) * 1024))
         (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 h) a2 (Z_to_bv 64 255) (Z_to_bv 64 NRO) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) (Z_to_bv 64 h3)
         x17 (Z_to_bv 64 (FT + (vv + 1) * 1024)) x19 (Z_to_bv 64 (FT + vv * 1024)) s6 s7 s8 s9 s10 s11
         (Z_to_bv 64 vv) (Z_to_bv 64 (vv + 1)) (Z_to_bv 64 j) (Z_to_bv 64 (vv * 1024))).
  Notation RWX ra a2 s8 s9 s10 s11 i h h3 vv j x17 x19 := (RW ra a2 (Z_to_bv 64 j) (Z_to_bv 64 (4 * j)) s8 s9 s10 s11 i h h3 vv j x17 x19).

  Lemma U0_sh_while : forall (i h h3 vv : Z) (ft : zarr) (x17 x19 : word) (f : nat) (j : Z) (ro : zarr)
      (ra a2 s6 s7 s8 s9 s10 s11 : word) (me m : word -> option byte),
    (4 <= h <= 364)%Z -> (1 <= h3 <= 121)%Z -> (h3 <= j <= i)%Z -> (i < 256)%Z -> (j + 1 <= h3 * Z.of_nat f)%Z -> rook ro -> (0 <= vv < 256)%Z ->
    MONO ft ->
    u32arr s0segs m (p + 2644) (zw32 ro 256) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    FRV m -> FRA m -> FRF m ->
    munch [(p + 2644, p + 3668)]%Z me m -> wmono s0segs me m ->
    (forall m' (ra' a2' s8' s9' s10' s11' : word), let rr := ms_sh_shift f ro ft h3 j vv in
      u32arr s0segs m' (p + 2644) (zw32 (fst rr) 256) -> u32arr s0segs m' FT (zw32 ft 65537) -> mem_inv s0segs m' ->
      FRV m' -> FRA m' -> FRF m' ->
      munch [(p + 2644, p + 3668)]%Z me m' -> wmono s0segs me m' -> rook (fst rr) -> (0 <= snd rr <= j)%Z ->
      evt s0segs Q (MS (RWX ra' a2' s8' s9' s10' s11' i h h3 vv (snd rr) x17 x19) F (Z_to_bv 64 0x20cf8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW ra a2 s6 s7 s8 s9 s10 s11 i h h3 vv j x17 x19) F (Z_to_bv 64 0x20bdc) fc None m (seg_rom s0segs)).
  Proof using XOK XSEP.
    intros i h h3 vv ft x17 x19. induction f as [|f IH]; [intros; lia|].
    intros j ro ra a2 s6 s7 s8 s9 s10 s11 me m Hh Hh3 Hj Hi Hf ROK Hvv MONOf RO FTB MI FV FA FF MU WM K.
    msenv_open XOK.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK (j - h3)%Z ltac:(lia)) as Rjh. set (u := zget ro (j - h3)) in Rjh.
    pose proof (MONOf vv ltac:(lia)) as Mv. pose proof (MONOf u ltac:(lia)) as Mu.
    urun.
    rd32_at RO (j - h3)%Z. fold u. try rewrite (zx32_of_Z u) by lia.
    urun.
    rd32_at FTB ((u + 1) * 256)%Z. rd32_at FTB (u * 256)%Z. rd32_at FTB ((vv + 1) * 256)%Z. rd32_at FTB (vv * 256)%Z.
    urun.
    rewrite ms_sh_shift_S in K. unfold bigfreq in K. rewrite !Z.shiftl_mul_pow2 in K by lia. change (2 ^ 8)%Z with 256%Z in K. fold u in K.
    if_cases Kc; zify_cond_z Kc.
    - replace (_ <? _) with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      urun_to 0x20cf8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _) end;
        [st_eq| exact RO| exact FTB| assumption| assumption| assumption| assumption| assumption| assumption| exact ROK| lia].
    - replace (_ <? _) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv zeta in K.
      urun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 2644) _ j _ RO ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store RO j u (rewrite unsigned_lit by lia; reflexivity).
      set (ro1 := zset ro j u) in RO, K.
      assert (ROK1 : rook ro1) by (intros k Hk; subst ro1; rewrite zget_zset; destruct (k =? j); [exact Rjh| apply ROK; lia]).
      urun.
      if_cases Kd; zify_cond_z Kd.
      + replace (j - h3 <=? h3 - 1) with false in K by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h3)%Z ro1 _ _ _ _ _ _ _ _ me); [st_eq| lia| lia| lia| lia| lia| exact ROK1| lia| exact MONOf| exact RO| exact FTB| assumption| assumption| assumption| assumption| assumption| assumption|].
        intros m' ra' a2' s8' s9' s10' s11'. cbv zeta. intros RO' FTB' MI' FV' FA' FF' MU' WM' ROK' J'.
        enter_with (K m' ra' a2' s8' s9' s10' s11'); [st_eq| exact RO'| exact FTB'| exact MI'| exact FV'| exact FA'| exact FF'| exact MU'| exact WM'| exact ROK'| lia].
      + replace (j - h3 <=? h3 - 1) with true in K by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _) end;
          [st_eq| exact RO| exact FTB| assumption| assumption| assumption| assumption| assumption| assumption| exact ROK1| lia].
        all: lia.
  Qed.

  Lemma U0_sh_pass : forall (h h3 : Z) (ft : zarr) (x17 x19 : word) (r : nat) (i : Z) (ro : zarr)
      (x0 x6 x7 x8 x11 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 : word) (me m : word -> option byte),
    (4 <= h <= 364)%Z -> (1 <= h3 <= 121)%Z -> (h3 <= i < 256)%Z -> (Z.of_nat r = 256 - i)%Z -> rook ro -> MONO ft ->
    u32arr s0segs m (p + 2644) (zw32 ro 256) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    FRV m -> FRA m -> FRF m ->
    munch [(p + 2644, p + 3668)]%Z me m -> wmono s0segs me m ->
    (forall m' (y0 y4 y5 y6 y7 y8 y11 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      let ro' := ms_sh_pass r ro ft h3 i in
      u32arr s0segs m' (p + 2644) (zw32 ro' 256) -> u32arr s0segs m' FT (zw32 ft 65537) -> mem_inv s0segs m' ->
      FRV m' -> FRA m' -> FRF m' ->
      munch [(p + 2644, p + 3668)]%Z me m' -> wmono s0segs me m' -> rook ro' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 h) y11 (Z_to_bv 64 255) (Z_to_bv 64 NRO) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) (Z_to_bv 64 h3)
                            x17 y18 x19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x20d18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp (Z_to_bv 64 256) (Z_to_bv 64 i) x6 x7 x8
                          (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 h) x11 (Z_to_bv 64 255) (Z_to_bv 64 NRO) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) (Z_to_bv 64 h3)
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 i) x28 x29 x30)
                     F (Z_to_bv 64 0x20b94) fc None m (seg_rom s0segs)).
  Proof using XOK XSEP.
    intros h h3 ft x17 x19. induction r as [|r IH]; [intros; lia|].
    intros i ro x0 x6 x7 x8 x11 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 me m Hh Hh3 Hi Hr ROK MONOf RO FTB MI FV FA FF MU WM K.
    msenv_open XOK.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK i ltac:(lia)) as Ri. set (vv := zget ro i) in Ri. pose proof (MONOf vv ltac:(lia)) as Mv.
    urun.
    rd32_at RO i. fold vv. try rewrite (zx32_of_Z vv) by lia.
    urun_to 0x20bdc%Z.
    rewrite ms_sh_pass_S in K. cbv zeta in K. fold vv in K.
    destruct (ms_sh_shift 300 ro ft h3 i vv) as [ro1 j] eqn:SH.
    enter_with (U0_sh_while i h h3 vv ft x17 x19 300%nat i ro _ _ _ _ _ _ _ _ me m);
      [st_eq| lia| lia| lia| lia| cbn; lia| exact ROK| lia| exact MONOf| exact RO| exact FTB| exact MI| exact FV| exact FA| exact FF| exact MU| exact WM|].
    intros m' ra' a2' s8' s9' s10' s11'. cbv zeta. rewrite SH. cbn [fst snd]. intros RO' FTB' MI' FV' FA' FF' MU' WM' ROK' J'.
    clear RO FTB MI MU WM FV FA FF.
    pose proof (zw32_length ro1 256 ltac:(lia)) as LR1.
    urun.
    pose proof (u32arr_store_ok s0segs m' (p + 2644) _ j _ RO' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store RO' j vv (rewrite unsigned_lit by lia; reflexivity).
    set (ro2 := zset ro1 j vv) in RO', K.
    assert (ROK2 : rook ro2) by (intros k Hk; subst ro2; rewrite zget_zset; destruct (k =? j); [exact Ri| apply ROK'; lia]).
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ro2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me); [st_eq| lia| lia| lia| lia| exact ROK2| exact MONOf| exact RO'| exact FTB'| assumption| assumption| assumption| assumption| assumption| assumption| exact K].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_sh_pass] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact RO'| exact FTB'| assumption| assumption| assumption| assumption| assumption| assumption| exact ROK2].
  Qed.

  Lemma S0_shell_iter : forall (h h3 : Z) (ro ft : zarr)
      (x0 x4 x5 x6 x7 x8 x11 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    (4 <= h <= 364)%Z -> (h3 = h / 3)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr s0segs m (p + 2644) (zw32 ro 256) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    FRV m -> FRA m -> FRF m ->
    munch [(p + 2644, p + 3668)]%Z me m -> wmono s0segs me m ->
    (forall m' (y0 y4 y5 y6 y7 y8 y11 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      let ro' := ms_sh_pass (Z.to_nat (256 - h3)) ro ft h3 h3 in
      u32arr s0segs m' (p + 2644) (zw32 ro' 256) -> u32arr s0segs m' FT (zw32 ft 65537) -> mem_inv s0segs m' ->
      FRV m' -> FRA m' -> FRF m' ->
      munch [(p + 2644, p + 3668)]%Z me m' -> wmono s0segs me m' -> rook ro' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 h) y11 (Z_to_bv 64 255) (Z_to_bv 64 NRO) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) (Z_to_bv 64 h3)
                            x17 y18 x19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x20d18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 h) x11 (Z_to_bv 64 255) (Z_to_bv 64 NRO) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20b58) fc None m (seg_rom s0segs)).
  Proof using XOK XSEP.
    intros h h3 ro ft x0 x4 x5 x6 x7 x8 x11 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m Hh Hh3 ROK MONOf RO FTB MI FV FA FF MU WM K.
    msenv_open XOK.
    assert (H3 : (1 <= h3 <= 121)%Z) by (subst h3; Z.div_mod_to_equations; lia).
    wstep. wstep. rewrite (Z.div_small (h * 1431655766) 9223372036854775808) by lia.
    wstep. rewrite div3_magic by lia. rewrite <- Hh3. wstep.
    urun.
    if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    urun.
    if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    urun_to 0x20b94%Z.
    enter_with (U0_sh_pass h h3 ft x17 x19 (Z.to_nat (256 - h3)) h3 ro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me m);
      [st_eq| lia| lia| lia| lia| exact ROK| exact MONOf| exact RO| exact FTB| exact MI| exact FV| exact FA| exact FF| exact MU| exact WM| exact K].
  Qed.

  Lemma S0_ro_init_gen : forall (x0 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word)
      (r : nat) (i : Z) (ro bd : zarr) (J JB : list byte) (me m : word -> option byte),
    (Z.of_nat r = 256 - i)%Z -> (0 <= i < 256)%Z ->
    (forall k, 0 <= k < i -> zdef ro k = true /\ zget ro k = k)%Z -> (forall k, 0 <= k < i -> zdef bd k = true /\ zget bd k = 0)%Z ->
    Z.of_nat (length J) = 1024%Z -> Z.of_nat (length JB) = 256%Z ->
    u32arr s0segs m (p + 2644) (ovw ro J 256) -> u8arr s0segs m (p + 2388) (ovb bd JB 256) -> mem_inv s0segs m ->
    FRV m -> FRA m -> FRF m ->
    munch [(p + 2388, p + 3668)]%Z me m -> wmono s0segs me m ->
    (forall m', let rr := ms_ro_init r bd ro i in
      u32arr s0segs m' (p + 2644) (ovw (snd rr) J 256) -> u8arr s0segs m' (p + 2388) (ovb (fst rr) JB 256) -> mem_inv s0segs m' ->
      FRV m' -> FRA m' -> FRF m' ->
      munch [(p + 2388, p + 3668)]%Z me m' -> wmono s0segs me m' ->
      (forall k, 0 <= k < 256 -> zdef (snd rr) k = true /\ zget (snd rr) k = k)%Z ->
      (forall k, 0 <= k < 256 -> zdef (fst rr) k = true /\ zget (fst rr) k = 0)%Z ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            (Z_to_bv 64 256) (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 (p + 3668)) x13 x14 x15 x16
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x20b38) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 i) (Z_to_bv 64 (p + 2644 + 4 * i)) (Z_to_bv 64 (p + 2388 + i)) (Z_to_bv 64 (p + 3668)) x13 x14 x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20b20) fc None m (seg_rom s0segs)).
  Proof using XOK XSEP.
    intros x0 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30.
    induction r as [|r IH]; [intros; lia|].
    intros i ro bd J JB me m Hr Hi DEF DEFB LJ LJb RO BD MI FV FA FF MU WM K.
    msenv_open XOK.
    pose proof (ovw_length ro J 256 ltac:(lia)) as LR. pose proof (ovb_length bd JB 256 ltac:(lia)) as LB.
    assert (SO : store_ok s0segs m (wa (p + 2388 + i)) 1 = true)
      by (eapply (u8arr_storeN_ok s0segs m (p + 2388) _ i 1 _ BD); [lia| rewrite ovb_length_nat; lia| reflexivity]).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
      pose proof (ovb_write1_zset s0segs mm (p + 2388) bd JB 256 i 0 BD ltac:(lia) ltac:(lia)) as BDw; clear BD;
      change bs with [Z_to_bv 8 0]; store_done; rename BDw into BD end.
    set (bd1 := zset bd i 0) in BD.
    assert (DEFB1 : forall k, (0 <= k < i + 1)%Z -> zdef bd1 k = true /\ zget bd1 k = 0%Z).
    { intros k Hk. subst bd1. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k i); [subst; split; reflexivity|]. apply DEFB. lia. }
    pose proof (u32arr_store_ok s0segs _ (p + 2644) _ i _ RO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2.
    wstep. ovw_store RO i i (rewrite unsigned_lit by lia; reflexivity).
    set (ro1 := zset ro i i) in RO.
    assert (DEF1 : forall k, (0 <= k < i + 1)%Z -> zdef ro1 k = true /\ zget ro1 k = k).
    { intros k Hk. subst ro1. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k i); [subst; split; reflexivity|]. apply DEF. lia. }
    urun.
    rewrite ms_ro_init_S in K. fold ro1 in K. fold bd1 in K.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ro1 bd1 J JB me); [st_eq| lia| lia| exact DEF1| exact DEFB1| exact LJ| exact LJb| exact RO| exact BD| assumption| assumption| assumption| assumption| assumption| assumption|].
      intros m'. cbv zeta. exact (K m').
    - assert (r = 0)%nat by lia. subst r. cbn [ms_ro_init fst snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
        [st_eq| exact RO| exact BD| assumption| assumption| assumption| assumption| assumption| assumption| intros k Hk; apply DEF1; lia| intros k Hk; apply DEFB1; lia].
  Qed.

  Lemma S0_ro_init : forall (J JB : list byte)
      (x0 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    Z.of_nat (length J) = 1024%Z -> Z.of_nat (length JB) = 256%Z ->
    u32arr s0segs m (p + 2644) (ovw znew J 256) -> rw_cells s0segs m (p + 2388) [CB (Z.to_nat 256) JB] -> mem_inv s0segs m ->
    FRV m -> FRA m -> FRF m ->
    munch [(p + 2388, p + 3668)]%Z me m -> wmono s0segs me m ->
    (forall m', let ro' := snd (ms_ro_init 256 znew znew 0) in
      u32arr s0segs m' (p + 2644) (ovw ro' J 256) -> u8arr s0segs m' (p + 2388) (zb8 znew 256) -> mem_inv s0segs m' ->
      FRV m' -> FRA m' -> FRF m' ->
      munch [(p + 2388, p + 3668)]%Z me m' -> wmono s0segs me m' -> (forall k, 0 <= k < 256 -> zdef ro' k = true /\ zget ro' k = k)%Z ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            (Z_to_bv 64 256) (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 (p + 3668)) x13 x14 x15 x16
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x20b38) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 0) (Z_to_bv 64 (p + 2644)) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 (p + 3668)) x13 x14 x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20b20) fc None m (seg_rom s0segs)).
  Proof using XOK XSEP.
    intros J JB x0 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m LJ LJb RO BDc MI FV FA FF MU WM K.
    pose proof (ovb_init s0segs m (p + 2388) 256 JB BDc ltac:(lia)) as BD.
    enter_with (S0_ro_init_gen x0 x4 x5 x6 x7 x8 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 256%nat 0%Z znew znew J JB me m);
      [st_eq| lia| lia| intros; lia| intros; lia| exact LJ| exact LJb| exact RO| exact BD| exact MI| exact FV| exact FA| exact FF| exact MU| exact WM|].
    intros m'. cbv zeta. intros RO' BD' MI' FV' FA' FF' MU' WM' DEF' DEFB'.
    eapply K; [exact RO'| | exact MI'| exact FV'| exact FA'| exact FF'| exact MU'| exact WM'| exact DEF'].
    rewrite (ovb_defined_zb8 _ JB 256) in BD' by (intros k Hk; apply (DEFB' k Hk)).
    replace (zb8 znew 256) with (zb8 (fst (ms_ro_init 256 znew znew 0)) 256); [exact BD'|].
    apply zb8_ext. intros k Hk. rewrite zget_znew. apply (DEFB' k Hk).
  Qed.


End S0MS.

End ACeilS1.
