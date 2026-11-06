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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_msV B0_cmp_msW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable sv : slv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation RO := (am_RO Y). Notation BD := (am_BD Y).
  Notation NRO := (18446744073709551615 - am_RO Y)%Z.
  Notation SL := (slb_cells X Y SHF SHn sv).
  Notation WRO := [(RO, RO + 1024)]%Z.
  Notation WRB := [(RO, RO + 1024); (BD, BD + 256)]%Z.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.
  Ltac sw32_at FTB idx v :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FTB with u32arr ?segs mm ?A (zw32 ?a ?nn) =>
        let SO := fresh "SO" in
        pose proof (u32arr_store_ok segs mm A _ idx _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO;
        wstep; zw32_store FTB idx v (rewrite unsigned_lit by lia; f_equal; lia); try clear SO
      end end.

  Notation BF ft v := (zget ft ((v + 1) * 256) - zget ft (v * 256))%Z.

  (* [comment removed for export] *)
  Lemma B0_sh_while : forall (x15 : word) (i : Z) (f : nat) (j h vv : Z) (ro ft : zarr)
      (xra x11 x12 x13 x16 x19 x21 x25 x26 : word) (me m : word -> option byte),
    (1 <= h <= 255)%Z -> (h <= j <= i)%Z -> (i < 256)%Z -> (j + 1 <= h * Z.of_nat f)%Z -> rook ro -> (0 <= vv < 256)%Z ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr b0segs m RO (zw32 ro 256) -> u32arr b0segs m FT (zw32 ft 65537) -> rw_cells b0segs m P SL -> mem_inv b0segs m ->
    munch WRO me m -> wmono b0segs me m ->
    shzW b0segs WRO me RO (RO + 1024) -> shzW b0segs WRO me FT (FT + 262144) -> shpW b0segs WRO me FT (FT + 262148) ->
    (forall m' (xra' x11' x12' x13' x16' x19' x21' : word), let rr := ms_sh_shift f ro ft h j vv in
      u32arr b0segs m' RO (zw32 (fst rr) 256) -> u32arr b0segs m' FT (zw32 ft 65537) -> rw_cells b0segs m' P SL -> mem_inv b0segs m' ->
      munch WRO me m' -> wmono b0segs me m' -> rook (fst rr) -> (0 <= snd rr <= j)%Z ->
      evt b0segs Q (MS (mkR xra' (Z_to_bv 64 P) gp tp (Z_to_bv 64 1431655766) (Z_to_bv 64 (1024 * (vv + 1))) (Z_to_bv 64 h) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (FT + 1024 * vv)) x11' x12' x13' (Z_to_bv 64 NRO) x15 x16' (Z_to_bv 64 255)
                            (Z_to_bv 64 (vv + 1)) x19' (Z_to_bv 64 (snd rr)) x21' (Z_to_bv 64 (1024 * vv)) (Z_to_bv 64 0) (Z_to_bv 64 (FT + 1024 * (vv + 1)))
                            (Z_to_bv 64 (snd rr)) (Z_to_bv 64 (4 * snd rr)) cSB
                            (Z_to_bv 64 256) (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 vv))
                       F (Z_to_bv 64 0xa1fb8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp (Z_to_bv 64 1431655766) (Z_to_bv 64 (1024 * (vv + 1))) (Z_to_bv 64 h) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (FT + 1024 * vv)) x11 x12 x13 (Z_to_bv 64 NRO) x15 x16 (Z_to_bv 64 255)
                          (Z_to_bv 64 (vv + 1)) x19 (Z_to_bv 64 j) x21 (Z_to_bv 64 (1024 * vv)) (Z_to_bv 64 0) (Z_to_bv 64 (FT + 1024 * (vv + 1)))
                          x25 x26 cSB
                          (Z_to_bv 64 256) (Z_to_bv 64 i) (Z_to_bv 64 i) (Z_to_bv 64 vv))
                     F (Z_to_bv 64 0xa1dd0) fc None m (seg_rom b0segs)).
  Proof.
    intros x15 i. induction f as [|f IH]; [intros; lia|].
    intros j h vv ro ft xra x11 x12 x13 x16 x19 x21 x25 x26 me m Hh Hj Hi Hf ROK Hvv MONO ROB FTB SLB MI MU WM SHR SHFz SHP K.
    msenv_open XOK. amenv_open YOK. pose proof (amsx_F_RO X Y YSX) as APFR. box_ors. open_slb_in SLB.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK (j - h)%Z ltac:(lia)) as Rjh. set (u := zget ro (j - h)) in Rjh.
    pose proof (MONO vv ltac:(lia)) as Mv. pose proof (MONO u ltac:(lia)) as Mu.
    (* [comment removed for export] *)
    brun. rd32_at ROB (j - h)%Z. fold u.
    (* [comment removed for export] *)
    brun_to 0xa1e58%Z. ack_rd (FT + (u + 1) * 256 * 4)%Z 4%Z. ack_merge.
    (* [comment removed for export] *)
    brun. rd32_at FTB ((u + 1) * 256)%Z.
    (* [comment removed for export] *)
    brun_to 0xa1ec8%Z. ack_rd (FT + 1024 * (vv + 1))%Z 4%Z. rd32_at FTB (u * 256)%Z. ack_merge.
    (* [comment removed for export] *)
    brun. rd32_at FTB ((vv + 1) * 256)%Z. brun. rd32_at FTB (vv * 256)%Z.
    rewrite ms_sh_shift_S in K. unfold bigfreq in K. rewrite !Z.shiftl_mul_pow2 in K by lia. change (2 ^ 8)%Z with 256%Z in K. fold u in K.
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (_ <? _) with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      brun_to 0xa1fb8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
        [st_eq| exact ROB| exact FTB| exact SLB| assumption| assumption| assumption| exact ROK| lia].
    - replace (_ <? _) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv zeta in K.
      (* [comment removed for export] *)
      brun. sw32_at ROB j u.
      set (ro1 := zset ro j u) in ROB, K.
      assert (ROK1 : rook ro1) by (intros k Hk; subst ro1; rewrite zget_zset; destruct (k =? j); [exact Rjh| apply ROK; lia]).
      (* [comment removed for export] *)
      brun. if_cases Kd; zify_cond_z Kd.
      + replace (j - h <=? h - 1) with false in K by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z h vv ro1 ft _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| exact ROK1| lia| exact MONO| exact ROB| exact FTB| exact SLB| assumption| assumption| assumption| exact SHR| exact SHFz| exact SHP|].
        intros m' xra' x11' x12' x13' x16' x19' x21'. cbv zeta. intros RO' FTB' SLB' MI' MU' WM' ROK' J'.
        enter_with (K m' xra' x11' x12' x13' x16' x19' x21'); [st_eq| exact RO'| exact FTB'| exact SLB'| exact MI'| exact MU'| exact WM'| exact ROK'| lia].
      + replace (j - h <=? h - 1) with true in K by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
          [st_eq| exact ROB| exact FTB| exact SLB| assumption| assumption| assumption| exact ROK1| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_sh_pass : forall (x15 : word) (r : nat) (i h : Z) (ro ft : zarr)
      (xra x6 x11 x12 x13 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x30 x31 : word) (me m : word -> option byte),
    (1 <= h <= 255)%Z -> (h <= i <= 256)%Z -> (Z.of_nat r = 256 - i)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr b0segs m RO (zw32 ro 256) -> u32arr b0segs m FT (zw32 ft 65537) -> rw_cells b0segs m P SL -> mem_inv b0segs m ->
    munch WRO me m -> wmono b0segs me m ->
    shzW b0segs WRO me RO (RO + 1024) -> shzW b0segs WRO me FT (FT + 262144) -> shpW b0segs WRO me FT (FT + 262148) ->
    (forall m' (xra' x6' x11' x12' x13' x16' x18' x19' x20' x21' x22' x23' x24' x25' x26' x30' x31' : word), let ro' := ms_sh_pass r ro ft h i in
      u32arr b0segs m' RO (zw32 ro' 256) -> u32arr b0segs m' FT (zw32 ft 65537) -> rw_cells b0segs m' P SL -> mem_inv b0segs m' ->
      munch WRO me m' -> wmono b0segs me m' -> rook ro' ->
      evt b0segs Q (MS (mkR xra' (Z_to_bv 64 P) gp tp (Z_to_bv 64 1431655766) x6' (Z_to_bv 64 h) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 256) x11' x12' x13' (Z_to_bv 64 NRO) x15 x16' (Z_to_bv 64 255)
                            x18' x19' x20' x21' x22' x23' x24' x25' x26' cSB
                            (Z_to_bv 64 256) (Z_to_bv 64 256) x30' x31')
                       F (Z_to_bv 64 0xa2010) fc None m' (seg_rom b0segs))) ->
    (i < 256)%Z ->
    evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp (Z_to_bv 64 1431655766) x6 (Z_to_bv 64 h) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 i) x11 x12 x13 (Z_to_bv 64 NRO) x15 x16 (Z_to_bv 64 255)
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB
                          (Z_to_bv 64 256) (Z_to_bv 64 i) x30 x31)
                     F (Z_to_bv 64 0xa1d74) fc None m (seg_rom b0segs)).
  Proof.
    intros x15. induction r as [|r IH]; [intros; lia|].
    intros i h ro ft xra x6 x11 x12 x13 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x30 x31 me m Hh Hi Hr ROK MONO ROB FTB SLB MI MU WM SHR SHFz SHP K Hi2.
    msenv_open XOK. amenv_open YOK. pose proof (amsx_F_RO X Y YSX) as APFR. box_ors. open_slb_in SLB.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK i ltac:(lia)) as Ri. set (vv := zget ro i) in Ri. pose proof (MONO vv ltac:(lia)) as Mv.
    (* [comment removed for export] *)
    brun. rd32_at ROB i. fold vv.
    (* [comment removed for export] *)
    brun_to 0xa1dd0%Z.
    rewrite ms_sh_pass_S in K. cbv zeta in K. fold vv in K.
    destruct (ms_sh_shift 300 ro ft h i vv) as [ro1 j] eqn:SH.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_sh_while x15 i 300%nat i h vv ro ft _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| lia| lia| lia| cbn; lia| exact ROK| lia| exact MONO| exact ROB| exact FTB| exact SLB| exact MI| exact MU| exact WM| exact SHR| exact SHFz| exact SHP|].
    intros m' xra' x11' x12' x13' x16' x19' x21'. cbv zeta. rewrite SH. cbn [fst snd]. intros RO' FTB' SLB' MI' MU' WM' ROK' J'.
    clear ROB FTB SLB MI MU WM. open_slb_in SLB'.
    pose proof (zw32_length ro1 256 ltac:(lia)) as LR1.
    (* [comment removed for export] *)
    brun. sw32_at RO' j vv.
    set (ro2 := zset ro1 j vv) in RO', K.
    assert (ROK2 : rook ro2) by (intros k Hk; subst ro2; rewrite zget_zset; destruct (k =? j); [exact Ri| apply ROK'; lia]).
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z h ro2 ft _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me); [st_eq| lia| lia| lia| exact ROK2| exact MONO| exact RO'| exact FTB'| exact SLB'| assumption| assumption| assumption| exact SHR| exact SHFz| exact SHP| exact K| lia].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_sh_pass] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact RO'| exact FTB'| exact SLB'| assumption| assumption| assumption| exact ROK2].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_shell_iter : forall (h h3 : Z) (ro ft : zarr)
      (xra x6 x7 x10 x11 x12 x13 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (4 <= h <= 364)%Z -> (h3 = h / 3)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr b0segs m RO (zw32 ro 256) -> u32arr b0segs m FT (zw32 ft 65537) -> rw_cells b0segs m P SL -> mem_inv b0segs m ->
    munch WRO me m -> wmono b0segs me m ->
    shzW b0segs WRO me RO (RO + 1024) -> shzW b0segs WRO me FT (FT + 262144) -> shpW b0segs WRO me FT (FT + 262148) ->
    (forall m' (xra' x6' x11' x12' x13' x16' x18' x19' x20' x21' x22' x23' x24' x25' x26' x30' x31' : word), let ro' := ms_sh_pass (Z.to_nat (256 - h3)) ro ft h3 h3 in
      u32arr b0segs m' RO (zw32 ro' 256) -> u32arr b0segs m' FT (zw32 ft 65537) -> rw_cells b0segs m' P SL -> mem_inv b0segs m' ->
      munch WRO me m' -> wmono b0segs me m' -> rook ro' ->
      evt b0segs Q (MS (mkR xra' (Z_to_bv 64 P) gp tp (Z_to_bv 64 1431655766) x6' (Z_to_bv 64 h3) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 256) x11' x12' x13' (Z_to_bv 64 NRO) (Z_to_bv 64 h) x16' (Z_to_bv 64 255)
                            x18' x19' x20' x21' x22' x23' x24' x25' x26' cSB
                            (Z_to_bv 64 256) (Z_to_bv 64 256) x30' x31')
                       F (Z_to_bv 64 0xa2010) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp (Z_to_bv 64 1431655766) x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 (Z_to_bv 64 NRO) (Z_to_bv 64 h) x16 (Z_to_bv 64 255)
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa1d38) fc None m (seg_rom b0segs)).
  Proof.
    intros h h3 ro ft xra x6 x7 x10 x11 x12 x13 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 me m Hh Hh3 ROK MONO ROB FTB SLB MI MU WM SHR SHFz SHP K.
    msenv_open XOK.
    assert (H3 : (1 <= h3 <= 121)%Z) by (subst h3; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep. wstep. rewrite (Z.div_small (h * 1431655766) 9223372036854775808) by lia.
    wstep. rewrite div3_magic by lia. rewrite <- Hh3. wstep.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    wstep. wstep. wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|]. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite ?zext32_id. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_sh_pass (Z_to_bv 64 h) (Z.to_nat (256 - h3)) h3 h3 ro ft _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| lia| lia| lia| exact ROK| exact MONO| exact ROB| exact FTB| exact SLB| exact MI| exact MU| exact WM| exact SHR| exact SHFz| exact SHP| exact K| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_ro_init : forall (xra x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (r : nat) (i : Z) (ro bd : zarr) (J Jb : list byte) (me m : word -> option byte),
    (Z.of_nat r = 256 - i)%Z -> (0 <= i < 256)%Z ->
    (forall k, 0 <= k < i -> zdef ro k = true /\ zget ro k = k)%Z -> (forall k, 0 <= k < i -> zdef bd k = true /\ zget bd k = 0)%Z ->
    Z.of_nat (length J) = 1024%Z -> Z.of_nat (length Jb) = 256%Z ->
    u32arr b0segs m RO (ovw ro J 256) -> u8arr b0segs m BD (ovb bd Jb 256) -> rw_cells b0segs m P SL -> mem_inv b0segs m ->
    munch WRB me m -> wmono b0segs me m ->
    (forall m', let rr := ms_ro_init r bd ro i in
      u32arr b0segs m' RO (ovw (snd rr) J 256) -> u8arr b0segs m' BD (ovb (fst rr) Jb 256) -> rw_cells b0segs m' P SL -> mem_inv b0segs m' ->
      munch WRB me m' -> wmono b0segs me m' ->
      (forall k, 0 <= k < 256 -> zdef (snd rr) k = true /\ zget (snd rr) k = k)%Z -> (forall k, 0 <= k < 256 -> zdef (fst rr) k = true /\ zget (fst rr) k = 0)%Z ->
      evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 256) (Z_to_bv 64 (RO + 1024)) (Z_to_bv 64 (BD + 256)) (Z_to_bv 64 (RO + 1024)) x14 x15 x16 x17
                            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa1d20) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 i) (Z_to_bv 64 (RO + 1024)) (Z_to_bv 64 (BD + i)) (Z_to_bv 64 (RO + 4 * i)) x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa1d08) fc None m (seg_rom b0segs)).
  Proof.
    intros xra x5 x6 x7 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    induction r as [|r IH]; [intros; lia|].
    intros i ro bd J Jb me m Hr Hi DEF DEFB LJ LJb ROB BDB SLB MI MU WM K.
    msenv_open XOK. amenv_open YOK. open_slb_in SLB.
    pose proof (ovw_length ro J 256 ltac:(lia)) as LR. pose proof (ovb_length bd Jb 256 ltac:(lia)) as LB.
    (* [comment removed for export] *)
    assert (SO : store_ok b0segs m (wa (BD + i)) 1 = true)
      by (eapply (u8arr_storeN_ok b0segs m BD _ i 1 _ BDB); [lia| rewrite ovb_length_nat; lia| reflexivity]).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?ad ?bs) _) =>
      pose proof (ovb_write1_zset b0segs mm BD bd Jb 256 i 0 BDB ltac:(lia) ltac:(lia)) as BDw; clear BDB;
      change bs with [Z_to_bv 8 0]; store_done; rename BDw into BDB end.
    set (bd1 := zset bd i 0) in BDB.
    assert (DEFB1 : forall k, (0 <= k < i + 1)%Z -> zdef bd1 k = true /\ zget bd1 k = 0%Z).
    { intros k Hk. subst bd1. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k i); [subst; split; reflexivity|]. apply DEFB. lia. }
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok b0segs _ RO _ i _ ROB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2.
    wstep. ovw_store ROB i i (rewrite unsigned_lit by lia; reflexivity).
    set (ro1 := zset ro i i) in ROB.
    assert (DEF1 : forall k, (0 <= k < i + 1)%Z -> zdef ro1 k = true /\ zget ro1 k = k).
    { intros k Hk. subst ro1. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k i); [subst; split; reflexivity|]. apply DEF. lia. }
    wstep. wstep. wstep.
    rewrite ms_ro_init_S in K. fold ro1 in K. fold bd1 in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ro1 bd1 J Jb me); [st_eq| lia| lia| exact DEF1| exact DEFB1| exact LJ| exact LJb| exact ROB| exact BDB| exact SLB| assumption| assumption| assumption|].
      intros m'. cbv zeta. exact (K m').
    - assert (r = 0)%nat by lia. subst r. cbn [ms_ro_init fst snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
        [st_eq| exact ROB| exact BDB| exact SLB| assumption| assumption| assumption| intros k Hk; apply DEF1; lia| intros k Hk; apply DEFB1; lia].
  Qed.
End B0MS.
End ACeilS1.
