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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_msV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880). Notation RO := (am_RO Y).
  Notation WRO := [(RO, RO + 1024)]%Z.
  Variables (ra s4 s5 s6 s8 s9 s10 : word).

  (* [comment removed for export] *)
  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.

  Notation BF ft v := (zget ft ((v + 1) * 256) - zget ft (v * 256))%Z.

  (* [comment removed for export] *)
  Lemma A0_sh_while : forall (i : Z) (f : nat) (j h vv : Z) (ro ft : zarr) (x11 x12 x13 x14 x15 x18 x28 x30 x31 : word) (me m : word -> option byte),
    (1 <= h <= 255)%Z -> (h <= j <= i)%Z -> (i < 256)%Z -> (j + 1 <= h * Z.of_nat f)%Z -> rook ro -> (0 <= vv < 256)%Z ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr a0segs m RO (zw32 ro 256) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch WRO me m -> wmono a0segs me m ->
    shzW a0segs WRO me RO (RO + 1024) -> shzW a0segs WRO me FT (FT + 262144) -> shpW a0segs WRO me FT (FT + 262148) ->
    (forall m' (x10' x11' x18' x30' x31' : word), let rr := ms_sh_shift f ro ft h j vv in
      u32arr a0segs m' RO (zw32 (fst rr) 256) -> u32arr a0segs m' FT (zw32 ft 65537) -> mem_inv a0segs m' ->
      munch WRO me m' -> wmono a0segs me m' -> rook (fst rr) -> (0 <= snd rr <= j)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 256) (Z_to_bv 64 i) (Z_to_bv 64 vv) (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12 x13 x14 x15 (Z_to_bv 64 h) (Z_to_bv 64 (i - h))
                            x18' cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 (Z_to_bv 64 RO) (Z_to_bv 64 (snd rr)) (Z_to_bv 64 (BF ft vv)) x30' x31')
                       F (Z_to_bv 64 0x98674) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 256) (Z_to_bv 64 i) (Z_to_bv 64 vv) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (j - h)) x11 x12 x13 x14 x15 (Z_to_bv 64 h) (Z_to_bv 64 (i - h))
                          x18 cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 (Z_to_bv 64 RO) x28 (Z_to_bv 64 (BF ft vv)) x30 x31)
                     F (Z_to_bv 64 0x9859c) fc None m (seg_rom a0segs)).
  Proof.
    intros i. induction f as [|f IH]; [intros; lia|].
    intros j h vv ro ft x11 x12 x13 x14 x15 x18 x28 x30 x31 me m Hh Hj Hi Hf ROK Hvv MONO ROB FTB MI MU WM SHR SHF SHP K.
    msenv_open XOK. amenv_open YOK. pose proof (amsx_F_RO X Y YSX) as APFR. box_ors.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK (j - h)%Z ltac:(lia)) as Rjh. set (u := zget ro (j - h)) in Rjh.
    pose proof (MONO vv ltac:(lia)) as Mv. pose proof (MONO u ltac:(lia)) as Mu.
    (* [comment removed for export] *)
    arun. rd32_at ROB (j - h)%Z. fold u.
    (* [comment removed for export] *)
    arun_to 0x985d4%Z. ack_rd (FT + (u * 256 + 256) * 4)%Z 4%Z. ack_merge.
    (* [comment removed for export] *)
    arun. rd32_at FTB ((u + 1) * 256)%Z. arun. rd32_at FTB (u * 256)%Z.
    rewrite ms_sh_shift_S in K. unfold bigfreq in K. rewrite !Z.shiftl_mul_pow2 in K by lia. change (2 ^ 8)%Z with 256%Z in K. fold u in K.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (_ <? _) with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
        [st_eq| exact ROB| exact FTB| assumption| assumption| assumption| exact ROK| lia].
    - replace (_ <? _) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv zeta in K.
      (* [comment removed for export] *)
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm RO _ j _ ROB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store ROB j u (rewrite unsigned_lit by lia; reflexivity).
      set (ro1 := zset ro j u) in ROB, K.
      assert (ROK1 : rook ro1) by (intros k Hk; subst ro1; rewrite zget_zset; destruct (k =? j); [exact Rjh| apply ROK; lia]).
      (* [comment removed for export] *)
      arun. if_cases Kd; zify_cond_z Kd.
      + replace (j - h <=? h - 1) with false in K by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z h vv ro1 ft _ x12 x13 x14 x15 _ _ _ _ me); [st_eq| lia| lia| lia| lia| exact ROK1| lia| exact MONO| exact ROB| exact FTB| assumption| assumption| assumption| exact SHR| exact SHF| exact SHP|].
        intros m' x10' x11' x18' x30' x31'. cbv zeta. intros RO' FTB' MI' MU' WM' ROK' J'.
        enter_with (K m' x10' x11' x18' x30' x31'); [st_eq| exact RO'| exact FTB'| exact MI'| exact MU'| exact WM'| exact ROK'| lia].
      + replace (j - h <=? h - 1) with true in K by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact ROB| exact FTB| assumption| assumption| assumption| exact ROK1| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_sh_pass : forall (r : nat) (i h : Z) (ro ft : zarr) (x7 x10 x11 x12 x13 x14 x15 x18 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h <= 255)%Z -> (h <= i <= 256)%Z -> (Z.of_nat r = 256 - i)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr a0segs m RO (zw32 ro 256) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch WRO me m -> wmono a0segs me m ->
    shzW a0segs WRO me RO (RO + 1024) -> shzW a0segs WRO me FT (FT + 262144) -> shpW a0segs WRO me FT (FT + 262148) ->
    (forall m' (x7' x10' x11' x18' x28' x29' x30' x31' : word), let ro' := ms_sh_pass r ro ft h i in
      u32arr a0segs m' RO (zw32 ro' 256) -> u32arr a0segs m' FT (zw32 ft 65537) -> mem_inv a0segs m' ->
      munch WRO me m' -> wmono a0segs me m' -> rook ro' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 256) (Z_to_bv 64 256) x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12 x13 x14 x15 (Z_to_bv 64 h) (Z_to_bv 64 (256 - h))
                            x18' cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 (Z_to_bv 64 RO) x28' x29' x30' x31')
                       F (Z_to_bv 64 0x986e0) fc None m' (seg_rom a0segs))) ->
    (i < 256)%Z ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 256) (Z_to_bv 64 i) x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 (Z_to_bv 64 h) (Z_to_bv 64 (i - h))
                          x18 cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 (Z_to_bv 64 RO) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98538) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]; [intros; lia|].
    intros i h ro ft x7 x10 x11 x12 x13 x14 x15 x18 x28 x29 x30 x31 me m Hh Hi Hr ROK MONO ROB FTB MI MU WM SHR SHF SHP K Hi2.
    msenv_open XOK. amenv_open YOK. pose proof (amsx_F_RO X Y YSX) as APFR. box_ors.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK i ltac:(lia)) as Ri. set (vv := zget ro i) in Ri. pose proof (MONO vv ltac:(lia)) as Mv.
    (* [comment removed for export] *)
    arun. rd32_at ROB i. fold vv.
    (* [comment removed for export] *)
    arun_to 0x9856c%Z. ack_rd (FT + (vv * 256 + 256) * 4)%Z 4%Z. ack_merge.
    (* [comment removed for export] *)
    arun. rd32_at FTB ((vv + 1) * 256)%Z. arun. rd32_at FTB (vv * 256)%Z. arun_to 0x9859c%Z.
    rewrite ms_sh_pass_S in K. cbv zeta in K. fold vv in K.
    destruct (ms_sh_shift 300 ro ft h i vv) as [ro1 j] eqn:SH.
    enter_with (A0_sh_while i 300%nat i h vv ro ft _ x12 x13 x14 x15 _ _ _ _ me m);
      [st_eq| lia| lia| lia| cbn; lia| exact ROK| lia| exact MONO| exact ROB| exact FTB| exact MI| exact MU| exact WM| exact SHR| exact SHF| exact SHP|].
    intros m' x10' x11' x18' x30' x31'. cbv zeta. rewrite SH. cbn [fst snd]. intros RO' FTB' MI' MU' WM' ROK' J'.
    clear ROB FTB MI MU WM.
    pose proof (zw32_length ro1 256 ltac:(lia)) as LR1.
    (* [comment removed for export] *)
    arun.
    pose proof (u32arr_store_ok a0segs m' RO _ j _ RO' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store RO' j vv (rewrite unsigned_lit by lia; reflexivity).
    set (ro2 := zset ro1 j vv) in RO', K.
    assert (ROK2 : rook ro2) by (intros k Hk; subst ro2; rewrite zget_zset; destruct (k =? j); [exact Ri| apply ROK'; lia]).
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z h ro2 ft _ _ _ x12 x13 x14 x15 _ _ _ _ _ me); [st_eq| lia| lia| lia| exact ROK2| exact MONO| exact RO'| exact FTB'| assumption| assumption| assumption| exact SHR| exact SHF| exact SHP| exact K| lia].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_sh_pass] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [st_eq| exact RO'| exact FTB'| assumption| assumption| assumption| exact ROK2].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_shell_iter : forall (h h3 : Z) (ro ft : zarr) (x5 x6 x7 x10 x11 x16 x17 x18 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (4 <= h <= 364)%Z -> (h3 = h / 3)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr a0segs m RO (zw32 ro 256) -> u32arr a0segs m FT (zw32 ft 65537) -> mem_inv a0segs m ->
    munch WRO me m -> wmono a0segs me m ->
    shzW a0segs WRO me RO (RO + 1024) -> shzW a0segs WRO me FT (FT + 262144) -> shpW a0segs WRO me FT (FT + 262148) ->
    (forall m' (x7' x10' x11' x18' x28' x29' x30' x31' : word), let ro' := ms_sh_pass (Z.to_nat (256 - h3)) ro ft h3 h3 in
      u32arr a0segs m' RO (zw32 ro' 256) -> u32arr a0segs m' FT (zw32 ft 65537) -> mem_inv a0segs m' ->
      munch WRO me m' -> wmono a0segs me m' -> rook ro' ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 256) (Z_to_bv 64 256) x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' (Z_to_bv 64 h) (Z_to_bv 64 767) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) (Z_to_bv 64 h3) (Z_to_bv 64 (256 - h3))
                            x18' cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 (Z_to_bv 64 RO) x28' x29' x30' x31')
                       F (Z_to_bv 64 0x986e0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 (Z_to_bv 64 h) (Z_to_bv 64 767) (Z_to_bv 64 1431655766) (Z_to_bv 64 2) x16 x17
                          x18 cSB s4 s5 s6 (Z_to_bv 64 FT) s8 s9 s10 (Z_to_bv 64 RO) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98508) fc None m (seg_rom a0segs)).
  Proof.
    intros h h3 ro ft x5 x6 x7 x10 x11 x16 x17 x18 x28 x29 x30 x31 me m Hh Hh3 ROK MONO ROB FTB MI MU WM SHR SHF SHP K.
    msenv_open XOK.
    assert (H3 : (1 <= h3 <= 121)%Z) by (subst h3; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep. wstep. rewrite (Z.div_small (h * 1431655766) 9223372036854775808) by lia.
    wstep. rewrite div3_magic by lia. rewrite <- Hh3. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    wstep. wstep. wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    wstep. wstep. wstep. wstep.
    enter_with (A0_sh_pass (Z.to_nat (256 - h3)) h3 h3 ro ft _ _ _ _ _ _ _ _ _ _ _ _ me m);
      [st_eq| lia| lia| lia| exact ROK| exact MONO| exact ROB| exact FTB| exact MI| exact MU| exact WM| exact SHR| exact SHF| exact SHP| exact K| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_ro_init : forall (r : nat) (i : Z) (ro bd : zarr) (J : list byte) (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s11 t3 t4 t5 t6 : word) (me m : word -> option byte),
    (Z.of_nat r = 256 - i)%Z -> (0 <= i < 256)%Z -> (forall k, 0 <= k < i -> zdef ro k = true /\ zget ro k = k)%Z ->
    Z.of_nat (length J) = 1024%Z ->
    u32arr a0segs m RO (ovw ro J 256) -> mem_inv a0segs m ->
    munch WRO me m -> wmono a0segs me m ->
    (forall m', let ro' := snd (ms_ro_init r bd ro i) in
      u32arr a0segs m' RO (ovw ro' J 256) -> mem_inv a0segs m' ->
      munch WRO me m' -> wmono a0segs me m' -> (forall k, 0 <= k < 256 -> zdef ro' k = true /\ zget ro' k = k)%Z ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 256) (Z_to_bv 64 (RO + 1024)) (Z_to_bv 64 (RO + 1024)) a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x984f0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 i) (Z_to_bv 64 (RO + 1024)) (Z_to_bv 64 (RO + 4 * i)) a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x984e0) fc None m (seg_rom a0segs)).
  Proof.
    induction r as [|r IH]; [intros; lia|].
    intros i ro bd J t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s11 t3 t4 t5 t6 me m Hr Hi DEF LJ ROB MI MU WM K.
    msenv_open XOK. amenv_open YOK.
    pose proof (ovw_length ro J 256 ltac:(lia)) as LR.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok a0segs m RO _ i _ ROB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store ROB i i (rewrite unsigned_lit by lia; reflexivity).
    set (ro1 := zset ro i i) in ROB.
    assert (DEF1 : forall k, (0 <= k < i + 1)%Z -> zdef ro1 k = true /\ zget ro1 k = k).
    { intros k Hk. subst ro1. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k i); [subst; split; reflexivity|]. apply DEF. lia. }
    wstep. wstep.
    rewrite ms_ro_init_S in K. fold ro1 in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ro1 (zset bd i 0) J t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s7 s11 t3 t4 t5 t6 me); [st_eq| lia| lia| exact DEF1| exact LJ| exact ROB| assumption| assumption| assumption|].
      intros m'. cbv zeta. exact (K m').
    - assert (r = 0)%nat by lia. subst r. cbn [ms_ro_init snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
        [st_eq| exact ROB| assumption| assumption| assumption| intros k Hk; apply DEF1; lia].
  Qed.
End A0MS.

End ACeilS1.
