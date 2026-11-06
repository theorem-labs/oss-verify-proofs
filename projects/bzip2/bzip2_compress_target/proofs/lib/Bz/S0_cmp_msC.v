(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Variables (ra t0 t1 t2 s0 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (zget a idx)) by lia
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)


  Notation BF ft v := (zget ft ((v + 1) * 256) - zget ft (v * 256))%Z.

  (* [comment removed for export] *)
  Lemma S0_sh_while : forall (x5 x10 x11 x13 x14 : word) (i : Z) (f : nat) (j h vv : Z) (ro ft : zarr) (x7 x30 x31 : word) (me m : word -> option byte),
    (1 <= h <= 255)%Z -> (h <= j <= i)%Z -> (i < 256)%Z -> (j + 1 <= h * Z.of_nat f)%Z -> rook ro -> (0 <= vv < 256)%Z ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr s0segs m (p + 2600) (zw32 ro 256) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(p + 2600, p + 3624)]%Z me m -> wmono s0segs me m ->
    (forall m' (x29' x30' x31' : word), let rr := ms_sh_shift f ro ft h j vv in
      u32arr s0segs m' (p + 2600) (zw32 (fst rr) 256) -> u32arr s0segs m' FT (zw32 ft 65537) -> mem_inv s0segs m' ->
      munch [(p + 2600, p + 3624)]%Z me m' -> wmono s0segs me m' -> rook (fst rr) -> (0 <= snd rr <= j)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 (Z_to_bv 64 vv) (Z_to_bv 64 (snd rr)) s0 (Z_to_bv 64 FT)
                            x10 x11 (Z_to_bv 64 (p + 2600)) x13 x14 (Z_to_bv 64 h) (Z_to_bv 64 (i - h)) (Z_to_bv 64 256)
                            s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (BF ft vv)) x29' x30' x31')
                       F (Z_to_bv 64 0x19a68) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 (Z_to_bv 64 vv) x7 s0 (Z_to_bv 64 FT)
                          x10 x11 (Z_to_bv 64 (p + 2600)) x13 x14 (Z_to_bv 64 h) (Z_to_bv 64 (i - h)) (Z_to_bv 64 256)
                          s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (BF ft vv)) (Z_to_bv 64 (j - h)) x30 x31)
                     F (Z_to_bv 64 0x19a10) fc None m (seg_rom s0segs)).
  Proof.
    intros x5 x10 x11 x13 x14 i. induction f as [|f IH]; [intros; lia|].
    intros j h vv ro ft x7 x30 x31 me m Hh Hj Hi Hf ROK Hvv MONO RO FTB MI MU WM K.
    msenv_open XOK.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK (j - h)%Z ltac:(lia)) as Rjh. set (u := zget ro (j - h)) in Rjh.
    pose proof (MONO vv ltac:(lia)) as Mv. pose proof (MONO u ltac:(lia)) as Mu.
    (* [comment removed for export] *)
    wstep. wstep. wstep. rd32_at RO (j - h)%Z. fold u.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    rd32_at FTB ((u + 1) * 256)%Z. rd32_at FTB (u * 256)%Z. wstep.
    (* [comment removed for export] *)
    wstep.
    rewrite ms_sh_shift_S in K. unfold bigfreq in K. rewrite !Z.shiftl_mul_pow2 in K by lia. change (2 ^ 8)%Z with 256%Z in K. fold u in K.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (_ <? _) with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
        [st_eq| exact RO| exact FTB| assumption| assumption| assumption| exact ROK| lia].
    - replace (_ <? _) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv zeta in K.
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 2600) _ j _ RO ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store RO j u (rewrite unsigned_lit by lia; reflexivity).
      set (ro1 := zset ro j u) in RO, K.
      assert (ROK1 : rook ro1) by (intros k Hk; subst ro1; rewrite zget_zset; destruct (k =? j); [exact Rjh| apply ROK; lia]).
      (* [comment removed for export] *)
      wstep.
      wstep; if_cases Kd; zify_cond_z Kd.
      + replace (j - h <=? h - 1) with false in K by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z h vv ro1 ft _ _ _ me); [st_eq| lia| lia| lia| lia| exact ROK1| lia| exact MONO| exact RO| exact FTB| assumption| assumption| assumption|].
        intros m' x29' x30' x31'. cbv zeta. intros RO' FTB' MI' MU' WM' ROK' J'.
        enter_with (K m' x29' x30' x31'); [st_eq| exact RO'| exact FTB'| exact MI'| exact MU'| exact WM'| exact ROK'| lia].
      + replace (j - h <=? h - 1) with true in K by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K.
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end;
          [st_eq| exact RO| exact FTB| assumption| assumption| assumption| exact ROK1| lia].
  Time Qed.


  (* [comment removed for export] *)
  Lemma S0_sh_pass : forall (x10 x11 x13 x14 : word) (r : nat) (i h : Z) (ro ft : zarr) (x6 x7 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h <= 255)%Z -> (h <= i <= 256)%Z -> (Z.of_nat r = 256 - i)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr s0segs m (p + 2600) (zw32 ro 256) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(p + 2600, p + 3624)]%Z me m -> wmono s0segs me m ->
    (forall m' (x6' x7' x28' x29' x30' x31' : word), let ro' := ms_sh_pass r ro ft h i in
      u32arr s0segs m' (p + 2600) (zw32 ro' 256) -> u32arr s0segs m' FT (zw32 ft 65537) -> mem_inv s0segs m' ->
      munch [(p + 2600, p + 3624)]%Z me m' -> wmono s0segs me m' -> rook ro' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp (Z_to_bv 64 256) x6' x7' s0 (Z_to_bv 64 FT)
                            x10 x11 (Z_to_bv 64 (p + 2600)) x13 x14 (Z_to_bv 64 h) (Z_to_bv 64 (256 - h)) (Z_to_bv 64 256)
                            s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' x31')
                       F (Z_to_bv 64 0x19a80) fc None m' (seg_rom s0segs))) ->
    (i < 256)%Z ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp (Z_to_bv 64 i) x6 x7 s0 (Z_to_bv 64 FT)
                          x10 x11 (Z_to_bv 64 (p + 2600)) x13 x14 (Z_to_bv 64 h) (Z_to_bv 64 (i - h)) (Z_to_bv 64 256)
                          s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x199dc) fc None m (seg_rom s0segs)).
  Proof.
    intros x10 x11 x13 x14. induction r as [|r IH]; [intros; lia|].
    intros i h ro ft x6 x7 x28 x29 x30 x31 me m Hh Hi Hr ROK MONO RO FTB MI MU WM K Hi2.
    msenv_open XOK.
    pose proof (zw32_length ro 256 ltac:(lia)) as LR. pose proof (zw32_length ft 65537 ltac:(lia)) as LF.
    pose proof (ROK i ltac:(lia)) as Ri. set (vv := zget ro i) in Ri. pose proof (MONO vv ltac:(lia)) as Mv.
    (* [comment removed for export] *)
    wstep. wstep. rd32_at RO i. fold vv.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    rd32_at FTB ((vv + 1) * 256)%Z. rd32_at FTB (vv * 256)%Z. wstep. wstep.
    rewrite ms_sh_pass_S in K. cbv zeta in K. fold vv in K.
    destruct (ms_sh_shift 300 ro ft h i vv) as [ro1 j] eqn:SH.
    eapply (S0_sh_while (Z_to_bv 64 i) x10 x11 x13 x14 i 300%nat i h vv ro ft _ _ _ me m);
      [lia| lia| lia| cbn; lia| exact ROK| lia| exact MONO| exact RO| exact FTB| exact MI| exact MU| exact WM|].
    intros m' x29' x30' x31'. cbv zeta. rewrite SH. cbn [fst snd]. intros RO' FTB' MI' MU' WM' ROK' J'.
    clear RO FTB MI MU WM.
    pose proof (zw32_length ro1 256 ltac:(lia)) as LR1.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    pose proof (u32arr_store_ok s0segs m' (p + 2600) _ j _ RO' ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO.
    wstep. zw32_store RO' j vv (rewrite unsigned_lit by lia; reflexivity).
    set (ro2 := zset ro1 j vv) in RO', K.
    assert (ROK2 : rook ro2) by (intros k Hk; subst ro2; rewrite zget_zset; destruct (k =? j); [exact Ri| apply ROK'; lia]).
    wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z h ro2 ft _ _ _ _ _ _ me); [st_eq| lia| lia| lia| exact ROK2| exact MONO| exact RO'| exact FTB'| assumption| assumption| assumption| exact K| lia].
    - assert (r = 0)%nat by lia. subst r. cbn [ms_sh_pass] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _) end;
        [st_eq| exact RO'| exact FTB'| assumption| assumption| assumption| exact ROK2].
  Time Qed.


  (* [comment removed for export] *)
  Lemma S0_shell_iter : forall (h h3 : Z) (ro ft : zarr) (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (4 <= h <= 364)%Z -> (h3 = h / 3)%Z -> rook ro ->
    (forall b, 0 <= b < 256 -> 0 <= zget ft (b * 256) <= zget ft ((b + 1) * 256) /\ zget ft ((b + 1) * 256) <= n)%Z ->
    u32arr s0segs m (p + 2600) (zw32 ro 256) -> u32arr s0segs m FT (zw32 ft 65537) -> mem_inv s0segs m ->
    munch [(p + 2600, p + 3624)]%Z me m -> wmono s0segs me m ->
    (forall m' (x6' x7' x28' x29' x30' x31' : word), let ro' := ms_sh_pass (Z.to_nat (256 - h3)) ro ft h3 h3 in
      u32arr s0segs m' (p + 2600) (zw32 ro' 256) -> u32arr s0segs m' FT (zw32 ft 65537) -> mem_inv s0segs m' ->
      munch [(p + 2600, p + 3624)]%Z me m' -> wmono s0segs me m' -> rook ro' ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp (Z_to_bv 64 256) x6' x7' s0 (Z_to_bv 64 FT)
                            (Z_to_bv 64 h) (Z_to_bv 64 767) (Z_to_bv 64 (p + 2600)) (Z_to_bv 64 1431655766) (Z_to_bv 64 2)
                            (Z_to_bv 64 h3) (Z_to_bv 64 (256 - h3)) (Z_to_bv 64 256)
                            s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' x31')
                       F (Z_to_bv 64 0x19a80) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp x5 x6 x7 s0 (Z_to_bv 64 FT)
                          (Z_to_bv 64 h) (Z_to_bv 64 767) (Z_to_bv 64 (p + 2600)) (Z_to_bv 64 1431655766) (Z_to_bv 64 2)
                          x15 x16 x17
                          s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x199ac) fc None m (seg_rom s0segs)).
  Proof.
    intros h h3 ro ft x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 me m Hh Hh3 ROK MONO RO FTB MI MU WM K.
    msenv_open XOK.
    assert (H3 : (1 <= h3 <= 121)%Z) by (subst h3; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    wstep. wstep. rewrite (Z.div_small (h * 1431655766) 9223372036854775808) by lia.
    wstep. rewrite div3_magic by lia. rewrite <- Hh3. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    wstep. wstep. wstep; if_cases Kd; zify_cond_z Kd; [exfalso; lia|].
    wstep. wstep. wstep. wstep.
    enter_with (S0_sh_pass _ _ _ _ (Z.to_nat (256 - h3)) h3 h3 ro ft _ _ _ _ _ _ me m);
      [st_eq| lia| lia| lia| exact ROK| exact MONO| exact RO| exact FTB| exact MI| exact MU| exact WM| exact K| lia].
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_ro_init : forall (x13 x14 x15 x16 x17 : word) (r : nat) (i : Z) (ro bd : zarr) (J : list byte) (me m : word -> option byte),
    (Z.of_nat r = 256 - i)%Z -> (0 <= i < 256)%Z -> (forall k, 0 <= k < i -> zdef ro k = true /\ zget ro k = k)%Z ->
    Z.of_nat (length J) = 1024%Z ->
    u32arr s0segs m (p + 2600) (ovw ro J 256) -> mem_inv s0segs m ->
    munch [(p + 2600, p + 3624)]%Z me m -> wmono s0segs me m ->
    (forall m', let ro' := snd (ms_ro_init r bd ro i) in
      u32arr s0segs m' (p + 2600) (ovw ro' J 256) -> mem_inv s0segs m' ->
      munch [(p + 2600, p + 3624)]%Z me m' -> wmono s0segs me m' -> (forall k, 0 <= k < 256 -> zdef ro' k = true /\ zget ro' k = k)%Z ->
      evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                            (Z_to_bv 64 256) (Z_to_bv 64 (p + 3624)) (Z_to_bv 64 (p + 3624)) x13 x14 x15 x16 x17
                            s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19990) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 p) gp tp t0 t1 t2 s0 (Z_to_bv 64 FT)
                          (Z_to_bv 64 i) (Z_to_bv 64 (p + 2600 + 4 * i)) (Z_to_bv 64 (p + 3624)) x13 x14 x15 x16 x17
                          s2 s3 (Z_to_bv 64 A2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19980) fc None m (seg_rom s0segs)).
  Proof.
    intros x13 x14 x15 x16 x17. induction r as [|r IH]; [intros; lia|].
    intros i ro bd J me m Hr Hi DEF LJ RO MI MU WM K.
    msenv_open XOK.
    pose proof (ovw_length ro J 256 ltac:(lia)) as LR.
    (* [comment removed for export] *)
    pose proof (u32arr_store_ok s0segs m (p + 2600) _ i _ RO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
    wstep. ovw_store RO i i (rewrite unsigned_lit by lia; reflexivity).
    set (ro1 := zset ro i i) in RO.
    assert (DEF1 : forall k, (0 <= k < i + 1)%Z -> zdef ro1 k = true /\ zget ro1 k = k).
    { intros k Hk. subst ro1. rewrite zdef_zset, zget_zset. destruct (Z.eqb_spec k i); [subst; split; reflexivity|]. apply DEF. lia. }
    wstep. wstep.
    rewrite ms_ro_init_S in K. fold ro1 in K.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z ro1 (zset bd i 0) J me); [st_eq| lia| lia| exact DEF1| exact LJ| exact RO| assumption| assumption| assumption|].
      intros m'. cbv zeta. exact (K m').
    - assert (r = 0)%nat by lia. subst r. cbn [ms_ro_init snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
        [st_eq| exact RO| assumption| assumption| assumption| intros k Hk; apply DEF1; lia].
  Time Qed.
End S0MS.

End ACeilS1.
