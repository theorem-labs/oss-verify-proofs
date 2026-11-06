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
  Hypothesis XOK : fsenv_ok X. Hypothesis YOK : afenv_ok X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation HR ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 nb) t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) s3 (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB s7 (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) s10 s11 t3 t4 t5 t6).
  Notation LIM := (fe_nb X + 64)%Z.

  Ltac prep XOK bh k BW :=
    fsenv_open XOK;
    pose proof (zw32_length bh 65537 ltac:(lia)) as LB;
    pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hm;
    pose proof (BW (k / 32)%Z) as Bw.
  Ltac wbound k := assert (Hw : (0 <= k / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).

  (* [comment removed for export] *)
  Lemma A0_scanA : forall (f : nat) (k : Z) (bh : zarr) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a5 a6 a7 s3 s7 s10 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_set_unal f bh k <= LIM)%Z ->
    isset_bh bh (fs_scan_set_unal f bh k) && unaligned_bh (fs_scan_set_unal f bh k) = false -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m -> munch Wl me m -> shzW a0segs Wl me FT (FT + 262144) ->
    (forall (x13 x14 x15 : word), let kA := fs_scan_set_unal f bh k in
      evt a0segs Q (MS (HR ra t1 t2 (Z_to_bv 64 (landv bh kA)) (Z_to_bv 64 (kA - 32)) (Z_to_bv 64 (kA - 1)) x13 x14 x15 a6 a7 s3 s7 s10 (Z_to_bv 64 (kA + 1)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b1c4) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (HR ra t1 t2 a0 a1 a2 (Z_to_bv 64 (k - 32)) (Z_to_bv 64 (k - 1)) a5 a6 a7 s3 s7 s10 (Z_to_bv 64 k) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9b168) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros k bh Wl me m ra t1 t2 a0 a1 a2 a5 a6 a7 s3 s7 s10 t3 t4 t5 t6 Hk HL STOP BW FTB MI MU SHF K; cbv zeta in K.
    - cbn [fs_scan_set_unal] in *. prep XOK bh k BW. wbound k.
      rewrite unaligned_bh_mod, isset_bh_testbit in STOP by lia.
      arun.
      pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. arun.
      if_cases Ka; zify_cond_z Ka; rewrite land31_mod32 in Ka.
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + arun. if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * exfalso. rewrite Kb in STOP. destruct (Z.eqb_spec (k mod 32) 0); [lia| cbn in STOP; discriminate].
        * wstep. enter_with (K _ _ _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_set_unal_S in *. prep XOK bh k BW.
      pose proof (fs_scan_set_unal_ge f bh (k + 1)) as GE.
      rewrite unaligned_bh_mod in HL, STOP, K. try rewrite unaligned_bh_mod in GE.
      destruct (isset_bh bh k) eqn:Ib; destruct (Z.eqb_spec (k mod 32) 0) as [Km|Km]; cbn [negb andb] in HL, STOP, K, GE;
        rewrite isset_bh_testbit in Ib by lia;
        [ wbound k | wbound k | wbound k | wbound k ];
        arun;
        pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
        (wstep; clear RD; arun);
        (if_cases Ka; zify_cond_z Ka; rewrite land31_mod32 in Ka); try (exfalso; lia).
      + (* [comment removed for export] *) enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        arun. if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * enter_with (IH (k + 1)%Z bh Wl me m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact MU| exact SHF| exact K].
        * exfalso. congruence.
      + (* [comment removed for export] *) enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        arun. if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * exfalso. congruence.
        * wstep. enter_with (K _ _ _); [st_eq|..]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_scanB : forall (f : nat) (k : Z) (bh : zarr) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t1 t2 a0 a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_word_ff f bh k <= LIM)%Z ->
    (bh_word bh (fs_scan_word_ff f bh k) =? 4294967295)%Z = false -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m -> munch Wl me m -> shzW a0segs Wl me FT (FT + 262144) ->
    (forall (x10 x13 : word), let kB := fs_scan_word_ff f bh k in
      evt a0segs Q (MS (HR ra t1 t2 x10 (Z_to_bv 64 kB) (Z_to_bv 64 (kB + 31)) x13 a4 a5 a6 a7 (Z_to_bv 64 (kB - 1)) s7 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b224) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (HR ra t1 t2 a0 (Z_to_bv 64 (k - 32)) (Z_to_bv 64 (k - 1)) a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9b1c8) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros k bh Wl me m ra t1 t2 a0 a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6 Hk HL STOP BW FTB MI MU SHF K; cbv zeta in K.
    - cbn [fs_scan_word_ff] in *. prep XOK bh k BW. wbound k. unfold bh_word in STOP. rewrite shiftr5_div in STOP.
      wstep. replace (k - 32 + 32)%Z with k by lia. arun.
      pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. arun.
      if_cases Kb; zify_cond_z Kb.
      + exfalso. apply Z.eqb_neq in STOP. first [lia | apply (proj1 (sx32_allones_iff _ Bw)) in Kb; lia].
      + wstep. enter_with (K _ _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_word_ff_S in *. prep XOK bh k BW.
      pose proof (fs_scan_word_ff_ge f bh (k + 32)) as GE.
      destruct (Z.eqb_spec (bh_word bh k) 4294967295) as [Wd|Wd]; unfold bh_word in Wd; rewrite shiftr5_div in Wd; wbound k;
        (wstep; replace (k - 32 + 32)%Z with k by lia; arun);
        pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
        (wstep; clear RD; arun);
        (if_cases Kb; zify_cond_z Kb).
      + enter_with (IH (k + 32)%Z bh Wl me m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact MU| exact SHF| exact K].
      + exfalso. first [lia | apply Kb; apply (proj2 (sx32_allones_iff _ Bw)); exact Wd].
      + exfalso. first [lia | apply (proj1 (sx32_allones_iff _ Bw)) in Kb; lia].
      + wstep. enter_with (K _ _); [st_eq|..]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_scanC : forall (f : nat) (k : Z) (bh : zarr) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 s11 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_set f bh k <= LIM)%Z ->
    isset_bh bh (fs_scan_set f bh k) = false -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m -> munch Wl me m -> shzW a0segs Wl me FT (FT + 262144) ->
    (forall (x11 : word), let kC := fs_scan_set f bh k in
      evt a0segs Q (MS (HR ra t1 t2 (Z_to_bv 64 0) x11 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 kC) s7 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b254) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (HR ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (k - 1)) s7 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9b224) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros k bh Wl me m ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s10 s11 t3 t4 t5 t6 Hk HL STOP BW FTB MI MU SHF K; cbv zeta in K.
    - cbn [fs_scan_set] in *. prep XOK bh k BW. wbound k. rewrite isset_bh_testbit in STOP by lia.
      wstep. try replace (k - 1 + 1)%Z with k by lia. arun.
      pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. do 2 wstep. rewrite (isset_test_val (zget bh (k / 32)) k), STOP by lia. cbn [Z.b2z].
      wstep; if_cases Kb; zify_cond_z Kb; [exfalso; lia|].
      enter_with (K _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_set_S in *. prep XOK bh k BW.
      pose proof (fs_scan_set_ge f bh (k + 1)) as GE.
      destruct (isset_bh bh k) eqn:Ib; rewrite isset_bh_testbit in Ib by lia; wbound k;
        (wstep; try replace (k - 1 + 1)%Z with k by lia; arun);
        pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
        (wstep; clear RD; do 2 wstep; rewrite (isset_test_val (zget bh (k / 32)) k), Ib by lia; cbn [Z.b2z]);
        (wstep; if_cases Kb; zify_cond_z Kb); try (exfalso; lia).
      + enter_with (IH (k + 1)%Z bh Wl me m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact MU| exact SHF| exact K].
      + enter_with (K _); [st_eq|..]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_scanD : forall (f : nat) (k : Z) (bh : zarr) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a5 a6 a7 s3 s7 s10 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_clr_unal f bh k <= LIM)%Z ->
    negb (isset_bh bh (fs_scan_clr_unal f bh k)) && unaligned_bh (fs_scan_clr_unal f bh k) = false -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m -> munch Wl me m -> shzW a0segs Wl me FT (FT + 262144) ->
    (forall (x13 x14 x15 : word), let kD := fs_scan_clr_unal f bh k in
      evt a0segs Q (MS (HR ra t1 t2 (Z_to_bv 64 (landv bh kD)) (Z_to_bv 64 (kD - 32)) (Z_to_bv 64 (kD - 1)) x13 x14 x15 a6 a7 s3 s7 s10 (Z_to_bv 64 (kD + 1)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b2c0) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (HR ra t1 t2 a0 a1 a2 (Z_to_bv 64 (k - 32)) (Z_to_bv 64 (k - 1)) a5 a6 a7 s3 s7 s10 (Z_to_bv 64 k) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9b264) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros k bh Wl me m ra t1 t2 a0 a1 a2 a5 a6 a7 s3 s7 s10 t3 t4 t5 t6 Hk HL STOP BW FTB MI MU SHF K; cbv zeta in K.
    - cbn [fs_scan_clr_unal] in *. prep XOK bh k BW. wbound k.
      rewrite unaligned_bh_mod, isset_bh_testbit in STOP by lia.
      arun.
      pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. arun.
      if_cases Ka; zify_cond_z Ka; rewrite land31_mod32 in Ka.
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + arun. if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * exfalso. rewrite Kb in STOP. destruct (Z.eqb_spec (k mod 32) 0); [lia| cbn in STOP; discriminate].
        * wstep. enter_with (K _ _ _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_clr_unal_S in *. prep XOK bh k BW.
      pose proof (fs_scan_clr_unal_ge f bh (k + 1)) as GE.
      rewrite unaligned_bh_mod in HL, STOP, K. try rewrite unaligned_bh_mod in GE.
      destruct (isset_bh bh k) eqn:Ib; destruct (Z.eqb_spec (k mod 32) 0) as [Km|Km]; cbn [negb andb] in HL, STOP, K, GE;
        rewrite isset_bh_testbit in Ib by lia;
        [ wbound k | wbound k | wbound k | wbound k ];
        arun;
        pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
        (wstep; clear RD; arun);
        (if_cases Ka; zify_cond_z Ka; rewrite land31_mod32 in Ka); try (exfalso; lia).
      + (* [comment removed for export] *) enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        arun. if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * exfalso. congruence.
        * wstep. enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *) enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        arun. if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * enter_with (IH (k + 1)%Z bh Wl me m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact MU| exact SHF| exact K].
        * exfalso. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_scanE : forall (f : nat) (k : Z) (bh : zarr) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t1 t2 a0 a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_word_00 f bh k <= LIM)%Z ->
    (bh_word bh (fs_scan_word_00 f bh k) =? 0)%Z = false -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m -> munch Wl me m -> shzW a0segs Wl me FT (FT + 262144) ->
    (forall (x10 x13 : word), let kE := fs_scan_word_00 f bh k in
      evt a0segs Q (MS (HR ra t1 t2 x10 (Z_to_bv 64 kE) (Z_to_bv 64 (kE + 31)) x13 a4 a5 a6 a7 s3 s7 s10 (Z_to_bv 64 (kE - 1)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9c07c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (HR ra t1 t2 a0 (Z_to_bv 64 (k - 32)) (Z_to_bv 64 (k - 1)) a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9c04c) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros k bh Wl me m ra t1 t2 a0 a3 a4 a5 a6 a7 s3 s7 s10 s11 t3 t4 t5 t6 Hk HL STOP BW FTB MI MU SHF K; cbv zeta in K.
    - cbn [fs_scan_word_00] in *. prep XOK bh k BW. wbound k. unfold bh_word in STOP. rewrite shiftr5_div in STOP.
      wstep. replace (k - 32 + 32)%Z with k by lia. arun.
      pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. arun.
      if_cases Kb; zify_cond_z Kb.
      + exfalso. apply Z.eqb_neq in STOP. first [lia | apply (proj1 (sx32_zero_iff _ Bw)) in Kb; lia].
      + enter_with (K _ _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_word_00_S in *. prep XOK bh k BW.
      pose proof (fs_scan_word_00_ge f bh (k + 32)) as GE.
      destruct (Z.eqb_spec (bh_word bh k) 0) as [Wd|Wd]; unfold bh_word in Wd; rewrite shiftr5_div in Wd; wbound k;
        (wstep; replace (k - 32 + 32)%Z with k by lia; arun);
        pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
        (wstep; clear RD; arun);
        (if_cases Kb; zify_cond_z Kb).
      + enter_with (IH (k + 32)%Z bh Wl me m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact MU| exact SHF| exact K].
      + exfalso. first [lia | apply Kb; apply (proj2 (sx32_zero_iff _ Bw)); exact Wd].
      + exfalso. first [lia | apply (proj1 (sx32_zero_iff _ Bw)) in Kb; lia].
      + enter_with (K _ _); [st_eq|..]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_scanF : forall (f : nat) (k : Z) (bh : zarr) (Wl : list (Z * Z)) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s10 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_clr f bh k <= LIM)%Z ->
    isset_bh bh (fs_scan_clr f bh k) = true -> bh_w32 bh ->
    u32arr a0segs m FT (zw32 bh 65537) -> mem_inv a0segs m -> munch Wl me m -> shzW a0segs Wl me FT (FT + 262144) ->
    (forall (x11 : word), let kF := fs_scan_clr f bh k in
      evt a0segs Q (MS (HR ra t1 t2 (Z_to_bv 64 1) x11 a2 a3 a4 a5 a6 a7 s3 s7 s10 (Z_to_bv 64 kF) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9b2c8) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (HR ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s10 (Z_to_bv 64 (k - 1)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9c07c) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH]; intros k bh Wl me m ra t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s10 t3 t4 t5 t6 Hk HL STOP BW FTB MI MU SHF K; cbv zeta in K.
    - cbn [fs_scan_clr] in *. prep XOK bh k BW. wbound k. rewrite isset_bh_testbit in STOP by lia.
      wstep. try replace (k - 1 + 1)%Z with k by lia. arun.
      pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. do 2 wstep. rewrite (isset_test_val (zget bh (k / 32)) k), STOP by lia. cbn [Z.b2z].
      wstep; if_cases Kb; zify_cond_z Kb; [exfalso; lia|].
      wstep. enter_with (K _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_clr_S in *. prep XOK bh k BW.
      pose proof (fs_scan_clr_ge f bh (k + 1)) as GE.
      destruct (isset_bh bh k) eqn:Ib; rewrite isset_bh_testbit in Ib by lia; cbn [negb] in HL, STOP, K, GE; wbound k;
        (wstep; try replace (k - 1 + 1)%Z with k by lia; arun);
        pose proof (zw32_read a0segs m FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
        (wstep; clear RD; do 2 wstep; rewrite (isset_test_val (zget bh (k / 32)) k), Ib by lia; cbn [Z.b2z]);
        (wstep; if_cases Kb; zify_cond_z Kb); try (exfalso; lia).
      + wstep. enter_with (K _); [st_eq|..]; reflexivity.
      + enter_with (IH (k + 1)%Z bh Wl me m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact MU| exact SHF| exact K].
  Qed.
End A0FS.

End ACeilS1.
