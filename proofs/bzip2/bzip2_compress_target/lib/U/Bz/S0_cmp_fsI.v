(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCFactsFs BzCFactsFs2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzCSortF BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
Module S0_cmp_fsC.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop. Variable Hh : Z.
  Hypothesis XOK : fsenv_ok X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  (* [comment removed for export] *)
  Notation HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) s5 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).
  Notation LIM := (fe_nb X + 64)%Z.

  Ltac prep XOK bh k BW :=
    fsenv_open XOK;
    pose proof (zw32_length bh 65537 ltac:(lia)) as LB;
    pose proof (Z.mod_pos_bound k 32 ltac:(lia)) as Hm;
    pose proof (BW (k / 32)%Z) as Bw.
  Ltac wbound k := assert (Hw : (0 <= k / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  Ltac m32 := rewrite ?land31_mod32; rewrite ?Z.mod_mod by lia.
  Ltac rdw bh k FTB :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read s0segs mm FT bh 65537 (k / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac wbound2 k := assert (Hw2 : (0 <= k / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).

  (* [comment removed for export] *)
  Lemma S0_scanA : forall (f : nat) (k : Z) (bh : zarr) (m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_set_unal f bh k <= LIM)%Z ->
    isset_bh bh (fs_scan_set_unal f bh k) && unaligned_bh (fs_scan_set_unal f bh k) = false -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    (forall (x13 x14 x21 : word), let kA := fs_scan_set_unal f bh k in
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 kA) (Z_to_bv 64 (kA / 32)) (Z_to_bv 64 (landv' bh kA)) x13 x14 a5 a6 a7 x21 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x227f0) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 k) s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x2279c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros k bh m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Hk HL STOP BW FTB MI K; cbv zeta in K.
    - cbn [fs_scan_set_unal] in *. prep XOK bh k BW. wbound k.
      rewrite unaligned_bh_mod, isset_bh_testbit in STOP by lia.
      urun_to 0x227cc%Z. rdw bh k FTB. urun_to 0x227dc%Z. m32.
      wstep; if_cases Ka; zify_cond_z Ka.
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + wstep; if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * enter_with (K _ _ _); [st_eq|..]; reflexivity.
        * exfalso. rewrite Kb in STOP. destruct (Z.eqb_spec (k mod 32) 0); [lia| cbn in STOP; discriminate].
    - rewrite fs_scan_set_unal_S in *. prep XOK bh k BW.
      pose proof (fs_scan_set_unal_ge f bh (k + 1)) as GE.
      rewrite unaligned_bh_mod in HL, STOP, K. try rewrite unaligned_bh_mod in GE.
      destruct (isset_bh bh k) eqn:Ib; destruct (Z.eqb_spec (k mod 32) 0) as [Km|Km]; cbn [negb andb] in HL, STOP, K, GE;
        rewrite isset_bh_testbit in Ib by lia;
        [ wbound k | wbound k | wbound k | wbound k ];
        (urun_to 0x227cc%Z; rdw bh k FTB; urun_to 0x227dc%Z; m32);
        (wstep; if_cases Ka; zify_cond_z Ka); try (exfalso; lia).
      + (* [comment removed for export] *) enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        wstep; if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * exfalso. congruence.
        * urun_to 0x2279c%Z.
          enter_with (IH (k + 1)%Z bh m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact K].
      + (* [comment removed for export] *) enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        wstep; if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * enter_with (K _ _ _); [st_eq|..]; reflexivity.
        * exfalso. congruence.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_scanB : forall (f : nat) (k : Z) (bh : zarr) (m : word -> option byte)
      (ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_word_ff f bh k <= LIM)%Z ->
    (bh_word bh (fs_scan_word_ff f bh k) =? 4294967295)%Z = false -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    (forall (x11 x12 x13 : word), let kB := fs_scan_word_ff f bh k in
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 kB) x11 x12 x13 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22838) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k) (Z_to_bv 64 (k / 32)) a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x227f4) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros k bh m ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 Hk HL STOP BW FTB MI K; cbv zeta in K.
    - cbn [fs_scan_word_ff] in *. prep XOK bh k BW. wbound k. unfold bh_word in STOP. rewrite shiftr5_div in STOP.
      urun_to 0x227fc%Z. rdw bh k FTB.
      wstep; if_cases Kb; zify_cond_z Kb.
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + exfalso. apply Z.eqb_neq in STOP. first [lia | apply (proj1 (sx32_allones_iff _ Bw)) in Kb; lia].
    - rewrite fs_scan_word_ff_S in *. prep XOK bh k BW.
      pose proof (fs_scan_word_ff_ge f bh (k + 32)) as GE.
      destruct (Z.eqb_spec (bh_word bh k) 4294967295) as [Wd|Wd]; unfold bh_word in Wd; rewrite shiftr5_div in Wd; wbound k;
        (urun_to 0x227fc%Z; rdw bh k FTB);
        (wstep; if_cases Kb; zify_cond_z Kb).
      + exfalso. first [lia | apply Kb; apply (proj2 (sx32_allones_iff _ Bw)); exact Wd].
      + wbound2 (k + 32)%Z. urun_to 0x227f4%Z.
        enter_with (IH (k + 32)%Z bh m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact K].
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + exfalso. first [lia | apply (proj1 (sx32_allones_iff _ Bw)) in Kb; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_scanC : forall (f : nat) (k : Z) (bh : zarr) (m : word -> option byte)
      (ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_set f bh k <= LIM)%Z ->
    isset_bh bh (fs_scan_set f bh k) = false -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    (forall (x11 x12 x13 : word), let kC := fs_scan_set f bh k in
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 kC) x11 x12 x13 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x228a8) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k) (Z_to_bv 64 (k / 32)) a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x2285c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros k bh m ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 Hk HL STOP BW FTB MI K; cbv zeta in K.
    - cbn [fs_scan_set] in *. prep XOK bh k BW. wbound k. rewrite isset_bh_testbit in STOP by lia.
      urun_to 0x22864%Z. rdw bh k FTB.
      urun_to 0x22870%Z. m32. rewrite (isset_test_val (zget bh (k / 32)) k), STOP by lia. cbn [Z.b2z].
      wstep; if_cases Kb; zify_cond_z Kb; [| exfalso; lia].
      enter_with (K _ _ _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_set_S in *. prep XOK bh k BW.
      pose proof (fs_scan_set_ge f bh (k + 1)) as GE.
      destruct (isset_bh bh k) eqn:Ib; rewrite isset_bh_testbit in Ib by lia; wbound k;
        (urun_to 0x22864%Z; rdw bh k FTB);
        (urun_to 0x22870%Z; m32; rewrite (isset_test_val (zget bh (k / 32)) k), Ib by lia; cbn [Z.b2z]);
        (wstep; if_cases Kb; zify_cond_z Kb); try (exfalso; lia).
      + wbound2 (k + 1)%Z. urun_to 0x2285c%Z.
        enter_with (IH (k + 1)%Z bh m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact K].
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_scanD : forall (f : nat) (k : Z) (bh : zarr) (m : word -> option byte)
      (ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_clr_unal f bh k <= LIM)%Z ->
    negb (isset_bh bh (fs_scan_clr_unal f bh k)) && unaligned_bh (fs_scan_clr_unal f bh k) = false -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    (forall (x12 x13 : word), let kD := fs_scan_clr_unal f bh k in
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 kD) (Z_to_bv 64 (landv' bh kD)) x12 x13 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x2292c) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k) (Z_to_bv 64 (k / 32)) a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x228d8) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros k bh m ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 Hk HL STOP BW FTB MI K; cbv zeta in K.
    - cbn [fs_scan_clr_unal] in *. prep XOK bh k BW. wbound k.
      rewrite unaligned_bh_mod, isset_bh_testbit in STOP by lia.
      urun_to 0x228e0%Z. rdw bh k FTB. urun_to 0x228f0%Z. m32.
      wstep; if_cases Ka; zify_cond_z Ka.
      + enter_with (K _ _); [st_eq|..]; reflexivity.
      + wstep; if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * enter_with (K _ _); [st_eq|..]; reflexivity.
        * exfalso. rewrite Kb in STOP. destruct (Z.eqb_spec (k mod 32) 0); [lia| cbn in STOP; discriminate].
    - rewrite fs_scan_clr_unal_S in *. prep XOK bh k BW.
      pose proof (fs_scan_clr_unal_ge f bh (k + 1)) as GE.
      rewrite unaligned_bh_mod in HL, STOP, K. try rewrite unaligned_bh_mod in GE.
      destruct (isset_bh bh k) eqn:Ib; destruct (Z.eqb_spec (k mod 32) 0) as [Km|Km]; cbn [negb andb] in HL, STOP, K, GE;
        rewrite isset_bh_testbit in Ib by lia;
        [ wbound k | wbound k | wbound k | wbound k ];
        (urun_to 0x228e0%Z; rdw bh k FTB; urun_to 0x228f0%Z; m32);
        (wstep; if_cases Ka; zify_cond_z Ka); try (exfalso; lia).
      + (* [comment removed for export] *) enter_with (K _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        wstep; if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * enter_with (K _ _); [st_eq|..]; reflexivity.
        * exfalso. congruence.
      + (* [comment removed for export] *) enter_with (K _ _); [st_eq|..]; reflexivity.
      + (* [comment removed for export] *)
        wstep; if_cases Kb; zify_cond_z Kb; bit_of_land Kb.
        * exfalso. congruence.
        * wbound2 (k + 1)%Z. urun_to 0x228d8%Z.
          enter_with (IH (k + 1)%Z bh m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_scanE : forall (f : nat) (k : Z) (bh : zarr) (m : word -> option byte)
      (ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_word_00 f bh k <= LIM)%Z ->
    (bh_word bh (fs_scan_word_00 f bh k) =? 0)%Z = false -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    (forall (x11 x12 x13 : word), let kE := fs_scan_word_00 f bh k in
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 kE) x11 x12 x13 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x23310) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k) (Z_to_bv 64 (k / 32)) a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x232cc) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros k bh m ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 Hk HL STOP BW FTB MI K; cbv zeta in K.
    - cbn [fs_scan_word_00] in *. prep XOK bh k BW. wbound k. unfold bh_word in STOP. rewrite shiftr5_div in STOP.
      urun_to 0x232d4%Z. rdw bh k FTB.
      wstep; if_cases Kb; zify_cond_z Kb.
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + exfalso. apply Z.eqb_neq in STOP. first [lia | apply (proj1 (sx32_zero_iff _ Bw)) in Kb; lia].
    - rewrite fs_scan_word_00_S in *. prep XOK bh k BW.
      pose proof (fs_scan_word_00_ge f bh (k + 32)) as GE.
      destruct (Z.eqb_spec (bh_word bh k) 0) as [Wd|Wd]; unfold bh_word in Wd; rewrite shiftr5_div in Wd; wbound k;
        (urun_to 0x232d4%Z; rdw bh k FTB);
        (wstep; if_cases Kb; zify_cond_z Kb).
      + exfalso. first [lia | apply Kb; apply (proj2 (sx32_zero_iff _ Bw)); exact Wd].
      + wbound2 (k + 32)%Z. urun_to 0x232cc%Z.
        enter_with (IH (k + 32)%Z bh m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact K].
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + exfalso. first [lia | apply (proj1 (sx32_zero_iff _ Bw)) in Kb; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_scanF : forall (f : nat) (k : Z) (bh : zarr) (m : word -> option byte)
      (ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word),
    (0 <= k)%Z -> (fs_scan_clr f bh k <= LIM)%Z ->
    isset_bh bh (fs_scan_clr f bh k) = true -> bh_w32 bh ->
    u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    (forall (x11 x12 x13 : word), let kF := fs_scan_clr f bh k in
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 kF) x11 x12 x13 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x22930) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k) (Z_to_bv 64 (k / 32)) a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x23334) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros k bh m ra t0 t2 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 Hk HL STOP BW FTB MI K; cbv zeta in K.
    - cbn [fs_scan_clr] in *. prep XOK bh k BW. wbound k. rewrite isset_bh_testbit in STOP by lia.
      urun_to 0x2333c%Z. rdw bh k FTB.
      urun_to 0x23348%Z. m32. rewrite (isset_test_val (zget bh (k / 32)) k), STOP by lia. cbn [Z.b2z].
      wstep; if_cases Kb; zify_cond_z Kb; [| exfalso; lia].
      enter_with (K _ _ _); [st_eq|..]; reflexivity.
    - rewrite fs_scan_clr_S in *. prep XOK bh k BW.
      pose proof (fs_scan_clr_ge f bh (k + 1)) as GE.
      destruct (isset_bh bh k) eqn:Ib; rewrite isset_bh_testbit in Ib by lia; cbn [negb] in HL, STOP, K, GE; wbound k;
        (urun_to 0x2333c%Z; rdw bh k FTB);
        (urun_to 0x23348%Z; m32; rewrite (isset_test_val (zget bh (k / 32)) k), Ib by lia; cbn [Z.b2z]);
        (wstep; if_cases Kb; zify_cond_z Kb); try (exfalso; lia).
      + enter_with (K _ _ _); [st_eq|..]; reflexivity.
      + wbound2 (k + 1)%Z. urun_to 0x23334%Z.
        enter_with (IH (k + 1)%Z bh m); [st_eq| lia| lia| exact STOP| exact BW| exact FTB| exact MI| exact K].
  Qed.
End S0FS.

End ACeilS1.
End S0_cmp_fsC.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsD S0_cmp_fsF S0_cmp_fsG.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_fsD.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_fsH.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsD.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop. Variables Hh l1 r1 : Z.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  (* [comment removed for export] *)
  Notation HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (r1 - 1)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).

  Lemma S0_headers : forall (n : nat) (i cc : Z) (fm ec bh : zarr) (me m : word -> option byte) (ra t0 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = r1)%Z -> (1 <= n)%nat -> (0 <= i)%Z -> (r1 <= nb)%Z -> (cc = -1 \/ 0 <= cc < nb)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec -> bh_w32 bh ->
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m A2 (zb8 ec ARR2_SIZE) -> u32arr s0segs m FT (zw32 bh 65537) -> mem_inv s0segs m ->
    munch [(FT, FT + 262148)]%Z me m -> wmono s0segs me m ->
    (forall m' (x10 x11 x12 x13 x14 x15 x16 x24 : word), let bh' := fs_headers n bh ec fm i cc in
      u8arr s0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 ec ARR2_SIZE) -> u32arr s0segs m' FT (zw32 bh' 65537) -> mem_inv s0segs m' ->
      munch [(FT, FT + 262148)]%Z me m' -> wmono s0segs me m' -> bh_w32 bh' ->
      evt s0segs Q (MS (HR ra t0 t2 x10 x11 x12 x13 x14 x15 x16 a7 x24 t3 t4 t5 t6) F (Z_to_bv 64 0x22798) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 cc) a4 a5 a6 a7 (Z_to_bv 64 i) t3 t4 t5 t6) F (Z_to_bv 64 0x233a4) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; intros i cc fm ec bh me m ra t0 t2 a4 a5 a6 a7 t3 t4 t5 t6 Hi Hn Hi0 Hr Hcc FMR ECR FMOK' ECOK' BW AR1 AR2 FTB MI MU WM K; cbv zeta in K; [lia|].
    fsenv_open XOK. pose proof XSEP as SP. unfold fsenv_sep, apartv in SP. cps_destruct SP as (AP12 & AP1F & AP2F). bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    pose proof (proj2 FMR i ltac:(lia)) as Fi. pose proof (ECR (rd32 fm i) ltac:(lia)) as Ei.
    (* [comment removed for export] *)
    urun_to 0x233c4%Z. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 s0segs mm A1 fm ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) FMOK' ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (zx32_of_Z (rd32 fm i)) by lia.
    urun_to 0x233f0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 s0segs mm A2 ec ARR2_SIZE (rd32 fm i) _ AR2 ltac:(lia) ltac:(lia) ECOK' ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (rd32 ec (rd32 fm i))) by lia.
    (* [comment removed for export] *)
    assert (TAIL : forall m1 bh1 cc1 (x14 x15 x16 : word),
      fs_headers n bh1 ec fm (i + 1) cc1 = fs_headers (S n) bh ec fm i cc -> (cc1 = -1 \/ 0 <= cc1 < nb)%Z -> bh_w32 bh1 ->
      u8arr s0segs m1 A1 (zb8 fm ARR1_SIZE) -> u8arr s0segs m1 A2 (zb8 ec ARR2_SIZE) -> u32arr s0segs m1 FT (zw32 bh1 65537) -> mem_inv s0segs m1 ->
      munch [(FT, FT + 262148)]%Z me m1 -> wmono s0segs me m1 ->
      evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 cc1) x14 x15 x16 a7 (Z_to_bv 64 i) t3 t4 t5 t6) F (Z_to_bv 64 0x23438) fc None m1 (seg_rom s0segs))).
    { intros m1 bh1 cc1 x14 x15 x16 E Hcc1 BW1 AR1' AR2' FTB1 MI1 MU1 WM1.
      (* [comment removed for export] *)
      urun_to 0x23450%Z. wstep; if_cases Ke; zify_cond_z Ke.
      - (* [comment removed for export] *)
        assert (n = 0)%nat by lia. subst n. cbn [fs_headers] in E, K. rewrite <- E in K.
        enter_with (K m1 _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact AR2'| exact FTB1| exact MI1| exact MU1| exact WM1| exact BW1].
      - (* [comment removed for export] *)
        wstep.
        enter_with (IH (i + 1)%Z cc1 fm ec bh1 me m1); [st_eq| lia| lia| lia| lia| exact Hcc1| exact FMR| exact ECR| exact FMOK'| exact ECOK'| exact BW1| exact AR1'| exact AR2'| exact FTB1| exact MI1| exact MU1| exact WM1|].
        intros m' y10 y11 y12 y13 y14 y15 y16 y24. cbv zeta. rewrite E. exact (K m' y10 y11 y12 y13 y14 y15 y16 y24). }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ecc : cc = rd32 ec (rd32 fm i)) by (destruct Hcc as [Hcc|Hcc]; [subst cc; exfalso; clear -Kc Ei; mlia| lia]).
      eapply (TAIL m bh cc); [| exact Hcc| exact BW| exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM].
      rewrite fs_headers_S. cbv zeta. replace (cc =? rd32 ec (rd32 fm i))%Z with true by (symmetry; apply Z.eqb_eq; exact Ecc). reflexivity.
    - (* [comment removed for export] *)
      assert (Ncc : cc <> rd32 ec (rd32 fm i)) by (destruct Hcc as [Hcc|Hcc]; [subst cc; lia| lia]).
      assert (Hw : (0 <= i / 32 <= 28125)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      pose proof (BW (i / 32)%Z) as Bw.
      (* [comment removed for export] *)
      urun_to 0x23424%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (zw32_read s0segs mm FT bh 65537 (i / 32) _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
      wstep. clear RD. urun_to 0x23430%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm FT _ (i / 32) _ FTB ltac:(rewrite zw32_length_nat; lia) eq_refl) as SO end.
      wstep. zw32_store FTB (i / 32)%Z (Z.lor (zget bh (i / 32)) (Z.shiftl 1 (Z.land i 31)))%Z (apply set_bh_store_b).
      (* [comment removed for export] *)
      wstep.
      eapply (TAIL _ (zset bh (i / 32) (Z.lor (zget bh (i / 32)) (Z.shiftl 1 (Z.land i 31)))) (rd32 ec (rd32 fm i)));
        [| right; lia| | exact AR1| exact AR2| exact FTB| exact MI| exact MU| exact WM].
      + rewrite fs_headers_S. cbv zeta. replace (cc =? rd32 ec (rd32 fm i))%Z with false by (symmetry; apply Z.eqb_neq; exact Ncc). cbn [negb].
        unfold set_bh, bh_word. rewrite shiftr5_div. reflexivity.
      + pose proof (set_bh_w32 bh i BW) as Y. unfold set_bh, bh_word in Y. rewrite shiftr5_div in Y. exact Y.
  Qed.
End S0FS.

End ACeilS1.
End S0_cmp_fsH.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsFs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsI.S0_cmp_fsC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsG OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_fsI.S0_cmp_fsH.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.UKit.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma landv_range : forall bh k, (0 <= landv bh k < 18446744073709551616)%Z.
Proof.
  intros bh k. unfold landv.
  set (a := (bv_swrap 32 (Z.shiftl 1 (k mod 32)) mod 18446744073709551616)%Z).
  set (b := bv_unsigned (sx32 (Z_to_bv 64 (zget bh (k / 32))))).
  assert (Ha : (0 <= a < 18446744073709551616)%Z) by (subst a; apply Z.mod_pos_bound; lia).
  assert (Hb : (0 <= b)%Z) by (subst b; apply bv_unsigned_in_range).
  pose proof (OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.land_lt_pow2 a b 64 ltac:(change (2^64)%Z with 18446744073709551616%Z; lia) Hb) as H.
  change (2^64)%Z with 18446744073709551616%Z in H. exact H.
Qed.
Lemma landv_zero_isset : forall bh k, bh_w32 bh -> (0 <= k)%Z -> landv bh k = 0%Z -> isset_bh bh k = false.
Proof. intros bh k BW Hk E. pose proof (landv_isset bh k BW Hk) as V. rewrite E in V. cbn in V. destruct (isset_bh bh k); [discriminate| reflexivity]. Qed.
Lemma landv_nz_isset : forall bh k, bh_w32 bh -> (0 <= k)%Z -> landv bh k <> 0%Z -> isset_bh bh k = true.
Proof. intros bh k BW Hk E. pose proof (landv_isset bh k BW Hk) as V. destruct (isset_bh bh k); [reflexivity|]. cbn in V. apply Z.eqb_eq in V. lia. Qed.
Lemma landv'_landv : forall bh k, landv' bh k = landv bh k.
Proof. intros bh k. unfold landv, landv'. apply Z.land_comm. Qed.

Section S0FS.
  Variable X : fsenv. Variable Q : machine_state -> Prop. Variable Hh : Z.
  Variables (str sv : word) (ec : zarr) (Jlo Jhi : list byte).
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X.
  Notation usp := (bv_unsigned (fe_sp X)). Notation p := (bv_unsigned (fe_sp X) - 3056)%Z.
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Hypothesis ECR : ec_range ec nb. Hypothesis ECOK' : zbok ec.
  Hypothesis LJlo : Z.of_nat (length Jlo) = 400%Z. Hypothesis LJhi : Z.of_nat (length Jhi) = 400%Z.
  (* [comment removed for export] *)
  Notation HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 p) gp tp t0 (Z_to_bv 64 Hh) t2 (Z_to_bv 64 nb) (Z_to_bv 64 A2) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 A1) (Z_to_bv 64 1) (Z_to_bv 64 FT) s5 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) s8 (Z_to_bv 64 (18446744073709551615 - A2)) (Z_to_bv 64 1) (Z_to_bv 64 1) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation Wb := [(fe_A1 X, fe_A1 X + ARR1_SIZE); (fe_FT X, fe_FT X + 262148); (bv_unsigned (fe_sp X) - 3056 + 40, bv_unsigned (fe_sp X) - 3056 + 72);
                  (bv_unsigned (fe_sp X) - 3056 + 2152, bv_unsigned (fe_sp X) - 3056 + 2952)]%Z.
  (* [comment removed for export] *)
  Definition bmem (fm bh slo shi : zarr) (hc nd rr tv : Z) (m : word -> option byte) : Prop :=
    u8arr s0segs m A1 (zb8 fm ARR1_SIZE) /\ u8arr s0segs m A2 (zb8 ec ARR2_SIZE) /\ u32arr s0segs m FT (zw32 bh 65537) /\
    rw_cells s0segs m (p + 8) (SCq X hc str sv nd rr tv) /\
    u32arr s0segs m (p + 2152) (ovw shi Jhi 100) /\ u32arr s0segs m (p + 2552) (ovw slo Jlo 100) /\ mem_inv s0segs m.
  (* [comment removed for export] *)
  Definition binv (fm bh : zarr) (r nnd : Z) : Prop := fm_range fm nb /\ zbok fm /\ bh_w32 bh /\ (0 <= nnd <= r + 1 /\ nnd <= nb)%Z.

  Ltac bmem_i AR1 AR2 FTB SC SHI SLO MI :=
    split; [exact AR1| split; [exact AR2| split; [exact FTB| split; [exact SC| split; [exact SHI| split; [exact SLO| exact MI]]]]]].
  (* [comment removed for export] *)
  Ltac store_addr E' :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?ad ?bs) _) =>
      replace (write_to_mem m0 ad bs) with (write_to_mem m0 (wa E') bs) by (f_equal; unfold wa; f_equal; lia) end.
  Ltac open XOK XSEP :=
    fsenv_open XOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & ?AP1F & ?AP2F).

  (* [comment removed for export] *)
  Lemma S0_bk2 : forall (fm bh slo shi : zarr) (r0 nnd hc nd rr tv k1 k2 : Z) (me m : word -> option byte)
      (ra t0 t2 a1 a2 a3 a4 a5 a6 s5 t3 t4 t5 t6 : word),
    let s := FBS fm ec bh slo shi r0 nnd false in
    k1 = bk1 nb bh (r0 + 1) -> k2 = bk2 nb bh k1 -> (nb <=? k1 - 1)%Z = false ->
    (0 <= r0 + 1)%Z -> (r0 + 2 <= k1 <= k2)%Z -> (k2 <= nb + 65)%Z ->
    bucket_ok nb s -> binv fm bh r0 nnd -> bmem fm bh slo shi hc nd rr tv m -> munch Wb me m -> wmono s0segs me m ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x24 x28 x29 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = false -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) (Z_to_bv 64 (fb_r s')) x24 x28 x29 x30 x31) F (Z_to_bv 64 0x22798) fc None m' (seg_rom s0segs))) ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x21 x24 x28 x29 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = true -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) x21 x24 x28 x29 x30 x31) F (Z_to_bv 64 0x23458) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k2) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nnd) s5 (Z_to_bv 64 (k1 - 1)) t3 t4 t5 t6) F (Z_to_bv 64 0x22930) fc None m (seg_rom s0segs)).
  Proof.
    intros fm bh slo shi r0 nnd hc nd rr tv k1 k2 me m ra t0 t2 a1 a2 a3 a4 a5 a6 s5 t3 t4 t5 t6 s Hk1 Hk2 C1 Hr0 Hk12 Hk2n BOK BI BM MU WM KC KB.
    cbv zeta in KC, KB. subst s. rewrite fs_bucket_iter_unfold in KC, KB. cbv zeta in KC, KB. rewrite <- Hk1, <- Hk2, C1 in KC, KB.
    cps_destruct BI as (FMR & FMOK' & BW & Hnnd). cps_destruct BM as (AR1 & AR2 & FTB & SC & SHI & SLO & MI).
    open XOK XSEP. bz_params.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length bh 65537 ltac:(lia)) as LB.
    pose proof (ovw_length shi Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length slo Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    urun_to 0x22938%Z. try rewrite (sx32_of_Z (k2 - 1)) by lia. try rewrite (sx32_of_Z (k2 + -1)) by lia.
    wstep; if_cases Kr; zify_cond_z Kr.
    - (* [comment removed for export] *)
      replace (nb <=? k2 - 1)%Z with true in KB by (symmetry; apply Z.leb_le; lia).
      enter_with (KB m hc nd rr tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
        [st_eq| reflexivity| reflexivity| split; [exact FMR| split; [exact FMOK'| split; [exact BW| lia]]]| bmem_i AR1 AR2 FTB SC SHI SLO MI| exact MU| exact WM].
    - replace (nb <=? k2 - 1)%Z with false in KC by (symmetry; apply Z.leb_gt; lia). clear KB.
      (* [comment removed for export] *)
      wstep; if_cases Klr; zify_cond_z Klr.
      + (* [comment removed for export] *)
        replace (k1 - 1 <? k2 - 1)%Z with false in KC by (symmetry; apply Z.ltb_ge; lia).
        enter_with (KC m hc nd rr tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
          [st_eq| reflexivity| reflexivity| split; [exact FMR| split; [exact FMOK'| split; [exact BW| lia]]]| bmem_i AR1 AR2 FTB SC SHI SLO MI| exact MU| exact WM].
      + (* [comment removed for export] *)
        replace (k1 - 1 <? k2 - 1)%Z with true in KC by (symmetry; apply Z.ltb_lt; lia).
        destruct BOK as [_ QOK]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd] in QOK. rewrite <- Hk1, <- Hk2 in QOK.
        specialize (QOK ltac:(lia) ltac:(lia) ltac:(lia)). destruct QOK as [QF QFIN].
        unfold SCq in SC.
        (* [comment removed for export] *)
        urun_to 0x22968%Z. wstep. wstep. wstep. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.
        (* [comment removed for export] *)
        wstep. wstep.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok s0segs mm (p + 2552) _ 0 _ SLO ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
        wstep. store_addr (p + 2552 + 4 * 0)%Z. ovw_store SLO 0%Z (k1 - 1)%Z wval_lit. try clear SO.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok s0segs mm (p + 2152) _ 0 _ SHI ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
        wstep. store_addr (p + 2152 + 4 * 0)%Z. ovw_store SHI 0%Z (k2 - 1)%Z wval_lit. try clear SO.
        (* [comment removed for export] *)
        wstep.
        set (nnd' := (nnd + (k2 - 1 - (k1 - 1) + 1))%Z) in *.
        set (q0 := FQS fm 1 (zset slo 0 (k1 - 1)) (zset shi 0 (k2 - 1)) 0) in *.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_qloop X Q Hh (k1 - 1) (k2 - 1) str sv nnd' ec Jlo Jhi XOK XSEP ECR ECOK' LJlo LJhi
                      (fqs_fuel (k1 - 1) (k2 - 1)) q0 (fqs_loop (fqs_fuel (k1 - 1) (k2 - 1)) ec q0) tv mm mm) end;
          [st_eq| cbn; lia| cbn; lia| exact FMR| exact FMOK'| | exact QF| reflexivity| exact QFIN| exact AR1| exact AR2| | exact SHI| exact SLO| exact MI| apply munch_refl| apply wmono_refl|].
        { clear KC. subst q0. intros i Hi. cbn [fq_slo fq_shi fq_sp] in Hi |- *. rewrite !zdef_zset. replace i with 0%Z by lia. cbn. split; reflexivity. }
        { unfold SCq. cbn [fq_r q0]. subst nnd'. first [exact SC | replace (nnd + (k2 - 1 - (k1 - 1) + 1))%Z with (nnd - k1 + k2 + 1)%Z by lia; exact SC]. }
        intros m1 tv1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 AR1_1 AR2_1 SC1 SHI1 SLO1 MI1 MU1 WM1 FMR1 FMOK1 Hr1.
        bz_params. clear AR1 AR2 SC SHI SLO MI. lazymatch type of MU1 with munch _ ?mq _ => transport_after_call s0segs mq m1 MU1 WM1 end.
        set (qf := fqs_loop (fqs_fuel (k1 - 1) (k2 - 1)) ec q0) in *.
        unfold SCq in SC1.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        (* [comment removed for export] *)
        wstep; if_cases Kx; zify_cond_z Kx; [exfalso; lia|].
        (* [comment removed for export] *)
        urun_to 0x233a4%Z.
        enter_with (S0_headers X Q Hh k2 XOK XSEP (Z.to_nat (k2 - 1 - (k1 - 1) + 1)) (k1 - 1) (-1) (fq_fm qf) ec bh m1 m1);
          [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact ECR| exact FMOK1| exact ECOK'| exact BW| exact AR1_1| exact AR2_1| exact FTB| exact MI1| apply munch_refl| apply wmono_refl|].
        intros m2 y10 y11 y12 y13 y14 y15 y16 y24. cbv zeta. intros AR1_2 AR2_2 FTB2 MI2 MU2 WM2 BW2. bz_params.
        clear AR1_1 AR2_1 FTB MI1 MU1 WM1. transport_after_call s0segs m1 m2 MU2 WM2.
        unfold fallbackQSort3, fpush in KC. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in KC. replace (0 + 1)%Z with 1%Z in KC by reflexivity. fold q0 in KC. fold qf in KC.
        enter_with (KC m2 Hh nnd' (fq_r qf) tv1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
          [st_eq| reflexivity| reflexivity| split; [exact FMR1| split; [exact FMOK1| split; [exact BW2| subst nnd'; lia]]]| bmem_i AR1_2 AR2_2 FTB2 SC1 SHI1 SLO1 MI2| exact MU| exact WM].
  Qed.
  (* [comment removed for export] *)
  Lemma S0_bk1 : forall (fm bh slo shi : zarr) (r0 nnd hc nd rr tv k1 : Z) (me m : word -> option byte)
      (ra t0 t2 a1 a2 a3 a4 a5 a6 s5 s8 t3 t4 t5 t6 : word),
    let s := FBS fm ec bh slo shi r0 nnd false in
    k1 = bk1 nb bh (r0 + 1) -> (nb <=? k1 - 1)%Z = false ->
    (0 <= r0 + 1)%Z -> (r0 + 2 <= k1)%Z ->
    bucket_ok nb s -> binv fm bh r0 nnd -> bmem fm bh slo shi hc nd rr tv m -> munch Wb me m -> wmono s0segs me m ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x24 x28 x29 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = false -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) (Z_to_bv 64 (fb_r s')) x24 x28 x29 x30 x31) F (Z_to_bv 64 0x22798) fc None m' (seg_rom s0segs))) ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x21 x24 x28 x29 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = true -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) x21 x24 x28 x29 x30 x31) F (Z_to_bv 64 0x23458) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 (Z_to_bv 64 k1) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nnd) s5 s8 t3 t4 t5 t6) F (Z_to_bv 64 0x228a8) fc None m (seg_rom s0segs)).
  Proof.
    intros fm bh slo shi r0 nnd hc nd rr tv k1 me m ra t0 t2 a1 a2 a3 a4 a5 a6 s5 s8 t3 t4 t5 t6 s Hk1 C1 Hr0 Hk1r BOK BI BM MU WM KC KB. subst s.
    pose proof BOK as BOK0. destruct BOK as [SOK _]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd] in SOK.
    unfold scan_ok in SOK. cbv zeta in SOK. rewrite <- Hk1 in SOK. cps_destruct SOK as (_ & _ & _ & _ & _ & SD).
    apply Z.leb_gt in C1. specialize (SD ltac:(lia)). cps_destruct SD as (STOPD & HD & SEF).
    pose proof BI as BI0. cps_destruct BI as (FMR & FMOK' & BW & Hnnd). pose proof BM as BM0. cps_destruct BM as (AR1 & AR2 & FTB & SC & SHI & SLO & MI).
    open XOK XSEP.
    set (kD := fs_scan_clr_unal (FSC nb) bh k1) in *.
    pose proof (fs_scan_clr_unal_ge (FSC nb) bh k1) as GD. fold kD in GD.
    (* [comment removed for export] *)
    urun_to 0x228b0%Z. try rewrite (sx32_of_Z (k1 - 1)) by lia. try rewrite (sx32_of_Z (k1 + -1)) by lia.
    wstep; if_cases Kl; zify_cond_z Kl; [exfalso; lia|].
    assert (Hw1 : (0 <= k1 / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    urun_to 0x228d8%Z.
    enter_with (S0_scanD X Q Hh XOK (FSC nb) k1 bh m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HD| exact STOPD| exact BW| exact FTB| exact MI|].
    intros x12 x13. cbv zeta. fold kD. rewrite landv'_landv. pose proof (landv_range bh kD) as LV.
    (* [comment removed for export] *)
    wstep; if_cases Ki; zify_cond_z Ki.
    - (* [comment removed for export] *)
      apply landv_zero_isset in Ki; [| exact BW| lia]. specialize (SEF Ki). cps_destruct SEF as (STOPE & HE & STOPF & HF).
      set (kE := fs_scan_word_00 (FSC nb) bh kD) in *. set (kF := fs_scan_clr (FSC nb) bh kE) in *.
      pose proof (fs_scan_word_00_ge (FSC nb) bh kD) as GE. fold kE in GE. pose proof (fs_scan_clr_ge (FSC nb) bh kE) as GF. fold kF in GF.
      assert (HwD : (0 <= kD / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      urun_to 0x232cc%Z.
      enter_with (S0_scanE X Q Hh XOK (FSC nb) kD bh m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HE| exact STOPE| exact BW| exact FTB| exact MI|].
      intros y11 y12 y13. cbv zeta. fold kE.
      assert (HwE : (0 <= kE / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      urun_to 0x23334%Z.
      enter_with (S0_scanF X Q Hh XOK (FSC nb) kE bh m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HF| exact STOPF| exact BW| exact FTB| exact MI|].
      intros z11 z12 z13. cbv zeta. fold kF.
      enter_with (S0_bk2 fm bh slo shi r0 nnd hc nd rr tv k1 kF me m); [st_eq| exact Hk1| | apply Z.leb_gt; exact C1| lia| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WM| exact KC| exact KB].
      unfold bk2. cbv zeta. fold kD. rewrite Ki. cbn [negb]. reflexivity.
    - (* [comment removed for export] *)
      apply landv_nz_isset in Ki; [| exact BW| lia].
      (* [comment removed for export] *)
      enter_with (S0_bk2 fm bh slo shi r0 nnd hc nd rr tv k1 kD me m); [st_eq| exact Hk1| | apply Z.leb_gt; exact C1| lia| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WM| exact KC| exact KB].
      unfold bk2. cbv zeta. fold kD. rewrite Ki. cbn [negb]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_biter : forall (fm bh slo shi : zarr) (r0 nnd hc nd rr tv : Z) (me m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s8 t3 t4 t5 t6 : word),
    let s := FBS fm ec bh slo shi r0 nnd false in
    bucket_ok nb s -> binv fm bh r0 nnd -> bmem fm bh slo shi hc nd rr tv m -> munch Wb me m -> wmono s0segs me m ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x24 x28 x29 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = false -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) (Z_to_bv 64 (fb_r s')) x24 x28 x29 x30 x31) F (Z_to_bv 64 0x22798) fc None m' (seg_rom s0segs))) ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x21 x24 x28 x29 x30 x31 : word), let s' := fs_bucket_iter nb s in
      fb_done s' = true -> fb_ec s' = ec -> binv (fb_fm s') (fb_bh s') (fb_r s') (fb_nnd s') -> bmem (fb_fm s') (fb_bh s') (fb_slo s') (fb_shi s') hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd s')) x21 x24 x28 x29 x30 x31) F (Z_to_bv 64 0x23458) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nnd) (Z_to_bv 64 r0) s8 t3 t4 t5 t6) F (Z_to_bv 64 0x22798) fc None m (seg_rom s0segs)).
  Proof.
    intros fm bh slo shi r0 nnd hc nd rr tv me m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s8 t3 t4 t5 t6 s BOK BI BM MU WM KC KB. subst s.
    pose proof BOK as BOK0. destruct BOK as [SOK _]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd] in SOK.
    unfold scan_ok in SOK. cbv zeta in SOK. cps_destruct SOK as (Hk0 & H01 & STOPA & HA & SBC & _).
    pose proof BI as BI0. cps_destruct BI as (FMR & FMOK' & BW & Hnnd). pose proof BM as BM0. cps_destruct BM as (AR1 & AR2 & FTB & SC & SHI & SLO & MI).
    open XOK XSEP.
    set (k0 := (r0 + 1)%Z) in *.
    set (kA := fs_scan_set_unal (FSC nb) bh k0) in *.
    pose proof (fs_scan_set_unal_ge (FSC nb) bh k0) as GA. fold kA in GA.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z (r0 + 1)) by lia.
    enter_with (S0_scanA X Q Hh XOK (FSC nb) k0 bh m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HA| exact STOPA| exact BW| exact FTB| exact MI|].
    intros x13 x14 x21. cbv zeta. fold kA. rewrite landv'_landv. pose proof (landv_range bh kA) as LV.
    (* [comment removed for export] *)
    wstep; if_cases Ki; zify_cond_z Ki.
    - (* [comment removed for export] *)
      apply landv_zero_isset in Ki; [| exact BW| lia].
      assert (Hk1 : kA = bk1 nb bh k0). { unfold bk1. cbv zeta. fold kA. rewrite Ki. reflexivity. }
      rewrite <- Hk1 in H01.
      (* [comment removed for export] *)
      destruct (Z.leb_spec nb (kA - 1)) as [Kl|Kl].
      + (* [comment removed for export] *)
        urun_to 0x228b0%Z. wstep; if_cases Kl'; zify_cond_z Kl'; [| exfalso; lia].
        cbv zeta in KB. rewrite fs_bucket_iter_unfold in KB. cbv zeta in KB. fold k0 in KB. rewrite <- Hk1 in KB.
        replace (nb <=? kA - 1)%Z with true in KB by (symmetry; apply Z.leb_le; lia).
        enter_with (KB m hc nd rr tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
          [st_eq| reflexivity| reflexivity| exact BI0| exact BM0| exact MU| exact WM].
      + enter_with (S0_bk1 fm bh slo shi r0 nnd hc nd rr tv kA me m); [st_eq| exact Hk1| apply Z.leb_gt; lia| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WM| exact KC| exact KB].
    - (* [comment removed for export] *)
      apply landv_nz_isset in Ki; [| exact BW| lia]. specialize (SBC Ki). cps_destruct SBC as (STOPB & HB & STOPC & HC).
      set (kB := fs_scan_word_ff (FSC nb) bh kA) in *. set (kC := fs_scan_set (FSC nb) bh kB) in *.
      pose proof (fs_scan_word_ff_ge (FSC nb) bh kA) as GB. fold kB in GB. pose proof (fs_scan_set_ge (FSC nb) bh kB) as GC. fold kC in GC.
      assert (Hk1 : kC = bk1 nb bh k0). { unfold bk1. cbv zeta. fold kA. rewrite Ki. fold kB. reflexivity. }
      rewrite <- Hk1 in H01.
      enter_with (S0_scanB X Q Hh XOK (FSC nb) kA bh m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HB| exact STOPB| exact BW| exact FTB| exact MI|].
      intros y11 y12 y13. cbv zeta. fold kB.
      assert (HwB : (0 <= kB / 32 <= 28127)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      urun_to 0x2285c%Z.
      enter_with (S0_scanC X Q Hh XOK (FSC nb) kB bh m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| lia| exact HC| exact STOPC| exact BW| exact FTB| exact MI|].
      intros z11 z12 z13. cbv zeta. fold kC.
      (* [comment removed for export] *)
      destruct (Z.leb_spec nb (kC - 1)) as [Kl|Kl].
      + urun_to 0x228b0%Z. wstep; if_cases Kl'; zify_cond_z Kl'; [| exfalso; lia].
        cbv zeta in KB. rewrite fs_bucket_iter_unfold in KB. cbv zeta in KB. fold k0 in KB. rewrite <- Hk1 in KB.
        replace (nb <=? kC - 1)%Z with true in KB by (symmetry; apply Z.leb_le; lia).
        enter_with (KB m hc nd rr tv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done];
          [st_eq| reflexivity| reflexivity| exact BI0| exact BM0| exact MU| exact WM].
      + (* [comment removed for export] *)
        enter_with (S0_bk1 fm bh slo shi r0 nnd hc nd rr tv kC me m); [st_eq| exact Hk1| apply Z.leb_gt; lia| lia| lia| exact BOK0| exact BI0| exact BM0| exact MU| exact WM| exact KC| exact KB].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_bloop : forall (u : nat) (s sfin : fbs) (hc nd rr tv : Z) (me m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s8 t3 t4 t5 t6 : word),
    fb_done s = false -> fb_ec s = ec ->
    (forall v, fb_done (fs_bucket_loop v nb s) = false -> bucket_ok nb (fs_bucket_loop v nb s)) ->
    fs_bucket_loop u nb s = sfin -> fb_done sfin = true ->
    binv (fb_fm s) (fb_bh s) (fb_r s) (fb_nnd s) -> bmem (fb_fm s) (fb_bh s) (fb_slo s) (fb_shi s) hc nd rr tv m -> munch Wb me m -> wmono s0segs me m ->
    (forall m' hc' nd' rr' tv' (x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x21 x24 x28 x29 x30 x31 : word),
      fb_ec sfin = ec -> binv (fb_fm sfin) (fb_bh sfin) (fb_r sfin) (fb_nnd sfin) -> bmem (fb_fm sfin) (fb_bh sfin) (fb_slo sfin) (fb_shi sfin) hc' nd' rr' tv' m' ->
      munch Wb me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (HR x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (fb_nnd sfin)) x21 x24 x28 x29 x30 x31) F (Z_to_bv 64 0x23458) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (HR ra t0 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (fb_nnd s)) (Z_to_bv 64 (fb_r s)) s8 t3 t4 t5 t6) F (Z_to_bv 64 0x22798) fc None m (seg_rom s0segs)).
  Proof.
    induction u as [|u IH]; intros s sfin hc nd rr tv me m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 s8 t3 t4 t5 t6 Hd Hec BF RES FIN BI BM MU WM K.
    { cbn [fs_bucket_loop] in RES. subst sfin. rewrite Hd in FIN. discriminate. }
    rewrite fs_bucket_loop_S, Hd in RES.
    pose proof (BF 0%nat Hd) as BOK. cbn [fs_bucket_loop] in BOK.
    destruct s as [fm ec0 bh slo shi r0 nnd dn]. cbn [fb_fm fb_ec fb_bh fb_slo fb_shi fb_r fb_nnd fb_done] in *. subst ec0 dn.
    eapply (S0_biter fm bh slo shi r0 nnd hc nd rr tv me m); [exact BOK| exact BI| exact BM| exact MU| exact WM| |].
    - intros m' hc' nd' rr' tv' x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x24 x28 x29 x30 x31. cbv zeta. intros Hd' Hec' BI' BM' MU' WM'.
      eapply (IH (fs_bucket_iter nb (FBS fm ec bh slo shi r0 nnd false)) sfin hc' nd' rr' tv' me m');
        [exact Hd'| exact Hec'| | exact RES| exact FIN| exact BI'| exact BM'| exact MU'| exact WM'| exact K].
      intros v Hv. specialize (BF (S v)). rewrite fs_bucket_loop_S in BF. cbn [fb_done] in BF. exact (BF Hv).
    - intros m' hc' nd' rr' tv' x1 x5 x7 x10 x11 x12 x13 x14 x15 x16 x21 x24 x28 x29 x30 x31. cbv zeta. intros Hd' Hec' BI' BM' MU' WM'.
      rewrite (fs_bucket_loop_done u) in RES by exact Hd'. subst sfin.
      eapply K; [exact Hec'| exact BI'| exact BM'| exact MU'| exact WM'].
  Qed.
End S0FS.

End ACeilS1.
