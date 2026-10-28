(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2 S0_cmp_msV.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2 S0_cmp_msV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
Module S0_cmp_msD.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_gtu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msV.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac sw_ptr AR1 j :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of AR1 with u8arr ?segs m ?A (zb8 ?a ?nn) =>
        let H := fresh "ARw" in
        pose proof (zb8_write4 segs m A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1
      end end.

  (* [comment removed for export] *)
  Lemma S0_shift1 : forall (d h lo hi v : Z) (a2 : zarr) (sb : scb) (x25 : word) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (xra x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m -> wmono s0segs me m ->
    (forall m' (xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x23' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 j') (Z_to_bv 64 h)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) (Z_to_bv 64 j') x23' (Z_to_bv 64 d) x25 (Z_to_bv 64 (v + d)) (Z_to_bv 64 (A1 + 4 * j'))
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x217a4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) (Z_to_bv 64 j) x23 (Z_to_bv 64 d) x25 (Z_to_bv 64 (v + d)) x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x216f8) fc None m (seg_rom s0segs)).
  Proof.
    intros d h lo hi v a2 sb x25. induction f as [|f IH]; [intros; lia|].
    intros j a1 b xra x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 me m
           Hh Hlo Hj Hhi Hd Hv A1OK A2OK PR Hf BL BH AR1 AR2 SCB BUD MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR (j - h)%Z ltac:(lia)) as Pjh. set (pv := rd32 a1 (j - h)) in Pjh.
    pose proof (mss_shift_budget_le (S f) a1 a2 qo n d h lo j v b) as BLE.
    pose proof (mss_shift_budget_le_gtu f a1 a2 qo n d h lo j v b) as BG. fold pv in BG.
    pose proof BL as BL2. rewrite mss_shift_S in K, BL2, BLE. fold pv in K. fold pv in BL2. fold pv in BLE.
    pose proof (mainGtU_budget_le (pv + d) (v + d) a2 qo n b) as GL.
    destruct (mainGtU (pv + d) (v + d) a2 qo n b) as [gt b1] eqn:GT. cbn [fst snd] in BG, GL.
    assert (Epv : rd32 a1 (j - h) = pv) by reflexivity. clearbody pv.
  (* [comment removed for export] *)
    urun_to 0x21730%Z. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
  (* [comment removed for export] *)
    open_sc_in SCB. urun_to 0x2174c%Z.
  (* [comment removed for export] *)
    wstep.
    call (S0_mainGtU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A2 qo n (pv + d)%Z (v + d)%Z b (p + 336)%Z a2);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR2| exact BUD| exact MI| exact A2OK
      | lia| lia| bz_params; lia| lia| lia| lia| bz_ceil; bz_params; unfold CEIL; lia| lia| lia| lia| unfold apart; lia
      | rewrite GT; cbn [snd]; lia| lia| ].
    rewrite GT in *. cbn [fst snd] in *. cbn [ci_segs S0C] in *. fold (scb_cells X sb) in SCB.
    match goal with H : ?x = Z_to_bv 64 (Z.b2z gt) |- _ => subst x end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    match goal with H : rw_cells _ _ (p + 336)%Z _ |- _ => rename H into BUD end.
    match goal with H : u8arr _ _ A2 (zb8 a2 ARR2_SIZE) |- _ => clear H end.
  (* [comment removed for export] *)
    destruct gt; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      wstep; if_cases Kz; [zify_cond Kz; exfalso; cbn in Kz; lia|]. clear Kz.
      urun_to 0x2177c%Z. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO : store_ok s0segs mm (wa (A1 + 4 * j)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 j. rewrite (unsigned_lit pv) in AR1 by lia.
      set (a1a := wr32 a1 j pv) in *.
      assert (A1OKa : zbok a1a) by (subst a1a; apply zbok_wr32; exact A1OK).
      assert (PRa : pr n a1a 0 (n - 1)).
      { intros y Hy. subst a1a. pose proof (PR y Hy). destruct (Z.eq_dec y j) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
      urun.
      if_cases Kc; zify_cond_z Kc.
      + replace (j - h <=? lo + h - 1) with false in K, BL2 by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z a1a b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact A1OKa| exact A2OK| exact PRa| lia| exact BL2| lia
          | exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM|].
        intros m' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x23' x28' x29' x30' x31'. cbv zeta.
        intros AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' J' B'.
        eapply (K m'); [exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia].
      + replace (j - h <=? lo + h - 1) with true in K, BL2 by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K, BL2.
        urun_to 0x217a4%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OKa| exact PRa| lia| lia].
    - (* [comment removed for export] *)
      wstep; if_cases Kz; [| zify_cond Kz; exfalso; cbn in Kz; lia]. clear Kz. cbn [fst snd] in K, BL2.
      urun_to 0x217a4%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia| lia].
  Time Qed.

  (* [comment removed for export] *)
  Lemma U0_shift2 : forall (d h lo hi v : Z) (a2 : zarr) (sb : scb) (x8 : word) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m -> wmono s0segs me m ->
    (forall m' (xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' x8 (Z_to_bv 64 h)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22' (Z_to_bv 64 v) (Z_to_bv 64 d) (Z_to_bv 64 j') (Z_to_bv 64 (v + d)) (Z_to_bv 64 (A1 + 4 * j'))
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x218bc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22 (Z_to_bv 64 v) (Z_to_bv 64 d) (Z_to_bv 64 j) (Z_to_bv 64 (v + d)) x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21818) fc None m (seg_rom s0segs)).
  Proof.
    intros d h lo hi v a2 sb x8. induction f as [|f IH]; [intros; lia|].
    intros j a1 b xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 me m
           Hh Hlo Hj Hhi Hd Hv A1OK A2OK PR Hf BL BH AR1 AR2 SCB BUD MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR (j - h)%Z ltac:(lia)) as Pjh. set (pv := rd32 a1 (j - h)) in Pjh.
    pose proof (mss_shift_budget_le (S f) a1 a2 qo n d h lo j v b) as BLE.
    pose proof (mss_shift_budget_le_gtu f a1 a2 qo n d h lo j v b) as BG. fold pv in BG.
    pose proof BL as BL2. rewrite mss_shift_S in K, BL2, BLE. fold pv in K. fold pv in BL2. fold pv in BLE.
    pose proof (mainGtU_budget_le (pv + d) (v + d) a2 qo n b) as GL.
    destruct (mainGtU (pv + d) (v + d) a2 qo n b) as [gt b1] eqn:GT. cbn [fst snd] in BG, GL.
    assert (Epv : rd32 a1 (j - h) = pv) by reflexivity. clearbody pv.
  (* [comment removed for export] *)
    urun_to 0x2184c%Z. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
  (* [comment removed for export] *)
    open_sc_in SCB. urun_to 0x21868%Z.
  (* [comment removed for export] *)
    wstep.
    call (S0_mainGtU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A2 qo n (pv + d)%Z (v + d)%Z b (p + 336)%Z a2);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR2| exact BUD| exact MI| exact A2OK
      | lia| lia| bz_params; lia| lia| lia| lia| bz_ceil; bz_params; unfold CEIL; lia| lia| lia| lia| unfold apart; lia
      | rewrite GT; cbn [snd]; lia| lia| ].
    rewrite GT in *. cbn [fst snd] in *. cbn [ci_segs S0C] in *. fold (scb_cells X sb) in SCB.
    match goal with H : ?x = Z_to_bv 64 (Z.b2z gt) |- _ => subst x end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    match goal with H : rw_cells _ _ (p + 336)%Z _ |- _ => rename H into BUD end.
    match goal with H : u8arr _ _ A2 (zb8 a2 ARR2_SIZE) |- _ => clear H end.
  (* [comment removed for export] *)
    destruct gt; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      wstep; if_cases Kz; [zify_cond Kz; exfalso; cbn in Kz; lia|]. clear Kz.
      urun_to 0x21898%Z. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO : store_ok s0segs mm (wa (A1 + 4 * j)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 j. rewrite (unsigned_lit pv) in AR1 by lia.
      set (a1a := wr32 a1 j pv) in *.
      assert (A1OKa : zbok a1a) by (subst a1a; apply zbok_wr32; exact A1OK).
      assert (PRa : pr n a1a 0 (n - 1)).
      { intros y Hy. subst a1a. pose proof (PR y Hy). destruct (Z.eq_dec y j) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
      urun.
      if_cases Kc; zify_cond_z Kc.
      + replace (j - h <=? lo + h - 1) with false in K, BL2 by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z a1a b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact A1OKa| exact A2OK| exact PRa| lia| exact BL2| lia
          | exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM|].
        intros m' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31'. cbv zeta.
        intros AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' J' B'.
        eapply (K m'); [exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia].
      + replace (j - h <=? lo + h - 1) with true in K, BL2 by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K, BL2.
        urun_to 0x218bc%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OKa| exact PRa| lia| lia].
    - (* [comment removed for export] *)
      wstep; if_cases Kz; [| zify_cond Kz; exfalso; cbn in Kz; lia]. clear Kz. cbn [fst snd] in K, BL2.
      urun_to 0x218bc%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia| lia].
  Time Qed.

  Lemma S0_shift2 : forall (d h lo hi v : Z) (a2 : zarr) (sb : scb) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m -> wmono s0segs me m ->
    (forall m' (xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 j) (Z_to_bv 64 h)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22' (Z_to_bv 64 v) (Z_to_bv 64 d) (Z_to_bv 64 j') (Z_to_bv 64 (v + d)) (Z_to_bv 64 (A1 + 4 * j'))
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x218bc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 j) (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22 (Z_to_bv 64 v) (Z_to_bv 64 d) (Z_to_bv 64 j) (Z_to_bv 64 (v + d)) x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21818) fc None m (seg_rom s0segs)).
  Proof.
    intros d h lo hi v a2 sb f j. exact (U0_shift2 d h lo hi v a2 sb (Z_to_bv 64 j) f j).
  Qed.

  (* [comment removed for export] *)
  Lemma U0_shift3 : forall (d h lo hi v : Z) (a2 : zarr) (sb : scb) (x25 : word) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m -> wmono s0segs me m ->
    (forall m' (xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 j') (Z_to_bv 64 h)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22' (Z_to_bv 64 v) (Z_to_bv 64 d) x25 (Z_to_bv 64 (v + d)) (Z_to_bv 64 (A1 + 4 * j'))
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x219c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 j) (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22 (Z_to_bv 64 v) (Z_to_bv 64 d) x25 (Z_to_bv 64 (v + d)) x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21924) fc None m (seg_rom s0segs)).
  Proof.
    intros d h lo hi v a2 sb x25. induction f as [|f IH]; [intros; lia|].
    intros j a1 b xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 me m
           Hh Hlo Hj Hhi Hd Hv A1OK A2OK PR Hf BL BH AR1 AR2 SCB BUD MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR (j - h)%Z ltac:(lia)) as Pjh. set (pv := rd32 a1 (j - h)) in Pjh.
    pose proof (mss_shift_budget_le (S f) a1 a2 qo n d h lo j v b) as BLE.
    pose proof (mss_shift_budget_le_gtu f a1 a2 qo n d h lo j v b) as BG. fold pv in BG.
    pose proof BL as BL2. rewrite mss_shift_S in K, BL2, BLE. fold pv in K. fold pv in BL2. fold pv in BLE.
    pose proof (mainGtU_budget_le (pv + d) (v + d) a2 qo n b) as GL.
    destruct (mainGtU (pv + d) (v + d) a2 qo n b) as [gt b1] eqn:GT. cbn [fst snd] in BG, GL.
    assert (Epv : rd32 a1 (j - h) = pv) by reflexivity. clearbody pv.
  (* [comment removed for export] *)
    urun_to 0x21958%Z. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
  (* [comment removed for export] *)
    open_sc_in SCB. urun_to 0x21974%Z.
  (* [comment removed for export] *)
    wstep.
    call (S0_mainGtU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A2 qo n (pv + d)%Z (v + d)%Z b (p + 336)%Z a2);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR2| exact BUD| exact MI| exact A2OK
      | lia| lia| bz_params; lia| lia| lia| lia| bz_ceil; bz_params; unfold CEIL; lia| lia| lia| lia| unfold apart; lia
      | rewrite GT; cbn [snd]; lia| lia| ].
    rewrite GT in *. cbn [fst snd] in *. cbn [ci_segs S0C] in *. fold (scb_cells X sb) in SCB.
    match goal with H : ?x = Z_to_bv 64 (Z.b2z gt) |- _ => subst x end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    match goal with H : rw_cells _ _ (p + 336)%Z _ |- _ => rename H into BUD end.
    match goal with H : u8arr _ _ A2 (zb8 a2 ARR2_SIZE) |- _ => clear H end.
  (* [comment removed for export] *)
    destruct gt; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      wstep; if_cases Kz; [zify_cond Kz; exfalso; cbn in Kz; lia|]. clear Kz.
      urun_to 0x219a4%Z. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO : store_ok s0segs mm (wa (A1 + 4 * j)) 4 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep. sw_ptr AR1 j. rewrite (unsigned_lit pv) in AR1 by lia.
      set (a1a := wr32 a1 j pv) in *.
      assert (A1OKa : zbok a1a) by (subst a1a; apply zbok_wr32; exact A1OK).
      assert (PRa : pr n a1a 0 (n - 1)).
      { intros y Hy. subst a1a. pose proof (PR y Hy). destruct (Z.eq_dec y j) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
      urun.
      if_cases Kc; zify_cond_z Kc.
      + replace (j - h <=? lo + h - 1) with false in K, BL2 by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z a1a b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact A1OKa| exact A2OK| exact PRa| lia| exact BL2| lia
          | exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM|].
        intros m' xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31'. cbv zeta.
        intros AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' J' B'.
        eapply (K m'); [exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia].
      + replace (j - h <=? lo + h - 1) with true in K, BL2 by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K, BL2.
        urun_to 0x219c8%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OKa| exact PRa| lia| lia].
    - (* [comment removed for export] *)
      wstep; if_cases Kz; [| zify_cond Kz; exfalso; cbn in Kz; lia]. clear Kz. cbn [fst snd] in K, BL2.
      urun_to 0x219c8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia| lia].
  Time Qed.

  Lemma S0_shift3 : forall (d h lo hi v : Z) (a2 : zarr) (sb : scb) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m -> wmono s0segs me m ->
    (forall m' (xra' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 336, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' (Z_to_bv 64 j') (Z_to_bv 64 h)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22' (Z_to_bv 64 v) (Z_to_bv 64 d) (Z_to_bv 64 j) (Z_to_bv 64 (v + d)) (Z_to_bv 64 (A1 + 4 * j'))
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x219c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 j) (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22 (Z_to_bv 64 v) (Z_to_bv 64 d) (Z_to_bv 64 j) (Z_to_bv 64 (v + d)) x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x21924) fc None m (seg_rom s0segs)).
  Proof.
    intros d h lo hi v a2 sb f j. exact (U0_shift3 d h lo hi v a2 sb (Z_to_bv 64 j) f j).
  Qed.

End S0MS.

End ACeilS1.
End S0_cmp_msD.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msE.S0_cmp_msD.
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
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac sw_ptr AR1 j :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?ad (le4 ?w)) _) =>
      lazymatch type of AR1 with u8arr ?segs m ?A (zb8 ?a ?nn) =>
        let H := fresh "ARw" in
        pose proof (zb8_write4 segs m A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1
      end end.

  Ltac sb_of H := lazymatch type of H with rw_cells _ _ _ [C8 _; C8 ?a; C8 ?b; C8 ?c; C8 ?d; _; C8 ?e; C8 ?f; C8 ?g; _; _; C8 ?h; _; _; C8 ?i; C8 ?j; C8 ?k; C8 ?l; _; _; _; C8 ?o; _; _; _; _; _] => constr:(mkSCB a b c d e f g h i j k l o) end.
  Ltac name_mem nm := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => first [ rename mm into nm | set (nm := mm) in *; clearbody nm ] end.
  (* [comment removed for export] *)
  Lemma S0_hloop : forall (d h lo hi : Z) (a2 : zarr) (w128 w136 w144 w152 w168 w176 w184 w208 : word)
      (f : nat) (i : Z) (a1 : zarr) (b : Z) (e240 e248 : Z) (w232 w288 : word)
      (xra x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= i <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (hi + 2 - i <= 3 * Z.of_nat f)%Z ->
    (-2147483648 < snd (fst (mss_hloop f a1 a2 qo n d h lo hi i b)))%Z -> (b < 2147483648)%Z ->
    (e240 = i + 2)%Z -> (e248 = i + 1)%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells s0segs m (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232 (Z_to_bv 64 e240)
                                   (Z_to_bv 64 e248) (Z_to_bv 64 hi) w288)) ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch [(A1, A1 + ARR1_SIZE); (p + 120, p + 340)]%Z me m -> wmono s0segs me m ->
    (forall m' (w232' w240' w248' w288' xra' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x25' x26' x27' x28' x29' x30' x31' : word),
      let r := mss_hloop f a1 a2 qo n d h lo hi i b in let a1' := fst (fst r) in let b' := snd (fst r) in
      snd r = false ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232' w240'
                                     w248' (Z_to_bv 64 hi) w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 120, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b' <= b)%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' x8' x9'
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) x19' (Z_to_bv 64 A2) x21' x22' x23' (Z_to_bv 64 d) x25' x26' x27'
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x21a2c) fc None m' (seg_rom s0segs))) ->
    (forall m' (w232' w240' w248' w288' xra' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x25' x26' x27' x28' x29' x30' x31' : word),
      let r := mss_hloop f a1 a2 qo n d h lo hi i b in let a1' := fst (fst r) in let b' := snd (fst r) in
      snd r = true -> (b' < 0)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232' w240'
                                     w248' (Z_to_bv 64 hi) w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' ->
      munch [(A1, A1 + ARR1_SIZE); (p + 120, p + 340)]%Z me m' -> wmono s0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      evt s0segs Q (MS (mkR xra' (Z_to_bv 64 p) gp tp x5' x6' x7' x8' x9'
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 A1) x19' (Z_to_bv 64 A2) x21' x22' x23' (Z_to_bv 64 d) x25' x26' x27'
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x21c18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 h)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 A2) (Z_to_bv 64 0) x22 x23 (Z_to_bv 64 d) (Z_to_bv 64 i) x26 x27
                          x28 (Z_to_bv 64 hi) x30 x31)
                     F (Z_to_bv 64 0x216b4) fc None m (seg_rom s0segs)).
  Proof.
    intros d h lo hi a2 w128 w136 w144 w152 w168 w176 w184 w208.
    induction f as [|f IH]; [intros; lia|].
    intros i a1 b e240 e248 w232 w288 xra x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x30 x31 me m
           Hh Hlo Hi Hhi Hd A1OK A2OK PR Hf BL BH E240 E248 AR1 AR2 SCB BUD MI MU WM K1 K2. subst e240 e248.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (mss_hloop_budget_le (S f) a1 a2 qo n d h lo hi i b) as BLE.
    pose proof BL as BL2. rewrite mss_hloop_S in K1, K2, BL2.
    open_sc_in SCB.
    (* [comment removed for export] *)
    urun.
    if_cases Kc; zify_cond_z Kc.
    { replace (hi <? i) with true in K1 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K1.
     
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia]. }
    replace (hi <? i) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
    pose proof (mss_hloop_le_ins1 f a1 a2 qo n d h lo hi i b ltac:(apply Z.ltb_ge; lia)) as LE1.
    rewrite mss_ins_shift_budget in LE1.
    (* [comment removed for export] *)
    pose proof (PR i ltac:(lia)) as Pv1. set (v1 := rd32 a1 i) in Pv1.
    assert (Ev1 : rd32 a1 i = v1) by reflexivity. clearbody v1.
    urun.
    rdptr AR1 A1OK i. rewrite Ev1.
    urun_to 0x216f8%Z.
    (* [comment removed for export] *)
    assert (BS1 : (-2147483648 < snd (mss_shift (S (Z.to_nat (i - lo))) a1 a2 qo n d h lo i v1 b))%Z) by (rewrite <- Ev1; lia).
    name_mem mq0.
    let sb := sb_of SCB in
    enter_with (S0_shift1 X Q XOK XSEP d h lo hi v1 a2 sb _ (S (Z.to_nat (i - lo))) i a1 b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq0 mq0);
      [st_eq| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| apply shift_fuel_ok; lia| exact BS1| lia
      | exact AR1| exact AR2| exact SCB| exact BUD| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1 xra1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31. cbv zeta. intros AR1_1 AR2_1 SCB1 BUD1 MI1 MU1 WM1 OK1 PR1 J1 B1.
    clear AR1 AR2 SCB BUD MI. transport_after_call s0segs mq0 m1 MU1 WM1. clear MU1 WM1. bz_params.
    destruct (mss_shift (S (Z.to_nat (i - lo))) a1 a2 qo n d h lo i v1 b) as [[a1s j1] b1] eqn:SH1. cbn [fst snd] in *.
    assert (E1 : mss_ins a1 a2 qo n d h lo i b = (wr32 a1s j1 v1, b1)) by (rewrite mss_ins_eq; cbv zeta; rewrite Ev1, SH1; reflexivity).
    rewrite E1 in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2.
    pose proof (zb8_length a1s ARR1_SIZE ltac:(lia)) as L1s.
    open_sc_in SCB1.
    (* [comment removed for export] *)
    urun.
    assert (SO : store_ok s0segs m1 (wa (A1 + 4 * j1)) 4 = true)
      by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j1) 4 _ AR1_1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]).
    wstep. sw_ptr AR1_1 j1. rewrite (unsigned_lit v1) in AR1_1 by lia.
    set (a1b := wr32 a1s j1 v1) in *.
    assert (OKb : zbok a1b) by (subst a1b; apply zbok_wr32; exact OK1).
    assert (PRb : pr n a1b 0 (n - 1)).
    { intros y Hy. subst a1b. pose proof (PR1 y Hy). destruct (Z.eq_dec y j1) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
    (* [comment removed for export] *)
    urun.
    if_cases Kc2; zify_cond_z Kc2.
    { replace (hi <? i + 1) with true in K1 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact AR1_1| exact AR2_1| exact SCB1| exact BUD1| exact MI1| assumption| assumption| exact OKb| exact PRb| lia]. }
    replace (hi <? i + 1) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
    pose proof (mss_hloop_le_ins2 f a1 a2 qo n d h lo hi i b _ _ ltac:(apply Z.ltb_ge; lia) E1 ltac:(apply Z.ltb_ge; lia)) as LE2.
    rewrite mss_ins_shift_budget in LE2.
    (* [comment removed for export] *)
    pose proof (PRb (i + 1)%Z ltac:(lia)) as Pv2. set (v2 := rd32 a1b (i + 1)) in Pv2.
    assert (Ev2 : rd32 a1b (i + 1) = v2) by reflexivity. clearbody v2.
    urun.
    rdptr AR1_1 OKb (i + 1)%Z. rewrite Ev2.
    urun_to 0x21818%Z.
    (* [comment removed for export] *)
    assert (BS2 : (-2147483648 < snd (mss_shift (S (Z.to_nat (i + 1 - lo))) a1b a2 qo n d h lo (i + 1) v2 b1))%Z) by (rewrite <- Ev2; lia).
    name_mem mq1.
    let sb := sb_of SCB1 in
    enter_with (S0_shift2 X Q XOK XSEP d h lo hi v2 a2 sb (S (Z.to_nat (i + 1 - lo))) (i + 1)%Z a1b b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq1 mq1);
      [st_eq| lia| lia| lia| lia| lia| lia| exact OKb| exact A2OK| exact PRb| apply shift_fuel_ok; lia| exact BS2| lia
      | exact AR1_1| exact AR2_1| exact SCB1| exact BUD1| exact MI1| apply munch_refl| apply wmono_refl|].
    intros m2 xra2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z22 z28 z29 z30 z31. cbv zeta. intros AR1_2 AR2_2 SCB2 BUD2 MI2 MU2 WM2 OK2 PR2 J2 B2.
    clear AR1_1 AR2_1 SCB1 BUD1 MI1. transport_after_call s0segs mq1 m2 MU2 WM2. clear MU2 WM2. bz_params.
    destruct (mss_shift (S (Z.to_nat (i + 1 - lo))) a1b a2 qo n d h lo (i + 1) v2 b1) as [[a1c j2] b2] eqn:SH2. cbn [fst snd] in *.
    assert (E2 : mss_ins a1b a2 qo n d h lo (i + 1) b1 = (wr32 a1c j2 v2, b2)) by (rewrite mss_ins_eq; cbv zeta; rewrite Ev2, SH2; reflexivity).
    rewrite E2 in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2.
    pose proof (zb8_length a1c ARR1_SIZE ltac:(lia)) as L1c.
    open_sc_in SCB2.
    (* [comment removed for export] *)
    urun.
    assert (SO2 : store_ok s0segs m2 (wa (A1 + 4 * j2)) 4 = true)
      by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j2) 4 _ AR1_2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]).
    wstep. sw_ptr AR1_2 j2. rewrite (unsigned_lit v2) in AR1_2 by lia.
    set (a1d := wr32 a1c j2 v2) in *.
    assert (OKd : zbok a1d) by (subst a1d; apply zbok_wr32; exact OK2).
    assert (PRd : pr n a1d 0 (n - 1)).
    { intros y Hy. subst a1d. pose proof (PR2 y Hy). destruct (Z.eq_dec y j2) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
    (* [comment removed for export] *)
    urun.
    if_cases Kc3; zify_cond_z Kc3.
    { replace (hi <? i + 1 + 1) with true in K1 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact AR1_2| exact AR2_2| exact SCB2| exact BUD2| exact MI2| assumption| assumption| exact OKd| exact PRd| lia]. }
    replace (hi <? i + 1 + 1) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
    pose proof (mss_hloop_le_ins3 f a1 a2 qo n d h lo hi i b _ _ _ _ ltac:(apply Z.ltb_ge; lia) E1 ltac:(apply Z.ltb_ge; lia) E2 ltac:(apply Z.ltb_ge; lia)) as LE3.
    rewrite mss_ins_shift_budget in LE3.
    (* [comment removed for export] *)
    pose proof (PRd (i + 2)%Z ltac:(lia)) as Pv3. set (v3 := rd32 a1d (i + 2)) in Pv3.
    assert (Ev3 : rd32 a1d (i + 2) = v3) by reflexivity. clearbody v3.
    replace (i + 1 + 1)%Z with (i + 2)%Z in * by lia.
    urun.
    rdptr AR1_2 OKd (i + 2)%Z. rewrite Ev3.
    urun_to 0x21924%Z.
    (* [comment removed for export] *)
    assert (BS3 : (-2147483648 < snd (mss_shift (S (Z.to_nat (i + 2 - lo))) a1d a2 qo n d h lo (i + 2) v3 b2))%Z) by (rewrite <- Ev3; lia).
    name_mem mq2.
    let sb := sb_of SCB2 in
    enter_with (S0_shift3 X Q XOK XSEP d h lo hi v3 a2 sb (S (Z.to_nat (i + 2 - lo))) (i + 2)%Z a1d b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq2 mq2);
      [st_eq| lia| lia| lia| lia| lia| lia| exact OKd| exact A2OK| exact PRd| apply shift_fuel_ok; lia| exact BS3| lia
      | exact AR1_2| exact AR2_2| exact SCB2| exact BUD2| exact MI2| apply munch_refl| apply wmono_refl|].
    intros m3 xra3 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u22 u28 u29 u30 u31. cbv zeta. intros AR1_3 AR2_3 SCB3 BUD3 MI3 MU3 WM3 OK3 PR3 J3 B3.
    clear AR1_2 AR2_2 SCB2 BUD2 MI2. transport_after_call s0segs mq2 m3 MU3 WM3. clear MU3 WM3. bz_params.
    destruct (mss_shift (S (Z.to_nat (i + 2 - lo))) a1d a2 qo n d h lo (i + 2) v3 b2) as [[a1e j3] b3] eqn:SH3. cbn [fst snd] in *.
    assert (E3 : mss_ins a1d a2 qo n d h lo (i + 2) b2 = (wr32 a1e j3 v3, b3)) by (rewrite mss_ins_eq; cbv zeta; rewrite Ev3, SH3; reflexivity).
    rewrite E3 in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2.
    pose proof (zb8_length a1e ARR1_SIZE ltac:(lia)) as L1e.
    open_sc_in SCB3.
    (* [comment removed for export] *)
    urun.
    assert (SO3 : store_ok s0segs m3 (wa (A1 + 4 * j3)) 4 = true)
      by (eapply (u8arr_storeN_ok s0segs _ A1 _ (4 * j3) 4 _ AR1_3); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]).
    wstep. sw_ptr AR1_3 j3. rewrite (unsigned_lit v3) in AR1_3 by lia.
    set (a1f := wr32 a1e j3 v3) in *.
    assert (OKf : zbok a1f) by (subst a1f; apply zbok_wr32; exact OK3).
    assert (PRf : pr n a1f 0 (n - 1)).
    { intros y Hy. subst a1f. pose proof (PR3 y Hy). destruct (Z.eq_dec y j3) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
    (* [comment removed for export] *)
    urun. rewrite (sx32_of_Z_signed b3) by lia.
    (* [comment removed for export] *)
    if_cases Kb; [apply bgez_taken in Kb; [|lia] | apply bgez_not_taken in Kb; [|lia]].
    - replace (b3 <? 0) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
      replace (i + 2 + 1)%Z with (i + 3)%Z in K1, K2, BL2 by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IH (i + 3)%Z a1f b3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| lia| exact OKf| exact A2OK| exact PRf| lia| exact BL2| lia| | | exact AR1_3| exact AR2_3| | exact BUD3| exact MI3| assumption| assumption| | ].
      3:{ exact SCB3. }
      + lia. + lia.
      + intros m' w232' w240' w248' w288' xra' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x25' x26' x27' x28' x29' x30' x31'. cbv zeta.
        intros FL AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' B'.
        eapply (K1 m'); [exact FL| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
      + intros m' w232' w240' w248' w288' xra' x5' x6' x7' x8' x9' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x25' x26' x27' x28' x29' x30' x31'. cbv zeta.
        intros FL BN AR1' AR2' SCB' BUD' MI' MU' WM' OK' PR' B'.
        eapply (K2 m'); [exact FL| exact BN| exact AR1'| exact AR2'| exact SCB'| exact BUD'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
    - replace (b3 <? 0) with true in K2 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K2.
      urun_to 0x21c18%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K2 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| lia| exact AR1_3| exact AR2_3| exact SCB3| exact BUD3| exact MI3| assumption| assumption| exact OKf| exact PRf| lia].
  Time Qed.
End S0MS.

End ACeilS1.
