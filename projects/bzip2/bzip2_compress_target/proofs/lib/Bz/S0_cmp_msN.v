(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCSewF.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCQsortM2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewC.BzCSewB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Lemma shiftr_bounds : forall b s, (0 <= b)%Z -> (0 <= s)%Z -> (0 <= Z.shiftr b s <= b)%Z.
Proof.
  intros b s Hb Hs. rewrite Z.shiftr_div_pow2 by lia.
  assert (P : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma shiftr_mono_l : forall a b s, (0 <= s)%Z -> (a <= b)%Z -> (Z.shiftr a s <= Z.shiftr b s)%Z.
Proof. intros. rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia| assumption]. Qed.
(* [comment removed for export] *)
Lemma shifts_small : forall b s, (0 <= b < 2097152)%Z -> (0 <= s)%Z -> (65534 < Z.shiftr b s)%Z -> (s <= 5)%Z.
Proof.
  intros b s Hb Hs H. destruct (Z.le_gt_cases s 5) as [L|G]; [exact L|]. exfalso.
  assert (M : (Z.shiftr b s <= Z.shiftr b 6)%Z).
  { rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_compat_l; [lia|]. split; [change (2 ^ 6)%Z with 64%Z; lia| apply Z.pow_le_mono_r; lia]. }
  rewrite (Z.shiftr_div_pow2 b 6) in M by lia. change (2 ^ 6)%Z with 64%Z in M. Z.div_mod_to_equations. lia.
Qed.

Lemma shiftr_m1 : forall s, (0 <= s)%Z -> Z.shiftr (-1) s = (-1)%Z.
Proof.
  intros s Hs. rewrite Z.shiftr_div_pow2 by lia. assert (P : (0 < 2 ^ s)%Z) by (apply Z.pow_pos_nonneg; lia).
  symmetry. apply Z.div_unique with (r := (2 ^ s - 1)%Z); [left; lia| lia].
Qed.

Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 4928)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  (* [comment removed for export] *)
  Lemma S0_shifts : forall (f : nat) (b sh : Z)
      (x0 x4 x5 x6 x7 x8 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (m : word -> option byte),
    (0 <= b < 2097152)%Z -> (0 <= sh <= 6)%Z -> (6 - sh < Z.of_nat f)%Z ->
    (forall (sh' : Z) (x13' : word), sh' = ms_shifts f b sh -> (0 <= sh' <= 6)%Z -> (Z.shiftr b sh' <= 65534)%Z ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            (Z_to_bv 64 b) (Z_to_bv 64 sh') x11 x12 x13' (Z_to_bv 64 65534) x15 x16
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a4bc) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 b) (Z_to_bv 64 (sh - 1)) x11 x12 x13 (Z_to_bv 64 65534) x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a4b0) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; [intros; exfalso; lia|].
    intros b sh x0 x4 x5 x6 x7 x8 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 m Hb Hsh Hf K.
    msenv_open XOK. rewrite ms_shifts_S in K.
    pose proof (shiftr_bounds b sh ltac:(lia) ltac:(lia)) as SB.
    (* [comment removed for export] *)
    wstep. wstep. replace (sh - 1 + 1)%Z with sh by lia. rewrite (Z.mod_small sh 32) by lia. rewrite swrap32_small by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - pose proof (shifts_small b sh ltac:(lia) ltac:(lia) ltac:(lia)) as S5.
      replace (65534 <? Z.shiftr b sh) with true in K by (symmetry; apply Z.ltb_lt; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH b (sh + 1)%Z x0 x4 x5 x6 x7 x8 x11 x12 _ x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 mm) end;
        [st_eq| lia| lia| lia| exact K].
    - replace (65534 <? Z.shiftr b sh) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K sh _) end; [st_eq| reflexivity| lia| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  Ltac rd32_at FTB idx :=
    lazymatch type of FTB with u32arr ?segs ?mm ?A (zw32 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zw32_read segs mm A a nn idx _ FTB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.

  (* [comment removed for export] *)
  Lemma S0_quad : forall (cnt : nat) (j bbStart sh : Z) (a1 a2 : zarr) (sb : scb)
      (x0 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 : word) (me m : word -> option byte),
    Z.of_nat cnt = (j + 1)%Z -> (0 <= j)%Z -> (0 <= bbStart)%Z -> (bbStart + j < n)%Z -> (0 <= sh <= 6)%Z -> (Z.shiftr j sh < 65536)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> rw_cells s0segs m (p + 144) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A2, A2 + ARR2_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (x11' x14' x15' x16' x4' : word), let a2' := ms_quad cnt a2 a1 qo n bbStart sh j in zbok a2' ->
      u8arr s0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> rw_cells s0segs m' (p + 144) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4' x5 x6 x7 x8
                            x9 (Z_to_bv 64 sh) x11' (Z_to_bv 64 (A1 - 4 + 4 * bbStart)) (Z_to_bv 64 (A1 - 4 + 4 * bbStart)) x14' x15' x16'
                            x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a534) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          x9 (Z_to_bv 64 sh) (Z_to_bv 64 j) (Z_to_bv 64 (A1 + 4 * (bbStart + j))) (Z_to_bv 64 (A1 - 4 + 4 * bbStart)) x14 x15 x16
                          x17 x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 n) x22 x23 x24 x25 (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a4f4) fc None m (seg_rom s0segs)).
  Proof.
    induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros j bbStart sh a1 a2 sb x0 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me m
           Hcnt Hj Hbs Hbj Hsh Hq A1OK A2OK PR AR1 AR2 SCB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. open_sc_in SCB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    rewrite ms_quad_S in K. cbv zeta in K.
    pose proof (PR (bbStart + j)%Z ltac:(lia)) as Pu. set (u := rd32 a1 (bbStart + j)) in *.
    pose proof (shiftr_bounds j sh ltac:(lia) ltac:(lia)) as SB.
    (* [comment removed for export] *)
    rdptr AR1 A1OK (bbStart + j)%Z. fold u.
    wstep. rewrite (Z.mod_small sh 32), swrap32_small by lia.
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SO1 : store_ok s0segs mm (wa (A2 + (qo + 2 * u))) 2 = true)
        by (eapply (u8arr_storeN_ok s0segs _ A2 _ (qo + 2 * u) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      pose proof (zb8_write2 s0segs mm A2 a2 ARR2_SIZE (qo + 2 * u) (Z_to_bv 64 (Z.shiftr j sh)) AR2 ltac:(lia) ltac:(lia)) as AR2w;
      change bs with (le2 (Z_to_bv 64 (Z.shiftr j sh))) end.
    clear AR2. store_done. rename AR2w into AR2. rewrite (unsigned_lit (Z.shiftr j sh)) in AR2 by lia.
    change (wr16 a2 (qo + 2 * u) (Z.shiftr j sh)) with (qwr a2 qo u (Z.shiftr j sh)) in AR2.
    pose proof (zbok_qwr a2 qo u (Z.shiftr j sh) A2OK) as OK1. set (a2q := qwr a2 qo u (Z.shiftr j sh)) in *.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Ko; zify_cond_z Ko.
    - replace (u <? BZ_N_OVERSHOOT) with false in K by (symmetry; apply Z.ltb_ge; unfold BZ_N_OVERSHOOT; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z bbStart sh a1 a2q sb x0 _ x5 x6 x7 x8 x9 _ _ _ x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me mm) end;
          [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact OK1| exact PR| exact AR1| exact AR2| | exact MI| exact MU| exact WM| exact K].
        * apply (Z.le_lt_trans _ (Z.shiftr j sh)); [apply shiftr_mono_l; lia| exact Hq].
        * match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
      + assert (cnt = 0%nat) as -> by lia. cbn [ms_quad] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact OK1| exact AR1| exact AR2| | exact MI| exact MU| exact WM].
        match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
    - replace (u <? BZ_N_OVERSHOOT) with true in K by (symmetry; apply Z.ltb_lt; unfold BZ_N_OVERSHOOT; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      pose proof (zb8_length a2q ARR2_SIZE ltac:(lia)) as L2q.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SO2 : store_ok s0segs mm (wa (A2 + (qo + 2 * (u + n)))) 2 = true)
          by (eapply (u8arr_storeN_ok s0segs _ A2 _ (qo + 2 * (u + n)) 2 _ AR2); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]) end.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
        pose proof (zb8_write2 s0segs mm A2 a2q ARR2_SIZE (qo + 2 * (u + n)) (Z_to_bv 64 (Z.shiftr j sh)) AR2 ltac:(lia) ltac:(lia)) as AR2w;
        change bs with (le2 (Z_to_bv 64 (Z.shiftr j sh))) end.
      clear AR2. store_done. rename AR2w into AR2. rewrite (unsigned_lit (Z.shiftr j sh)) in AR2 by lia.
      change (wr16 a2q (qo + 2 * (u + n)) (Z.shiftr j sh)) with (qwr a2q qo (u + n) (Z.shiftr j sh)) in AR2.
      pose proof (zbok_qwr a2q qo (u + n) (Z.shiftr j sh) OK1) as OK2. set (a2r := qwr a2q qo (u + n) (Z.shiftr j sh)) in *.
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (j - 1)%Z bbStart sh a1 a2r sb x0 _ x5 x6 x7 x8 x9 _ _ _ x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 me mm) end;
          [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact OK2| exact PR| exact AR1| exact AR2| | exact MI| exact MU| exact WM| exact K].
        * apply (Z.le_lt_trans _ (Z.shiftr j sh)); [apply shiftr_mono_l; lia| exact Hq].
        * match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
      + assert (cnt = 0%nat) as -> by lia. cbn [ms_quad] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _) end;
          [st_eq| exact OK2| exact AR1| exact AR2| | exact MI| exact MU| exact WM].
        match goal with H : rw_cells _ _ (p + 144)%Z _ |- _ => exact H end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_step3 : forall (i ss : Z) (a1 a2 ftm : zarr) (sa : sca) (sb : scb)
      (x0 x4 x5 x6 x11 x12 x13 x14 x15 x16 x24 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let bbStart := clearmask (zget ftm (Z.shiftl ss 8)) in let bbEnd := clearmask (zget ftm (Z.shiftl (ss + 1) 8)) in
    let bbSize := (bbEnd - bbStart)%Z in let sh := ms_shifts 40 bbSize 0 in
    (0 <= i < 255)%Z -> (0 <= ss < 256)%Z -> ftv ftm -> (bbStart <= bbEnd)%Z -> (bbEnd <= n)%Z -> k104 sa = Z_to_bv 64 (FT + 1024 * ss) ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ftm 65537) ->
    rw_cells s0segs m (p + 16) (sca_cells X sa) -> rw_cells s0segs m (p + 144) (scb_cells X sb) -> mem_inv s0segs m ->
    munch [(A2, A2 + ARR2_SIZE)]%Z me m -> wmono s0segs me m ->
    (forall m' (y4 y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y27 y28 y29 y30 : word),
      let a2' := ms_quad (Z.to_nat bbSize) a2 a1 qo n bbStart sh (bbSize - 1) in zbok a2' ->
      u8arr s0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ftm 65537) ->
      rw_cells s0segs m' (p + 16) (sca_cells X sa) -> rw_cells s0segs m' (p + 144) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 (p + 2600)) (Z_to_bv 64 FT)
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                            x24 (Z_to_bv 64 (i + 1)) (Z_to_bv 64 A1) y27 y28 y29 y30)
                       F (Z_to_bv 64 0x19b00) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 (p + 2344 + ss)) (Z_to_bv 64 FT)
                          (Z_to_bv 64 255) (Z_to_bv 64 2097152) x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 (FT + 262144 + 4 * ss)) (Z_to_bv 64 (FT + 262144 + 4 * ss)) (Z_to_bv 64 A2) (Z_to_bv 64 (FT + 4 * (256 * ss + 256))) (Z_to_bv 64 n)
                          (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624)) x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) x27 x28 x29 x30)
                     F (Z_to_bv 64 0x1a48c) fc None m (seg_rom s0segs)).
  Proof.
    intros i ss a1 a2 ftm sa sb x0 x4 x5 x6 x11 x12 x13 x14 x15 x16 x24 x27 x28 x29 x30 me m.
    intros bbStart bbEnd bbSize sh Hi Hss FTV Hle Hn K104 A1OK A2OK PR AR1 AR2 FTB SCA SCB MI MU WM K.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2. pose proof (zw32_length ftm 65537 ltac:(lia)) as Lft.
    destruct sa as [w48 w56 w64 w88 w96 w104]. cbn [k104] in K104. subst w104. open_sc_in SCA.
    pose proof (FTV (256 * ss)%Z ltac:(lia)) as V0. pose proof (FTV (256 * ss + 256)%Z ltac:(lia)) as V1.
    assert (Hbs : bbStart = clearmask (zget ftm (256 * ss))) by (subst bbStart; rewrite shl8; reflexivity).
    assert (Hbe : bbEnd = clearmask (zget ftm (256 * ss + 256))) by (subst bbEnd; rewrite shl8; f_equal; f_equal; lia).
    pose proof (clearmask_bounds (zget ftm (256 * ss)) ltac:(lia)) as Bs. rewrite <- Hbs in Bs.
    pose proof (clearmask_bounds (zget ftm (256 * ss + 256)) ltac:(lia)) as Be. rewrite <- Hbe in Be.
    (* [comment removed for export] *)
    wstep. rd32_at FTB (256 * ss)%Z. rd32_at FTB (256 * ss + 256)%Z. wstep.
    wstep. rewrite land_CM64, <- Hbs by lia. wstep. rewrite land_CM64, <- Hbe by lia.
    wstep. fold bbSize. replace (bbEnd - bbStart)%Z with bbSize by reflexivity.
    wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_shifts 40 bbSize 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
      [st_eq| subst bbSize; lia| lia| cbn; lia|].
    intros sh' v13 Esh Hsh' Hq. fold sh in Esh. subst sh'.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    assert (TAIL : forall m' (a2' : zarr) (y4 y11 y12 y13 y14 y15 y16 : word),
      a2' = ms_quad (Z.to_nat bbSize) a2 a1 qo n bbStart sh (bbSize - 1) -> zbok a2' ->
      u8arr s0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ftm 65537) ->
      rw_cells s0segs m' (p + 16) (sca_cells X (mkSCA w48 w56 w64 w88 w96 (Z_to_bv 64 (FT + 1024 * ss)))) -> rw_cells s0segs m' (p + 144) (scb_cells X sb) -> mem_inv s0segs m' ->
      munch [(A2, A2 + ARR2_SIZE)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp y4 x5 x6 (Z_to_bv 64 (p + 2600)) (Z_to_bv 64 FT)
                            (Z_to_bv 64 bbSize) (Z_to_bv 64 sh) y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 256) (Z_to_bv 64 98) (Z_to_bv 64 A2) (Z_to_bv 64 (p + 1320)) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 (p + 3624))
                            x24 (Z_to_bv 64 i) (Z_to_bv 64 A1) x27 x28 x29 x30)
                       F (Z_to_bv 64 0x1a534) fc None m' (seg_rom s0segs))).
    { intros m' a2' y4 y11 y12 y13 y14 y15 y16 Ea2 OK' AR1' AR2' FTB' SCA' SCB' MI' MU' WM'. rewrite <- Ea2 in K.
      clear AR1 AR2 FTB SCB MI MU WM. match goal with H : rw_cells _ m (p + 16)%Z _ |- _ => clear H end.
      (* [comment removed for export] *)
      wstep. wstep. rewrite (Z.mod_small sh 32) by lia.
      assert (SR : (-1 <= Z.shiftr (bbSize - 1) sh <= 65534)%Z).
      { destruct (Z.eq_dec bbSize 0) as [E0|NE].
        - rewrite E0. change (0 - 1)%Z with (-1)%Z. rewrite shiftr_m1 by lia. lia.
        - pose proof (shiftr_bounds (bbSize - 1) sh ltac:(lia) ltac:(lia)). pose proof (shiftr_mono_l (bbSize - 1) bbSize sh ltac:(lia) ltac:(lia)). lia. }
      replace (bbSize + -1)%Z with (bbSize - 1)%Z by lia. rewrite swrap32_small by lia.
      wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
      (* [comment removed for export] *)
      wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact OK'| exact AR1'| exact AR2'| exact FTB'| exact SCA'| exact SCB'| exact MI'| exact MU'| exact WM']. }
    wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - (* [comment removed for export] *)
      assert (E0 : bbSize = 0%Z) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm a2 _ _ _ _ _ _ _) end;
        [st_eq| rewrite E0; reflexivity| exact A2OK| exact AR1| exact AR2| exact FTB| exact SCA| exact SCB| exact MI| exact MU| exact WM].
    - (* [comment removed for export] *)
      do 8 wstep.
      replace (Z_to_bv 64 (18446744073709551615 - bbStart + bbEnd)) with (Z_to_bv 64 (bbSize - 1))
        by (apply Z_to_bv_eqm; subst bbSize; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_quad (Z.to_nat bbSize) (bbSize - 1)%Z bbStart sh a1 a2 sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| | exact A1OK| exact A2OK| exact PR| exact AR1| exact AR2| exact SCB| exact MI| apply munch_refl| apply wmono_refl|].
      { pose proof (shiftr_mono_l (bbSize - 1) bbSize sh ltac:(lia) ltac:(lia)). lia. }
      intros m' y11 y14 y15 y16 y4. cbv zeta. intros OK' AR1' AR2' SCB' MI' MU' WM'.
      clear AR1 AR2 SCB MI. transport_after_call s0segs m m' MU' WM'. clear MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact OK'| exact AR1'| exact AR2'| exact FTB| exact SCA| exact SCB'| exact MI'| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End S0MS.

End ACeilS1.
