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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msD B0_cmp_msW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  (* [comment removed for export] *)
  Variables (w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w416 w480 : word).
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WSH := [(A1, A1 + ARR1_SIZE); (P + 496, P + 500); (P - 32, P)]%Z.
  Notation WH := [(A1, A1 + ARR1_SIZE); (P, P + 500); (P - 32, P)]%Z.
  (* [comment removed for export] *)
  Notation SLH q328 q336 q344 q352 q392 hi :=
    (slm_cells X Y SHF SHn (mkSLQ w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 q328 q336 q344 q352 q392 (Z_to_bv 64 hi) w416 (Z_to_bv 64 0) w480)).
  (* [comment removed for export] *)

  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac sw_ptr AR1 j v :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of AR1 with u8arr ?segs mm ?A (zb8 ?a ?nn) =>
        let SO := fresh "SO" in
        assert (SO : store_ok segs mm (wa (A + 4 * j)) 4 = true)
          by (eapply (u8arr_storeN_ok segs mm A _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]);
        wstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?ad (le4 ?w)) _) =>
          let H := fresh "ARw" in
          pose proof (zb8_write4 segs mm A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1;
          rewrite unsigned_lit in AR1 by lia;
          lazymatch type of AR1 with u8arr _ _ _ (zb8 (wr32 _ _ ?x) _) => replace x with v in AR1 by lia end
        end; try clear SO end end.
  Ltac key_left j :=
    try lazymatch goal with |- context [Z_to_bv 64 (?x + me_A1 X)] => replace (x + me_A1 X)%Z with (me_A1 X + 4 * j)%Z by lia end.
  (* [comment removed for export] *)
  Ltac sub_aco ACW MU := eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve].
  Ltac sub_shz SH MU := eapply (shzW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac sub_shp SH MU := eapply (shpW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].

  Lemma B0_hloop : forall (d h lo hi : Z) (a2 : zarr)
      (f : nat) (i : Z) (a1 : zarr) (b : Z) (e336 e344 : Z) (w328 w352 w392 : word)
      (x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x25 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= i <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (hi + 2 - i <= 3 * Z.of_nat f)%Z ->
    (-2147483648 < snd (fst (mss_hloop f a1 a2 qo n d h lo hi i b)))%Z -> (b < 2147483648)%Z ->
    (e336 = i + 2)%Z -> (e344 = i + 1)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells b0segs m P (SLH w328 (Z_to_bv 64 e336) (Z_to_bv 64 e344) w352 w392 hi) ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m ->
    munch WH me m -> wmono b0segs me m ->
    acoW WH me ->
    shzW b0segs WH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WH me A2 (A2 + ARR2_SIZE) -> shpW b0segs WH me (P + 496) (P + 500) ->
    (forall m' (w328' w336' w344' w352' w392' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x23' x25' x28' x29' x30' x31' : word),
      let r := mss_hloop f a1 a2 qo n d h lo hi i b in let a1' := fst (fst r) in let b' := snd (fst r) in
      snd r = false ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells b0segs m' P (SLH w328' w336' w344' w352' w392' hi) ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' ->
      munch WH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b' <= b)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' x19' x20' x21' (Z_to_bv 64 (lo + h - 1)) x23' (Z_to_bv 64 d) x25' (Z_to_bv 64 h) cSB
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa3890) fc None m' (seg_rom b0segs))) ->
    (forall m' (w328' w336' w344' w352' w392' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x23' x25' x28' x29' x30' x31' : word),
      let r := mss_hloop f a1 a2 qo n d h lo hi i b in let a1' := fst (fst r) in let b' := snd (fst r) in
      snd r = true -> (b' < 0)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      rw_cells b0segs m' P (SLH w328' w336' w344' w352' w392' hi) ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' ->
      munch WH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (-2147483648 < b')%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' x19' x20' x21' (Z_to_bv 64 (lo + h - 1)) x23' (Z_to_bv 64 d) x25' (Z_to_bv 64 h) cSB
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa3970) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 (Z_to_bv 64 i) x13 x14 x15 x16 x17
                          x18 x19 x20 x21 (Z_to_bv 64 (lo + h - 1)) x23 (Z_to_bv 64 d) x25 (Z_to_bv 64 h) cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa322c) fc None m (seg_rom b0segs)).
  Proof.
    intros d h lo hi a2.
    induction f as [|f IH]; [intros; lia|].
    intros i a1 b e336 e344 w328 w352 w392 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x25 x28 x29 x30 x31 me m
           Hh Hlo Hi Hhi Hd A1OK A2OK PR Hf BL BH E336 E344 AR1 AR2 SLB BUD STK MI MU WM ACW SH1 SH2 SHB K1 K2. subst e336 e344.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. pose proof alloc_ceiling_range as ACR.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (mss_hloop_budget_le (S f) a1 a2 qo n d h lo hi i b) as BLE.
    pose proof BL as BL2. rewrite mss_hloop_S in K1, K2, BL2.
    open_slb_in SLB.
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    { replace (hi <? i) with true in K1 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia]. }
    replace (hi <? i) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
    pose proof (mss_hloop_le_ins1 f a1 a2 qo n d h lo hi i b ltac:(apply Z.ltb_ge; lia)) as LE1.
    rewrite mss_ins_shift_budget in LE1.
    (* [comment removed for export] *)
    pose proof (PR i ltac:(lia)) as Pv1. set (v1 := rd32 a1 i) in Pv1.
    assert (Ev1 : rd32 a1 i = v1) by reflexivity. clearbody v1.
    brun_to 0xa3240%Z. brun. rdptr AR1 A1OK i. rewrite Ev1. brun_to 0xa3298%Z.
    (* [comment removed for export] *)
    assert (BS1 : (-2147483648 < snd (mss_shift (S (Z.to_nat (i - lo))) a1 a2 qo n d h lo i v1 b))%Z) by (rewrite <- Ev1; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq1 end.
    enter_with (B0_shift1 X Y SHF SHn Q XOK XSEP YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d h lo hi v1 a2 (S (Z.to_nat (i - lo))) i a1 b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq1 mq1);
      [st_eq| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| apply shift_fuel_ok; lia| exact BS1| lia
      | exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| apply munch_refl| apply wmono_refl
      | sub_aco ACW MU| sub_shz SH1 MU| sub_shz SH2 MU| sub_shp SHB MU|].
    intros m1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y28 y29 y30 y31. cbv zeta. intros AR1_1 AR2_1 SLB1 BUD1 STK1 MI1 MU1 WM1 OK1 PR1 J1 B1.
    clear AR1 AR2 SLB BUD STK MI. transport_after_call b0segs mq1 m1 MU1 WM1. clear MU1 WM1. bz_params. open_slb_in SLB1.
    destruct (mss_shift (S (Z.to_nat (i - lo))) a1 a2 qo n d h lo i v1 b) as [[a1s j1] b1] eqn:SH1e. cbn [fst snd] in *.
    assert (E1 : mss_ins a1 a2 qo n d h lo i b = (wr32 a1s j1 v1, b1)) by (rewrite mss_ins_eq; cbv zeta; rewrite Ev1, SH1e; reflexivity).
    rewrite E1 in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2.
    pose proof (zb8_length a1s ARR1_SIZE ltac:(lia)) as L1s.
    (* [comment removed for export] *)
    brun. sw_ptr AR1_1 j1 v1.
    set (a1b := wr32 a1s j1 v1) in *.
    assert (OKb : zbok a1b) by (subst a1b; apply zbok_wr32; exact OK1).
    assert (PRb : pr n a1b 0 (n - 1)).
    { intros y Hy. subst a1b. pose proof (PR1 y Hy). destruct (Z.eq_dec y j1) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
    (* [comment removed for export] *)
    brun. if_cases Kc2; zify_cond_z Kc2.
    { replace (hi <? i + 1) with true in K1 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact AR1_1| exact AR2_1| exact SLB1| exact BUD1| exact STK1| exact MI1| assumption| assumption| exact OKb| exact PRb| lia]. }
    replace (hi <? i + 1) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
    pose proof (mss_hloop_le_ins2 f a1 a2 qo n d h lo hi i b _ _ ltac:(apply Z.ltb_ge; lia) E1 ltac:(apply Z.ltb_ge; lia)) as LE2.
    rewrite mss_ins_shift_budget in LE2.
    (* [comment removed for export] *)
    pose proof (PRb (i + 1)%Z ltac:(lia)) as Pv2. set (v2 := rd32 a1b (i + 1)) in Pv2.
    assert (Ev2 : rd32 a1b (i + 1) = v2) by reflexivity. clearbody v2.
    brun_to 0xa3470%Z. key_left (i + 1)%Z. brun. rdptr AR1_1 OKb (i + 1)%Z. rewrite Ev2. brun_to 0xa3490%Z.
    (* [comment removed for export] *)
    assert (BS2 : (-2147483648 < snd (mss_shift (S (Z.to_nat (i + 1 - lo))) a1b a2 qo n d h lo (i + 1) v2 b1))%Z) by (rewrite <- Ev2; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq2 end.
    enter_with (B0_shift2 X Y SHF SHn Q XOK XSEP YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d h lo hi v2 a2 (S (Z.to_nat (i + 1 - lo))) (i + 1)%Z a1b b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq2 mq2);
      [st_eq| lia| lia| lia| lia| lia| lia| exact OKb| exact A2OK| exact PRb| apply shift_fuel_ok; lia| exact BS2| lia
      | exact AR1_1| exact AR2_1| exact SLB1| exact BUD1| exact STK1| exact MI1| apply munch_refl| apply wmono_refl
      | sub_aco ACW MU| sub_shz SH1 MU| sub_shz SH2 MU| sub_shp SHB MU|].
    intros m2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z21 z28 z29 z30 z31. cbv zeta. intros AR1_2 AR2_2 SLB2 BUD2 STK2 MI2 MU2 WM2 OK2 PR2 J2 B2.
    clear AR1_1 AR2_1 SLB1 BUD1 STK1 MI1. transport_after_call b0segs mq2 m2 MU2 WM2. clear MU2 WM2. bz_params. open_slb_in SLB2.
    destruct (mss_shift (S (Z.to_nat (i + 1 - lo))) a1b a2 qo n d h lo (i + 1) v2 b1) as [[a1c j2] b2] eqn:SH2e. cbn [fst snd] in *.
    assert (E2 : mss_ins a1b a2 qo n d h lo (i + 1) b1 = (wr32 a1c j2 v2, b2)) by (rewrite mss_ins_eq; cbv zeta; rewrite Ev2, SH2e; reflexivity).
    rewrite E2 in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2.
    pose proof (zb8_length a1c ARR1_SIZE ltac:(lia)) as L1c.
    (* [comment removed for export] *)
    brun. sw_ptr AR1_2 j2 v2.
    set (a1d := wr32 a1c j2 v2) in *.
    assert (OKd : zbok a1d) by (subst a1d; apply zbok_wr32; exact OK2).
    assert (PRd : pr n a1d 0 (n - 1)).
    { intros y Hy. subst a1d. pose proof (PR2 y Hy). destruct (Z.eq_dec y j2) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
    (* [comment removed for export] *)
    brun. if_cases Kc3; zify_cond_z Kc3.
    { replace (hi <? i + 1 + 1) with true in K1 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K1 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| exact AR1_2| exact AR2_2| exact SLB2| exact BUD2| exact STK2| exact MI2| assumption| assumption| exact OKd| exact PRd| lia]. }
    replace (hi <? i + 1 + 1) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
    pose proof (mss_hloop_le_ins3 f a1 a2 qo n d h lo hi i b _ _ _ _ ltac:(apply Z.ltb_ge; lia) E1 ltac:(apply Z.ltb_ge; lia) E2 ltac:(apply Z.ltb_ge; lia)) as LE3.
    rewrite mss_ins_shift_budget in LE3.
    (* [comment removed for export] *)
    pose proof (PRd (i + 2)%Z ltac:(lia)) as Pv3. set (v3 := rd32 a1d (i + 2)) in Pv3.
    assert (Ev3 : rd32 a1d (i + 2) = v3) by reflexivity. clearbody v3.
    replace (i + 1 + 1)%Z with (i + 2)%Z in * by lia.
    brun_to 0xa3658%Z. key_left (i + 2)%Z. brun. rdptr AR1_2 OKd (i + 2)%Z. rewrite Ev3. brun_to 0xa3678%Z.
    (* [comment removed for export] *)
    assert (BS3 : (-2147483648 < snd (mss_shift (S (Z.to_nat (i + 2 - lo))) a1d a2 qo n d h lo (i + 2) v3 b2))%Z) by (rewrite <- Ev3; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq3 end.
    enter_with (B0_shift3 X Y SHF SHn Q XOK XSEP YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d h lo hi v3 a2 (S (Z.to_nat (i + 2 - lo))) (i + 2)%Z a1d b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq3 mq3);
      [st_eq| lia| lia| lia| lia| lia| lia| exact OKd| exact A2OK| exact PRd| apply shift_fuel_ok; lia| exact BS3| lia
      | exact AR1_2| exact AR2_2| exact SLB2| exact BUD2| exact STK2| exact MI2| apply munch_refl| apply wmono_refl
      | sub_aco ACW MU| sub_shz SH1 MU| sub_shz SH2 MU| sub_shp SHB MU|].
    intros m3 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u18 u21 u28 u29 u30 u31. cbv zeta. intros AR1_3 AR2_3 SLB3 BUD3 STK3 MI3 MU3 WM3 OK3 PR3 J3 B3.
    clear AR1_2 AR2_2 SLB2 BUD2 STK2 MI2. transport_after_call b0segs mq3 m3 MU3 WM3. clear MU3 WM3. bz_params. open_slb_in SLB3.
    destruct (mss_shift (S (Z.to_nat (i + 2 - lo))) a1d a2 qo n d h lo (i + 2) v3 b2) as [[a1e j3] b3] eqn:SH3e. cbn [fst snd] in *.
    assert (E3 : mss_ins a1d a2 qo n d h lo (i + 2) b2 = (wr32 a1e j3 v3, b3)) by (rewrite mss_ins_eq; cbv zeta; rewrite Ev3, SH3e; reflexivity).
    rewrite E3 in K1, K2, BL2. cbv zeta in K1. cbv zeta in K2. cbv zeta in BL2.
    pose proof (zb8_length a1e ARR1_SIZE ltac:(lia)) as L1e.
    (* [comment removed for export] *)
    brun. sw_ptr AR1_3 j3 v3.
    set (a1f := wr32 a1e j3 v3) in *.
    assert (OKf : zbok a1f) by (subst a1f; apply zbok_wr32; exact OK3).
    assert (PRf : pr n a1f 0 (n - 1)).
    { intros y Hy. subst a1f. pose proof (PR3 y Hy). destruct (Z.eq_dec y j3) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
    (* [comment removed for export] *)
    brun_to 0xa3808%Z. wstep. rewrite (sx32_of_Z_signed b3) by lia.
    (* [comment removed for export] *)
    brun_to 0xa3828%Z.
    (* [comment removed for export] *)
    wstep; if_cases Kb; [apply bgez_taken in Kb; [|lia] | apply bgez_not_taken in Kb; [|lia]].
    - replace (b3 <? 0) with false in K1, K2, BL2 by (symmetry; apply Z.ltb_ge; lia).
      replace (i + 2 + 1)%Z with (i + 3)%Z in K1, K2, BL2 by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IH (i + 3)%Z a1f b3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
        [st_eq| lia| lia| lia| lia| lia| exact OKf| exact A2OK| exact PRf| lia| exact BL2| lia| |
        | exact AR1_3| exact AR2_3| exact SLB3| exact BUD3| exact STK3| exact MI3| assumption| assumption| exact ACW| exact SH1| exact SH2| exact SHB| | ].
      + lia. + lia.
      + intros m' w328' w336' w344' w352' w392' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x23' x25' x28' x29' x30' x31'. cbv zeta.
        intros FL AR1' AR2' SLB' BUD' STK' MI' MU' WM' OK' PR' B'.
        eapply (K1 m'); [exact FL| exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
      + intros m' w328' w336' w344' w352' w392' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x20' x21' x23' x25' x28' x29' x30' x31'. cbv zeta.
        intros FL BN AR1' AR2' SLB' BUD' STK' MI' MU' WM' OK' PR' B'.
        eapply (K2 m'); [exact FL| exact BN| exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia].
    - replace (b3 <? 0) with true in K2 by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K2.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K2 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| reflexivity| lia| exact AR1_3| exact AR2_3| exact SLB3| exact BUD3| exact STK3| exact MI3| assumption| assumption| exact OKf| exact PRf| lia].
  Qed.
End B0MS.
End ACeilS1.
