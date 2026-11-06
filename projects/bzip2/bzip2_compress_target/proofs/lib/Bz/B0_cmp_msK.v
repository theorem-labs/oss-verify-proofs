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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_msF B0_cmp_msH B0_cmp_msJ B0_cmp_msW B0_cmp_fsW.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Ltac sx_norm_all := repeat match goal with |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_of_Z_signed v) by lia end.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id; demod; sx_norm_all.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  (* [comment removed for export] *)
  Variables (w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w480 : word).
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation NA2 := (18446744073709551615 - A2)%Z. Notation NSLO := (18446744073709551615 - am_SLO Y)%Z.
  Notation W1 := [(A1, A1 + ARR1_SIZE)]%Z.
  Notation WST := [(P, P + 496); (P + 500, P + 536); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.
  Notation WH := [(A1, A1 + ARR1_SIZE); (P, P + 500); (P - 32, P)]%Z.
  Notation WQA := [(A1, A1 + ARR1_SIZE); (P, P + 536); (P - 32, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.
  (* [comment removed for export] *)
  Notation SLK q240 q248 q264 q272 q312 q328 q336 q344 q352 q392 q408 q416 q440 :=
    (slm_cells X Y SHF SHn (mkSLQ w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 q240 q248 q264 q272 q312 q328 q336 q344 q352 q392 q408 q416 q440 w480)).
  (* [comment removed for export] *)

  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  Ltac rdblk AR2 AOK idx :=
    lazymatch type of AR2 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read1 segs mm A a nn idx _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; cbv beta;
      let B := fresh "By" in pose proof (AOK idx) as B;
      rewrite (unsigned_lit8 (zget a idx)) by lia
    end.
  Ltac sub_aco ACW MU := eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve].
  Ltac sub_shz SH MU := eapply (shzW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac sub_shp SH MU := eapply (shpW_sub b0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].

  (* [comment removed for export] *)
  Lemma B0_med : forall (lo hi d : Z) (a1 a2 : zarr) (w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w440 : word) (W : list ivl) (me : word -> option byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x26 x28 x29 x30 x31 : word) (m : word -> option byte),
    (0 <= lo)%Z -> (lo + 20 <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    rw_cells b0segs m P (SLK w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 (Z_to_bv 64 hi) (Z_to_bv 64 lo) w440) -> mem_inv b0segs m ->
    munch W me m -> shzW b0segs W me A1 (A1 + ARR1_SIZE) -> shzW b0segs W me A2 (A2 + ARR2_SIZE) ->
    (forall (med : Z) (x5' x11' x12' x16' : word),
      med = mmed3 (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d)) -> (0 <= med < 256)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6 x7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A1 + 4 * lo)) x11' x12' x13 x14 x15 x16' (Z_to_bv 64 med)
                            x18 x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28 x29 x30 x31)
                       F (Z_to_bv 64 0xa270c) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2560) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi d a1 a2 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w440 W me
           x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x23 x25 x26 x28 x29 x30 x31 m
           Hlo Hlh Hhi Hd A1OK A2OK PR AR1 AR2 SLB MI MU SH1 SH2 K.
    msenv_open XOK. amenv_open YOK. bz_params. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR lo ltac:(lia)) as Pl. set (pl := rd32 a1 lo) in *. assert (Epl : rd32 a1 lo = pl) by reflexivity. clearbody pl.
    pose proof (PR hi ltac:(lia)) as Ph. set (ph := rd32 a1 hi) in *. assert (Eph : rd32 a1 hi = ph) by reflexivity. clearbody ph.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK lo. rewrite Epl.
    (* [comment removed for export] *)
    brun. rdblk AR2 A2OK (pl + d)%Z.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK hi. rewrite Eph.
    (* [comment removed for export] *)
    brun_to 0xa2670%Z.
    set (mid := Z.shiftr (lo + hi) 1) in *.
    assert (Hmid : mid = ((lo + hi) / 2)%Z) by (subst mid; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    lazymatch goal with |- context [Z_to_bv 64 ((lo + hi) / 2)] => idtac | |- _ => idtac "WARN: sraiw form" end.
    rewrite <- ?Hmid.
    pose proof (PR mid ltac:(rewrite Hmid; Z.div_mod_to_equations; lia)) as Pm. set (pm := rd32 a1 mid) in *. assert (Epm : rd32 a1 mid = pm) by reflexivity. clearbody pm.
    assert (Hmid2 : (lo <= mid <= hi)%Z) by (rewrite Hmid; Z.div_mod_to_equations; lia).
    clearbody mid.
    (* [comment removed for export] *)
    brun. rdblk AR2 A2OK (ph + d)%Z.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK mid. rewrite Epm.
    unfold rd8 in K. set (c0 := zget a2 (pl + d)) in *. set (c1 := zget a2 (ph + d)) in *. clearbody c0 c1.
    (* [comment removed for export] *)
    assert (JOIN1 : forall y5,
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 (A2 + (pm + d))) (Z_to_bv 64 (if c1 <? c0 then c0 else c1)) x13 x14 x15 (Z_to_bv 64 c1) (Z_to_bv 64 (if c1 <? c0 then c1 else c0))
                          x18 x19 x20 (Z_to_bv 64 A2) (Z_to_bv 64 NA2) x23 (Z_to_bv 64 d) x25 x26 cSB x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa26f8) fc None m (seg_rom b0segs))).
    2:{ brun. if_cases Kc1; zify_cond_z Kc1.
        - (* [comment removed for export] *)
          wstep; if_cases Kc2; zify_cond_z Kc2; [exfalso; lia|]. wstep.
          enter_with (JOIN1 _). all: replace (c1 <? c0) with true by (symmetry; apply Z.ltb_lt; lia); st_eq.
        - wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
          + enter_with (JOIN1 _). all: replace (c1 <? c0) with false by (symmetry; apply Z.ltb_ge; lia); st_eq.
          + (* [comment removed for export] *) wstep. enter_with (JOIN1 _). all: replace (c1 <? c0) with false by (symmetry; apply Z.ltb_ge; lia); st_eq. }
    intros y5.
    set (mx := if c1 <? c0 then c0 else c1) in *. set (mn := if c1 <? c0 then c1 else c0) in *.
    assert (Hmx : (0 <= mx < 256)%Z) by (subst mx; destruct (c1 <? c0); lia).
    assert (Hmn : (0 <= mn < 256)%Z) by (subst mn; destruct (c1 <? c0); lia).
    assert (Hmnx : (mn <= mx)%Z) by (subst mn mx; destruct (Z.ltb_spec c1 c0); lia).
    (* [comment removed for export] *)
    rdblk AR2 A2OK (pm + d)%Z.
    set (c2 := zget a2 (pm + d)) in *. clearbody c2.
    assert (MED : forall med, (med = if c2 <? mx then (if c2 <? mn then mn else c2) else mx)%Z ->
              med = mmed3 c0 c1 c2 /\ (0 <= med < 256)%Z).
    { intros med ->. unfold mmed3. subst mx mn. destruct (Z.ltb_spec c1 c0); destruct (Z.ltb_spec c2 c0); destruct (Z.ltb_spec c2 c1); split; try reflexivity; lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc3; zify_cond_z Kc3.
    - (* [comment removed for export] *)
      wstep; if_cases Kc4; zify_cond_z Kc4; [|exfalso; lia].
      destruct (MED mn) as [E1 E2]; [replace (c2 <? mx) with true by (symmetry; apply Z.ltb_lt; lia); replace (c2 <? mn) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
      enter_with (K mn _ _ _ _ E1 E2). st_eq.
    - wstep. wstep; if_cases Kc4; zify_cond_z Kc4.
      + (* [comment removed for export] *)
        destruct (MED c2) as [E1 E2]; [replace (c2 <? mx) with true by (symmetry; apply Z.ltb_lt; lia); replace (c2 <? mn) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
        enter_with (K c2 _ _ _ _ E1 E2). st_eq.
      + (* [comment removed for export] *)
        wstep.
        destruct (MED mx) as [E1 E2]; [replace (c2 <? mx) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
        enter_with (K mx _ _ _ _ E1 E2). st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  Notation WAP := [(A1, A1 + ARR1_SIZE); (P, P + 496); (P + 500, P + 536); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.   (* [comment removed for export] *)
  Ltac st_stk ARR idx v :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of ARR with u32arr _ _ ?BASE _ =>
        let SO := fresh "SO" in
        pose proof (u32arr_store_ok b0segs mm BASE _ idx _ ARR ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO;
        wstep; ovw_store ARR idx v (apply unsigned_lit_mod32); try clear SO end end.

  (* [comment removed for export] *)
  Definition bqat (qsp : Z) (m : word -> option byte) : Prop :=
    forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x28 x29 x30 x31 : word),
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                      x10 x11 x12 x13 x14 x15 x16 x17
                      x18 x19 (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 A2) (Z_to_bv 64 NA2) (Z_to_bv 64 NSLO) x24 (Z_to_bv 64 (SD + 4 * (qsp - 1))) (Z_to_bv 64 qsp) cSB
                      x28 x29 x30 x31)
                 F (Z_to_bv 64 0xa24a4) fc None m (seg_rom b0segs)).

  (* [comment removed for export] *)
  Lemma B0_apart : forall (lo hi d ltLo unLo unHi gtHi qsp SHl SHh SHd : Z) (a1 a2 : zarr) (slo shi sd : zarr) (Jlo Jhi Jd : list byte)
      (w240 w248 w264 w272 w312 w328 w336 w344 w352 : word) (nx : nxt)
      (x11 x12 x17 x18 x19 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 51)%Z ->
    saddr (SLO + 4 * (qsp - 1)) SHl -> saddr (SHI + 4 * (qsp - 1)) SHh -> saddr (SD + 4 * (qsp - 1)) SHd ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr b0segs m SLO (ovw slo Jlo 100) -> u32arr b0segs m SHI (ovw shi Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLK w240 w248 w264 w272 w312 w328 w336 w344 w352 (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
    rw_cells b0segs m (P + 500) (nxt_cells nx) -> mem_inv b0segs m ->
    munch WAP me m -> wmono b0segs me m ->
    shzW b0segs WAP me A1 (A1 + ARR1_SIZE) -> shzW b0segs WAP me SLO (SLO + 400) -> shzW b0segs WAP me SHI (SHI + 400) -> shzW b0segs WAP me SD (SD + 400) ->
    ((gtHi < ltLo)%Z -> forall m',
      u8arr b0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw slo Jlo 100) -> u32arr b0segs m' SHI (ovw shi Jhi 100) ->
      u32arr b0segs m' SD (ovw (zset sd (qsp - 1) (d + 1)) Jd 100) ->
      rw_cells b0segs m' P (SLK w240 w248 w264 w272 w312 w328 w336 w344 w352 (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx) -> mem_inv b0segs m' ->
      munch WAP me m' -> wmono b0segs me m' ->
      bqat qsp m') ->
    ((ltLo <= gtHi)%Z -> forall m' (nx' : nxt),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - (gtHi - unHi) + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1'' := mvswap (S (Z.to_nat mm)) a1' unLo (hi - mm + 1) mm in
      u8arr b0segs m' A1 (zb8 a1'' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr b0segs m' SHI (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr b0segs m' SD (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      rw_cells b0segs m' P (SLK w240 w248 w264 w272 (Z_to_bv 64 (qsp + 2)) w328 w336 w344 w352 (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> mem_inv b0segs m' -> munch WAP me m' -> wmono b0segs me m' ->
      zbok a1'' -> pr n a1'' 0 (n - 1) ->
      bfree_at X Y Q 0xa38bc m') ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 unHi) (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + 4 * lo)) x11 x12 (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) (Z_to_bv 64 unLo) x17
                          x18 x19 (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 A2) (Z_to_bv 64 NA2) (Z_to_bv 64 NSLO) (Z_to_bv 64 d) (Z_to_bv 64 (SD + 4 * (qsp - 1))) (Z_to_bv 64 qsp) cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2a6c) fc None m (seg_rom b0segs)).
  Proof.
    intros lo hi d ltLo unLo unHi gtHi qsp SHl SHh SHd a1 a2 slo shi sd Jlo Jhi Jd w240 w248 w264 w272 w312 w328 w336 w344 w352 nx
           x11 x12 x17 x18 x19 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgt Hhi Hd Hq ASl ASh ASd LJlo LJhi LJd A1OK PR AR1 AR2 SLOB SHIB SDB SLB NX MI MU WM SH1 SHZl SHZh SHZd KA KB.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_SLO X Y YSX) as AS1l. pose proof (amsx_1_SHI X Y YSX) as AS1h. pose proof (amsx_1_SD X Y YSX) as AS1d.
    pose proof (amsx_2_SLO X Y YSX) as AS2l. pose proof (amsx_2_SHI X Y YSX) as AS2h. pose proof (amsx_2_SD X Y YSX) as AS2d. box_ors.
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *) clear KA. specialize (KB ltac:(lia)). cbv zeta in KB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq0 end.
      enter_with (B0_qswap1 X Y SHF SHn Q XOK YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo hi ltLo unLo unHi gtHi a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq0 mq0);
        [st_eq| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact SLB| exact MI| apply munch_refl| apply wmono_refl| sub_shz SH1 MU|].
      intros m1 z10 z11 z12 z17 z28 z29 z30 z31. cbv zeta. intros AR1_1 SLB1 MI1 MU1 WM1 OK1 PR1.
      clear AR1 SLB MI. transport_after_call b0segs mq0 m1 MU1 WM1. clear MU1 WM1.
      enter_with (B0_qswap2 X Y SHF SHn Q XOK YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo hi ltLo unLo unHi gtHi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 m1);
        [st_eq| lia| lia| lia| lia| lia| exact OK1| exact PR1| exact AR1_1| exact SLB1| exact MI1| apply munch_refl| apply wmono_refl| sub_shz SH1 MU|].
      intros m2 v5 v6 v10 v11 v17 v28 v29 v30. cbv zeta. intros AR1_2 SLB2 MI2 MU2 WM2 OK2 PR2.
      clear AR1_1 SLB1 MI1. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      enter_with (B0_qnext X Y SHF SHn Q XOK YOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo hi d ltLo unLo (gtHi - unHi)%Z qsp SHl SHh SHd slo shi sd Jlo Jhi Jd _ nx _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 m2);
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact ASl| exact ASh| exact ASd| exact LJlo| exact LJhi| exact LJd| exact SLOB| exact SHIB| exact SDB| exact SLB2| exact NX| exact MI2
        | apply munch_refl| apply wmono_refl| sub_shz SHZl MU| sub_shz SHZh MU| sub_shz SHZd MU|].
      intros m3 u0 u1 u2 u3 u4 u5 u6 u7 u8. cbv zeta.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [f0 f1] eqn:E1 end; cbv beta iota.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [g1 g2] eqn:E2 end; cbv beta iota.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [h0 h1] eqn:E3 end; cbv beta iota.
      destruct h0 as [[l0 hh0] d0]. destruct h1 as [[l1 hh1] d1]. destruct g2 as [[l2 hh2] d2]. cbv beta iota in KB.
      intros SLO3 SHI3 SD3 SLB3 NX3 MI3 MU3 WM3.
      clear SLOB SHIB SDB SLB2 NX MI2. bz_params.
      transport_after_call b0segs m2 m3 MU3 WM3. clear MU3 WM3.
      eapply (KB m3 _); [exact AR1_2| exact AR2| exact SLO3| exact SHI3| exact SD3| exact SLB3| exact NX3| exact MI3| exact MU| exact WM| exact OK2| exact PR2].
    - (* [comment removed for export] *)
      clear KB. specialize (KA ltac:(lia)). open_slb_in SLB. open_nx_in NX.
      brun. st_stk SDB (qsp - 1)%Z (d + 1)%Z.
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (KA mm AR1 AR2 SLOB SHIB SDB SLB NX ltac:(assumption) MU WM) as KK end.
      unfold bqat in KK. enter_with KK. st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  Lemma ovw_zset_same : forall a i J nn, zdef a i = true -> ovw (zset a i (zget a i)) J nn = ovw a J nn.
  Proof.
    intros a i J nn D. apply ovw_ext. intros k Hk. rewrite zdef_zset, zget_zset.
    destruct (Z.eqb_spec k i); [subst; rewrite D; split; reflexivity| split; reflexivity].
  Qed.

  Ltac rdstk ARR idx DEF :=
    lazymatch type of ARR with u32arr ?segs ?mm ?A (ovw ?a ?J ?nn) =>
      let RD := fresh "RD" in
      pose proof (ovw_read segs mm A a J nn idx _ ARR ltac:(lia) DEF ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z_signed (zget a idx)) by lia
    end.

  (* [comment removed for export] *)
  Definition qviews (me : word -> option byte) : Prop :=
    acoW WQA me /\ shzW b0segs WQA me A1 (A1 + ARR1_SIZE) /\ shzW b0segs WQA me A2 (A2 + ARR2_SIZE) /\ shpW b0segs WQA me (P + 496) (P + 500) /\
    shzW b0segs WQA me 858336 858392 /\
    shzW b0segs WQA me SLO (SLO + 400) /\ shzW b0segs WQA me SHI (SHI + 400) /\ shzW b0segs WQA me SD (SD + 400).

  (* [comment removed for export] *)
  Lemma B0_iter : forall (qsp b lo hi d : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte)
      (w240 w248 w264 w272 w328 w336 w344 w352 w408 w416 : word) (e312 e392 e440 : Z) (nx : nxt) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    zget slo (qsp - 1) = lo -> zget shi (qsp - 1) = hi -> zget sd (qsp - 1) = d ->
    (1 <= qsp <= 51)%Z -> (0 <= lo)%Z -> (lo <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= b < 2147483648)%Z ->
    ((hi - lo < 20 \/ 14 < d)%Z -> (-2147483648 < snd (mainSimpleSort a1 a2 qo n lo hi d b))%Z) ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr b0segs m SLO (ovw slo Jlo 100) -> u32arr b0segs m SHI (ovw shi Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLK w240 w248 w264 w272 (Z_to_bv 64 e312) w328 w336 w344 w352 (Z_to_bv 64 e392) w408 w416 (Z_to_bv 64 e440)) ->
    (e312 = qsp - 1 /\ e392 = SHI + 4 * (qsp - 1) /\ e440 = SLO + 4 * (qsp - 1))%Z ->
    rw_cells b0segs m (P + 500) (nxt_cells nx) -> rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m -> b0_incs m ->
    munch WQA me m -> wmono b0segs me m -> qviews me ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' : zarr),
      ITER a2 qo n q = MQS a1' qsp slo' shi' sd' nlo nhi nd b false ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      (forall i, 0 <= i < qsp -> zdef slo' i = true /\ zdef shi' i = true /\ zdef sd' i = true)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw slo' Jlo 100) -> u32arr b0segs m' SHI (ovw shi' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLK w240 w248 w264 w272 (Z_to_bv 64 (qsp - 1)) w328 w336 w344 w352 (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (SLO + 4 * (qsp - 1)))) ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx) -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQA me m' -> wmono b0segs me m' ->
      bqat qsp m') ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (w240' w248' w264' w272' w328' w336' w344' w352' w392' w408' w416' w440' : word) (nx' : nxt),
      ITER a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z -> (0 <= qsp')%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      (forall i, 0 <= i < qsp' -> zdef slo' i = true /\ zdef shi' i = true /\ zdef sd' i = true)%Z ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw slo' Jlo 100) -> u32arr b0segs m' SHI (ovw shi' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLK w240' w248' w264' w272' (Z_to_bv 64 qsp') w328' w336' w344' w352' w392' w408' w416' w440') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQA me m' -> wmono b0segs me m' ->
      bfree_at X Y Q 0xa38bc m') ->
    (* [comment removed for export] *)
    (forall m' (a1' : zarr) (b' : Z) (w240' w248' w264' w272' w328' w336' w344' w352' w392' w408' w416' w440' : word),
      ITER a2 qo n q = MQS a1' (qsp - 1) slo shi sd nlo nhi nd b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw slo Jlo 100) -> u32arr b0segs m' SHI (ovw shi Jhi 100) -> u32arr b0segs m' SD (ovw sd Jd 100) ->
      rw_cells b0segs m' P (SLK w240' w248' w264' w272' (Z_to_bv 64 (qsp - 1)) w328' w336' w344' w352' w392' w408' w416' w440') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx) -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQA me m' -> wmono b0segs me m' ->
      bfree_at X Y Q 0xa3970 m') ->
    bqat qsp m.
  Proof.
    intros qsp b lo hi d a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd w240 w248 w264 w272 w328 w336 w344 w352 w408 w416 e312 e392 e440 nx me m.
    intros q Elo Ehi Ed Hq Hlo Hlh Hhi Hd Hb BFIN A1OK A2OK PR DEF LJlo LJhi LJd AR1 AR2 SLOB SHIB SDB SLB EE NX BUD STK MI IB MU WM QV KA KB KC. subst q.
    destruct EE as (-> & -> & ->).
    destruct QV as (ACW & SH1 & SH2 & SHB & SHINC & SHZl & SHZh & SHZd).
    unfold bqat. intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x24 x28 x29 x30 x31.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_SLO X Y YSX) as AP1a. pose proof (amsx_1_SHI X Y YSX) as AP1b. pose proof (amsx_1_SD X Y YSX) as AP1c.
    pose proof (amsx_2_SLO X Y YSX) as AP2a. pose proof (amsx_2_SHI X Y YSX) as AP2b. pose proof (amsx_2_SD X Y YSX) as AP2c. box_ors.
    bz_params. pose proof alloc_ceiling_range as ACR.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    cps_destruct (DEF (qsp - 1)%Z ltac:(lia)) as (Dlo & Dhi & Dd).
    open_slb_in SLB. unfold b0_incs, B0_INCS in IB.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    (* [comment removed for export] *)
    brun. rdstk SLOB (qsp - 1)%Z Dlo. rewrite Elo.
    (* [comment removed for export] *)
    brun_to 0xa2528%Z. rdstk SHIB (qsp - 1)%Z Dhi. rewrite Ehi.
    (* [comment removed for export] *)
    brun_to 0xa2548%Z. rdstk SDB (qsp - 1)%Z Dd. rewrite Ed.
    (* [comment removed for export] *)
    pose proof (saddr_intro (SLO + 4 * (qsp - 1))) as ASl. set (SHl := ((SLO + 4 * (qsp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHl.
    pose proof (saddr_intro (SHI + 4 * (qsp - 1))) as ASh. set (SHh := ((SHI + 4 * (qsp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHh.
    pose proof (saddr_intro (SD + 4 * (qsp - 1))) as ASd. set (SHd := ((SD + 4 * (qsp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHd.
    (* [comment removed for export] *)
    brun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    assert (LEAF : (hi - lo < 20 \/ 14 < d)%Z -> forall y11,
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (hi - lo)) y11 (Z_to_bv 64 hi) (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) x16 x17
                          x18 x19 (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 A2) (Z_to_bv 64 NA2) (Z_to_bv 64 NSLO) (Z_to_bv 64 d) (Z_to_bv 64 (SD + 4 * (qsp - 1))) (Z_to_bv 64 qsp) cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa2b30) fc None mq (seg_rom b0segs))).
    { intros Hleaf y11. specialize (BFIN Hleaf). clear KA.
      pose proof (ITER_leaf a2 qo n a1 qsp slo shi sd nlo nhi nd b) as IL. cbv zeta in IL. rewrite !Elo, !Ehi, !Ed in IL.
      specialize (IL ltac:(apply Bool.orb_true_iff; destruct Hleaf; [left | right]; apply Z.ltb_lt; lia)).
      enter_with (B0_mss X Y SHF SHn Q XOK XSEP YOK _ _ _ _ _ _ _ _ _ _ _ _ d lo hi a1 a2 b _ _ _ _ _ _ _ _ _ _
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq mq);
        [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| exact BFIN| lia| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact IB
        | apply munch_refl| apply wmono_refl| sub_aco ACW MU| sub_shz SH1 MU| sub_shz SH2 MU| sub_shp SHB MU| sub_shz SHINC MU| |].
      - intros m' w240' w248' w264' w272' w328' w336' w344' w352' w392' w440'. cbv zeta.
        intros Hb' AR1' AR2' SLB' BUD' STK' MI' IB' MU' WM' OK' PR' LE'.
        clear AR1 AR2 SLB BUD STK MI IB. bz_params. transport_after_call b0segs mq m' MU' WM'. clear MU' WM'.
        eapply (KB m' (fst (mainSimpleSort a1 a2 qo n lo hi d b)) slo shi sd nlo nhi nd (qsp - 1)%Z (snd (mainSimpleSort a1 a2 qo n lo hi d b))
                   w240' w248' w264' w272' w328' w336' w344' w352' w392' _ _ w440' nx);
          [ | lia| lia| exact OK'| exact PR'| | exact AR1'| exact AR2'| exact SLOB| exact SHIB| exact SDB| exact SLB'| exact NX| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU| exact WM].
        + rewrite IL. replace (snd (mainSimpleSort a1 a2 qo n lo hi d b) <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        + intros i Hi. apply DEF. lia.
      - intros m' w240' w248' w264' w272' w328' w336' w344' w352' w392' w440'. cbv zeta.
        intros Hb' AR1' AR2' SLB' BUD' STK' MI' IB' MU' WM' OK' PR' LE'.
        clear AR1 AR2 SLB BUD STK MI IB. bz_params. transport_after_call b0segs mq m' MU' WM'. clear MU' WM'.
        eapply (KC m' (fst (mainSimpleSort a1 a2 qo n lo hi d b)) (snd (mainSimpleSort a1 a2 qo n lo hi d b))
                   w240' w248' w264' w272' w328' w336' w344' w352' w392' _ _ w440');
          [ | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLOB| exact SHIB| exact SDB| exact SLB'| exact NX| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU| exact WM].
        rewrite IL. replace (snd (mainSimpleSort a1 a2 qo n lo hi d b) <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    if_cases Kc1; zify_cond_z Kc1.
    { enter_with (LEAF ltac:(lia) _). st_eq. }
    brun. if_cases Kc2; zify_cond_z Kc2.
    { enter_with (LEAF ltac:(lia) _). st_eq. }
    clear LEAF BFIN.
    enter_with (B0_med lo hi d a1 a2 _ _ _ _ _ _ _ _ _ _ _ WQA me _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq);
      [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| exact AR1| exact AR2| exact SLB| exact MI| exact MU| exact SH1| exact SH2|].
    intros med y5 y11 y12 y16 Hmed Hmr.
    pose proof (ITER_part a2 a1 qsp slo shi sd nlo nhi nd b med) as IP. cbv zeta in IP. rewrite !Elo, !Ehi, !Ed in IP.
    cps_destruct (IP Hlo ltac:(lia) Hmed) as (Epp & P1 & P2 & P3 & P4 & P5). clear IP.
    (* [comment removed for export] *)
    brun. if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    enter_with (B0_part X Y Q XOK XSEP YOK lo hi d med (Z.to_nat (hi - lo + 1)) a2 _ _ _ _ _ _ _ _ _
                  (S (Z.to_nat (hi - lo + 1))) lo hi lo hi a1 _ _ _ _ _ _ _ mq mq);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| exact MI| apply munch_refl| apply wmono_refl| sub_shz SH1 MU| sub_shz SH2 MU|].
    intros m1 z11 z12 z18 z28 z29 z30 z31. cbv zeta. intros AR1_1 AR2_1 MI1 MU1 WM1 OK1 PR1 B1 B2 B3.
    clear AR1 AR2 MI. bz_params. transport_after_call b0segs mq m1 MU1 WM1. clear MU1 WM1.
    set (pp := mpart_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) a2 d med (MP a1 lo hi lo hi)) in *.
    enter_with (B0_apart lo hi d (mp_ltLo pp) (mp_unLo pp) (mp_unHi pp) (mp_gtHi pp) qsp SHl SHh SHd (mp_a1 pp) a2 slo shi sd Jlo Jhi Jd
                  _ _ _ _ _ _ _ _ _ nx _ _ _ _ _ _ _ _ _ m1 m1);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact ASl| exact ASh| exact ASd| exact LJlo| exact LJhi| exact LJd| exact OK1| exact PR1| exact AR1_1| exact AR2_1
      | exact SLOB| exact SHIB| exact SDB| exact SLB| exact NX| exact MI1| apply munch_refl| apply wmono_refl| sub_shz SH1 MU| sub_shz SHZl MU| sub_shz SHZh MU| sub_shz SHZd MU| |].
    - (* [comment removed for export] *) intros Hlt m2 AR1_2 AR2_2 SLO2 SHI2 SD2 SLB2 NX2 MI2 MU2 WM2. clear KB KC.
      clear SLOB SHIB SDB SLB NX AR1_1 AR2_1 MI1. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      rewrite <- (ovw_zset_same slo (qsp - 1) Jlo 100 Dlo), Elo in SLO2. rewrite <- (ovw_zset_same shi (qsp - 1) Jhi 100 Dhi), Ehi in SHI2.
      eapply (KA m2 (mp_a1 pp) (zset slo (qsp - 1) lo) (zset shi (qsp - 1) hi) (zset sd (qsp - 1) (d + 1)));
        [ | exact OK1| exact PR1| | exact AR1_2| exact AR2_2| exact SLO2| exact SHI2| exact SD2| exact SLB2| exact NX2| exact BUD| exact STK| exact MI2| exact IB| exact MU| exact WM].
      + pose proof (ITER_repush a2 qo n a1 qsp slo shi sd nlo nhi nd b pp) as IR. cbv zeta in IR. rewrite !Elo, !Ehi, !Ed in IR.
        apply IR; [| exact Epp| lia]. apply Bool.orb_false_iff; split; apply Z.ltb_ge; lia.
      + intros i Hi. rewrite !zdef_zset. cps_destruct (DEF i Hi) as (D1 & D2 & D3). rewrite D1, D2, D3, !Bool.orb_true_r. CmpFast.tauto_g.
    - (* [comment removed for export] *) intros Hle m2 nx2. clear KA KC. cbv zeta.
      pose proof (iter_push_shape a1 qsp slo shi sd nlo nhi nd b pp) as PS. cbv zeta in PS. rewrite !Elo, !Ehi, !Ed in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [f0 f1] eqn:E1 end; cbv beta iota; cbv beta iota in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [g1 g2] eqn:E2 end; cbv beta iota; cbv beta iota in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [h0 h1] eqn:E3 end; cbv beta iota; cbv beta iota in PS.
      destruct h0 as [[l0 u0] d0]. destruct h1 as [[l1 u1] d1]. destruct g2 as [[l2 u2] d2]. cbv beta iota in PS.
      cps_destruct PS as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
      intros AR1_2 AR2_2 SLO2 SHI2 SD2 SLB2 NX2 MI2 MU2 WM2 OK2 PR2.
      clear SLOB SHIB SDB SLB NX AR1_1 AR2_1 MI1. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      lazymatch type of AR1_2 with u8arr _ _ _ (zb8 ?a1x _) =>
        eapply (KB m2 a1x _ _ _ (mq_nlo (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp))))
                      (mq_nhi (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp))))
                      (mq_nd (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp)))) (qsp + 2)%Z b
                      _ _ _ _ _ _ _ _ _ _ _ _ nx2) end;
        [ | lia| lia| exact OK2| exact PR2| | exact AR1_2| exact AR2_2| exact SLO2| exact SHI2| exact SD2| exact SLB2| exact NX2| exact BUD| exact STK| exact MI2| exact IB| exact MU| exact WM].
      + pose proof (ITER_push3 a2 qo n a1 qsp slo shi sd nlo nhi nd b pp) as I3. cbv zeta in I3. rewrite !Elo, !Ehi, !Ed in I3.
        rewrite (I3 ltac:(apply Bool.orb_false_iff; split; apply Z.ltb_ge; lia) Epp ltac:(lia)).
        rewrite (mqs_eta (PUSH3 _)) at 1. rewrite S1, S2, S3, S4, S5, S6, S7.
        unfold A1V, TOPlo, TOPhi. cbn [mq_a1 mq_sp mq_slo mq_shi mq_sd]. rewrite !Elo, !Ehi. reflexivity.
      + intros i Hi. rewrite !zdef_zset.
        destruct (Z.ltb_spec i (qsp - 1)).
        * cps_destruct (DEF i ltac:(lia)) as (D1 & D2 & D3). rewrite D1, D2, D3, !Bool.orb_true_r. CmpFast.tauto_g.
        * destruct (Z.eqb_spec i (qsp + 1)); [cbn [orb]; CmpFast.tauto_g|]. destruct (Z.eqb_spec i qsp); [cbn [orb]; CmpFast.tauto_g|].
          destruct (Z.eqb_spec i (qsp - 1)); [cbn [orb]; CmpFast.tauto_g|]. exfalso; lia.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_qloop : forall (f : nat) (qsp b : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte)
      (w240 w248 w264 w272 w328 w336 w344 w352 w408 w416 : word) (e312 e392 e440 : Z) (nx : nxt) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    (1 <= qsp)%Z -> (0 <= b < 2147483648)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop f a2 qo n q) <= 0 \/ mq_exit (mqs_loop f a2 qo n q) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr b0segs m SLO (ovw slo Jlo 100) -> u32arr b0segs m SHI (ovw shi Jhi 100) -> u32arr b0segs m SD (ovw sd Jd 100) ->
    rw_cells b0segs m P (SLK w240 w248 w264 w272 (Z_to_bv 64 e312) w328 w336 w344 w352 (Z_to_bv 64 e392) w408 w416 (Z_to_bv 64 e440)) ->
    (e312 = qsp - 1 /\ e392 = SHI + 4 * (qsp - 1) /\ e440 = SLO + 4 * (qsp - 1))%Z ->
    rw_cells b0segs m (P + 500) (nxt_cells nx) -> rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m -> b0_incs m ->
    munch WQA me m -> wmono b0segs me m -> qviews me ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (b' : Z) (w240' w248' w264' w272' w328' w336' w344' w352' w392' w408' w416' w440' : word) (nx' : nxt),
      mqs_loop f a2 qo n q = MQS a1' 0 slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw slo' Jlo 100) -> u32arr b0segs m' SHI (ovw shi' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLK w240' w248' w264' w272' (Z_to_bv 64 0) w328' w336' w344' w352' w392' w408' w416' w440') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQA me m' -> wmono b0segs me m' ->
      bfree_at X Y Q 0xa3970 m') ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (w312' : word) (w240' w248' w264' w272' w328' w336' w344' w352' w392' w408' w416' w440' : word) (nx' : nxt),
      mqs_loop f a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr b0segs m' SLO (ovw slo' Jlo 100) -> u32arr b0segs m' SHI (ovw shi' Jhi 100) -> u32arr b0segs m' SD (ovw sd' Jd 100) ->
      rw_cells b0segs m' P (SLK w240' w248' w264' w272' w312' w328' w336' w344' w352' w392' w408' w416' w440') ->
      rw_cells b0segs m' (P + 500) (nxt_cells nx') -> rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' -> b0_incs m' ->
      munch WQA me m' -> wmono b0segs me m' ->
      bfree_at X Y Q 0xa3970 m') ->
    bqat qsp m.
  Proof.
    induction f as [|f IH].
    { intros qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd w240 w248 w264 w272 w328 w336 w344 w352 w408 w416 e312 e392 e440 nx me m q Hq Hb OKv FIN.
      exfalso. subst q. cbn [mqs_loop mq_sp mq_exit] in FIN. destruct FIN as [FIN|FIN]; [lia| discriminate]. }
    intros qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd w240 w248 w264 w272 w328 w336 w344 w352 w408 w416 e312 e392 e440 nx me m.
    intros q Hq Hb OKv FIN A1OK A2OK PR DEF LJlo LJhi LJd AR1 AR2 SLOB SHIB SDB SLB EE NX BUD STK MI IB MU WM QV Kdone Kexit. subst q.
    msenv_open XOK. amenv_open YOK.
    rewrite mqs_loop_step in FIN, Kdone, Kexit by lia.
    pose proof (OKv 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [mqs_loop] in F0. unfold mqsF in F0. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F0.
    cps_destruct F0 as (Fsp & Flo & Flh & Fhi & Fd & Fbud).
    eapply (B0_iter qsp b (zget slo (qsp - 1)) (zget shi (qsp - 1)) (zget sd (qsp - 1)) a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd
                    w240 w248 w264 w272 w328 w336 w344 w352 w408 w416 e312 e392 e440 nx me m);
      [reflexivity| reflexivity| reflexivity| lia| lia| lia| lia| lia| lia| intros HL; apply Fbud; [exact HL| exact A1OK| exact PR| lia]
      | exact A1OK| exact A2OK| exact PR| exact DEF| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SLB| exact EE| exact NX| exact BUD| exact STK| exact MI| exact IB| exact MU| exact WM| exact QV| | |].
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' EQ OK' PR' DEF' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM'.
      rewrite EQ in FIN, Kdone, Kexit.
      eapply (IH qsp b a1' a2 slo' shi' sd' nlo nhi nd Jlo Jhi Jd _ _ _ _ _ _ _ _ _ _ _ _ _ nx me m');
        [lia| lia| | exact FIN| exact OK'| exact A2OK| exact PR'| exact DEF'| exact LJlo| exact LJhi| exact LJd
        | exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SLB'| repeat split; reflexivity| exact NX'| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU'| exact WM'| exact QV
        | exact Kdone | exact Kexit].
      intros v. pose proof (OKv (S v)) as O. cbv zeta in O. rewrite mqs_loop_step in O by lia. rewrite EQ in O. exact O.
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' v240 v248 v264 v272 v328 v336 v344 v352 v392 v408 v416 v440 nx'.
      intros EQ Hb' Hq' OK' PR' DEF' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM'.
      rewrite EQ in FIN, Kdone, Kexit.
      assert (OKv' : forall v, let q' := mqs_loop v a2 qo n (MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' false) in
                       (0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z).
      { intros v. pose proof (OKv (S v)) as O. cbv zeta in O. rewrite mqs_loop_step in O by lia. rewrite EQ in O. exact O. }
      clear OKv EQ AR1 AR2 SLOB SHIB SDB SLB NX BUD STK MI IB MU WM DEF.
      pose proof (zb8_length a1' ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
      pose proof (ovw_length slo' Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi' Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd' Jd 100 ltac:(lia)) as Ld.
      assert (Hq51 : (qsp' <= 51)%Z).
      { destruct (Z_le_gt_dec qsp' 0); [lia|]. pose proof (OKv' 0%nat ltac:(cbn; lia) eq_refl) as F1. cbn [mqs_loop] in F1.
        unfold mqsF in F1. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F1. destruct F1 as (Fsp' & _). exact Fsp'. }
      unfold bfree_at. intros. open_slb_in SLB'. unfold b0_incs, B0_INCS in IB'.
      (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
      + (* [comment removed for export] *)
        assert (qsp' = 0)%Z as Z0 by lia. subst qsp'.
        rewrite (mqs_loop_halt f) in Kdone by (cbn; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (Kdone mm a1' slo' shi' sd' nlo' nhi' nd' b' _ _ _ _ _ _ _ _ _ _ _ _ nx' eq_refl ltac:(lia) OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM') as KK end.
        unfold bfree_at in KK. enter_with KK. st_eq.
      + (* [comment removed for export] *)
        brun_to 0xa24a4%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (BQ : bqat qsp' mm) end.
        { eapply (IH qsp' b' a1' a2 slo' shi' sd' nlo' nhi' nd' Jlo Jhi Jd _ _ _ _ _ _ _ _ _ _ _ _ _ nx' me);
            [lia| lia| exact OKv'| exact FIN| exact OK'| exact A2OK| exact PR'| exact DEF'| exact LJlo| exact LJhi| exact LJd
            | exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SLB'| repeat split; lia| exact NX'| exact BUD'| exact STK'| exact MI'| exact IB'| assumption| assumption| exact QV| | ].
          * intros m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' b'' u240 u248 u264 u272 u328 u336 u344 u352 u392 u408 u416 u440 nx''.
            intros EQf Hb'' OK'' PR'' AR1'' AR2'' SLO'' SHI'' SD'' SLB'' NX'' BUD'' STK'' MI'' IB'' MU'' WM''.
            eapply (Kdone m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' b'' u240 u248 u264 u272 u328 u336 u344 u352 u392 u408 u416 u440 nx'');
              [exact EQf| lia| exact OK''| exact PR''| exact AR1''| exact AR2''| exact SLO''| exact SHI''| exact SD''
              | exact SLB''| exact NX''| exact BUD''| exact STK''| exact MI''| exact IB''| exact MU''| exact WM''].
          * intros m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' qsp'' b'' u312 u240 u248 u264 u272 u328 u336 u344 u352 u392 u408 u416 u440 nx''.
            intros EQf Hb'' OK'' PR'' AR1'' AR2'' SLO'' SHI'' SD'' SLB'' NX'' BUD'' STK'' MI'' IB'' MU'' WM''.
            eapply (Kexit m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' qsp'' b'' u312 u240 u248 u264 u272 u328 u336 u344 u352 u392 u408 u416 u440 nx'');
              [exact EQf| lia| exact OK''| exact PR''| exact AR1''| exact AR2''| exact SLO''| exact SHI''| exact SD''
              | exact SLB''| exact NX''| exact BUD''| exact STK''| exact MI''| exact IB''| exact MU''| exact WM'']. }
        unfold bqat in BQ. enter_with BQ. st_eq.
    - (* [comment removed for export] *)
      intros m' a1' b' v240 v248 v264 v272 v328 v336 v344 v352 v392 v408 v416 v440.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SLB' NX' BUD' STK' MI' IB' MU' WM'.
      rewrite EQ in Kexit. rewrite (mqs_loop_halt f) in Kexit by (cbn; right; reflexivity).
      eapply (Kexit m' a1' slo shi sd nlo nhi nd (qsp - 1)%Z b' _ v240 v248 v264 v272 v328 v336 v344 v352 v392 v408 v416 v440 nx);
        [reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SLB'| exact NX'| exact BUD'| exact STK'| exact MI'| exact IB'| exact MU'| exact WM'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0MS.
End ACeilS1.
