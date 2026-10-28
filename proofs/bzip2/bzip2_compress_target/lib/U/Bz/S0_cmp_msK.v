(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import MuslStr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs CmpCutMS CmpMsKit S0_cmp_gtu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasMs2 BzCLemmasMs3 CmpMsKit2 S0_cmp_msV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_msH.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_msH.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_msJ.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_msJ.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_msE.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_msE S0_cmp_msF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzIncs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require UKit.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasMs3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msV OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msH OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msJ.S0_cmp_msI OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msJ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msE.S0_cmp_msD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_msF.
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
  Notation NA2 := (18446744073709551615 - me_A2 X)%Z.
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

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

  Ltac med_run_to pc :=
    first [ UKit.u_at_pc pc
          | UKit.u_pc_is_lit; let R := UKit.u_regs in wstep; rewrite ?zext32_id; UKit.u_flags R; UKit.u_try_lit_branch; UKit.u_try_guard; med_run_to pc
          | lazymatch goal with |- evt _ _ (MS _ _ ?q _ _ _ _) => idtac "med_run_to: stopped at" q end; fail 1 ].

  (* [comment removed for export] *)
  Lemma S0_med : forall (lo hi d : Z) (a1 a2 : zarr)
      (xra x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x26 x27 x28 x31 : word) (m : word -> option byte),
    (0 <= lo)%Z -> (lo + 20 <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv s0segs m ->
    (forall (med : Z) (x11' : word),
      med = mmed3 (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d)) -> (0 <= med < 256)%Z ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 NA2)
                            (Z_to_bv 64 (A1 + 4 * lo)) x11' (Z_to_bv 64 hi) (Z_to_bv 64 med) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 lo) x17
                            (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 x22 x23 (Z_to_bv 64 d) x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                       F (Z_to_bv 64 0x21100) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 NA2)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 x22 x23 (Z_to_bv 64 d) x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x20fbc) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d a1 a2 xra x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x25 x26 x27 x28 x31 m
           Hlo Hlh Hhi Hd A1OK A2OK PR AR1 AR2 MI K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR lo ltac:(lia)) as Pl. set (pl := rd32 a1 lo) in *. assert (Epl : rd32 a1 lo = pl) by reflexivity. clearbody pl.
    pose proof (PR hi ltac:(lia)) as Ph. set (ph := rd32 a1 hi) in *. assert (Eph : rd32 a1 hi = ph) by reflexivity. clearbody ph.
    set (mid := Z.shiftr (lo + hi) 1) in *.
    assert (Hmid : mid = ((lo + hi) / 2)%Z) by (subst mid; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (Hmid2 : (lo <= mid <= hi)%Z) by (rewrite Hmid; Z.div_mod_to_equations; lia).
    pose proof (PR mid ltac:(lia)) as Pm. set (pm := rd32 a1 mid) in *. assert (Epm : rd32 a1 mid = pm) by reflexivity. clearbody pm.
    (* [comment removed for export] *)
    med_run_to 0x20ff0%Z. rdptr AR1 A1OK lo. rewrite Epl.
    med_run_to 0x2103c%Z. rdptr AR1 A1OK hi. rewrite Eph.
    (* [comment removed for export] *)
    med_run_to 0x21068%Z.
    rewrite <- ?Hmid. clearbody mid.
    med_run_to 0x2109c%Z. rdptr AR1 A1OK mid. rewrite Epm.
    (* [comment removed for export] *)
    med_run_to 0x210bc%Z. rdblk AR2 A2OK (pl + d)%Z. rdblk AR2 A2OK (ph + d)%Z.
    unfold rd8 in K. set (c0 := zget a2 (pl + d)) in *. set (c1 := zget a2 (ph + d)) in *. clearbody c0 c1.
    (* [comment removed for export] *)
    assert (JOIN1 : forall y15,
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 (Z_to_bv 64 NA2)
                          (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 (if c1 <? c0 then c0 else c1)) (Z_to_bv 64 c1) (Z_to_bv 64 (if c1 <? c0 then c1 else c0)) (Z_to_bv 64 (pm + d)) y15 x16 x17
                          (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 x22 x23 (Z_to_bv 64 d) x25 x26 x27 x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x210d8) fc None m (seg_rom s0segs))).
    2:{ wstep. wstep; if_cases Kc1; zify_cond_z Kc1.
        - (* [comment removed for export] *)
          wstep; if_cases Kc2; zify_cond_z Kc2; [exfalso; lia|]. wstep.
          enter_with (JOIN1 _). all: replace (c1 <? c0) with true by (symmetry; apply Z.ltb_lt; lia); st_eq.
        - wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
          + enter_with (JOIN1 _). all: replace (c1 <? c0) with false by (symmetry; apply Z.ltb_ge; lia); st_eq.
          + (* [comment removed for export] *) wstep. enter_with (JOIN1 _). all: replace (c1 <? c0) with false by (symmetry; apply Z.ltb_ge; lia); st_eq. }
    intros y15.
    set (mx := if c1 <? c0 then c0 else c1) in *. set (mn := if c1 <? c0 then c1 else c0) in *.
    assert (Hmx : (0 <= mx < 256)%Z) by (subst mx; destruct (c1 <? c0); lia).
    assert (Hmn : (0 <= mn < 256)%Z) by (subst mn; destruct (c1 <? c0); lia).
    assert (Hmnx : (mn <= mx)%Z) by (subst mn mx; destruct (Z.ltb_spec c1 c0); lia).
    (* [comment removed for export] *)
    wstep. rdblk AR2 A2OK (pm + d)%Z.
    set (c2 := zget a2 (pm + d)) in *. clearbody c2.
    (* [comment removed for export] *)
    assert (MED : forall med, (med = if c2 <? mx then (if c2 <? mn then mn else c2) else mx)%Z ->
              med = mmed3 c0 c1 c2 /\ (0 <= med < 256)%Z).
    { intros med ->. unfold mmed3. subst mx mn. destruct (Z.ltb_spec c1 c0); destruct (Z.ltb_spec c2 c0); destruct (Z.ltb_spec c2 c1); split; try reflexivity; lia. }
    wstep; if_cases Kc3; zify_cond_z Kc3.
    - wstep; if_cases Kc4; zify_cond_z Kc4; [|exfalso; lia].
      med_run_to 0x21100%Z.
      destruct (MED mn) as [E1 E2]; [replace (c2 <? mx) with true by (symmetry; apply Z.ltb_lt; lia); replace (c2 <? mn) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
      enter_with (K mn _ E1 E2). st_eq.
    - wstep. wstep; if_cases Kc4; zify_cond_z Kc4.
      + med_run_to 0x21100%Z.
        destruct (MED c2) as [E1 E2]; [replace (c2 <? mx) with true by (symmetry; apply Z.ltb_lt; lia); replace (c2 <? mn) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
        enter_with (K c2 _ E1 E2). st_eq.
      + wstep. med_run_to 0x21100%Z.
        destruct (MED mx) as [E1 E2]; [replace (c2 <? mx) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
        enter_with (K mx _ E1 E2). st_eq.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
  Definition WQ : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (p + 120, p + 340); (p + 3668, p + 4904)]%Z.

  (* [comment removed for export] *)
  Lemma S0_apart : forall (lo hi d ltLo unLo unHi gtHi qsp b : Z) (a1 a2 : zarr) (slo shi sd : zarr) (Jlo Jhi Jd : list byte) (nx : list word) (sb : scb)
      (xra x5 x6 x7 x13 x16 x17 x28 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 51)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr s0segs m (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    munch WQ me m -> wmono s0segs me m ->
    ((gtHi < ltLo)%Z -> forall m' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 : word),
      u8arr s0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi Jhi 100) ->
      u32arr s0segs m' (p + 3704) (ovw (zset sd (qsp - 1) (d + 1)) Jd 100) -> u32arr s0segs m' (p + 3668) nx ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m' ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp y5 y6 y7 (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 NA2)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) (Z_to_bv 64 A2) (Z_to_bv 64 2) (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) y24
                            (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1)))
                            y28 y29 y30 y31)
                       F (Z_to_bv 64 0x20f4c) fc None m' (seg_rom s0segs))) ->
    ((ltLo <= gtHi)%Z -> forall m' (nx' : list word) (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - (gtHi - unHi) + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1'' := mvswap (S (Z.to_nat mm)) a1' unLo (hi - mm + 1) mm in
      u8arr s0segs m' A1 (zb8 a1'' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr s0segs m' (p + 4104) (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr s0segs m' (p + 3704) (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) (k144 sb) (k152 sb) (k168 sb) (k176 sb) (k184 sb)
                                       (Z_to_bv 64 (qsp + 2)) (k232 sb) (k240 sb) (k248 sb) (k256 sb) (k288 sb))) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m' -> munch WQ me m' -> wmono s0segs me m' ->
      zbok a1'' -> pr n a1'' 0 (n - 1) ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c0c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 NA2)
                          (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 unLo) (Z_to_bv 64 unHi) x13 (Z_to_bv 64 gtHi) (Z_to_bv 64 ltLo) x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) (Z_to_bv 64 A2) (Z_to_bv 64 2) (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) (Z_to_bv 64 d)
                          (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1)))
                          x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x21324) fc None m (seg_rom s0segs)).
  Proof.
    intros lo hi d ltLo unLo unHi gtHi qsp b a1 a2 slo shi sd Jlo Jhi Jd nx sb xra x5 x6 x7 x13 x16 x17 x28 x31 me m
           Hlo Hlt Hun Hgt Hhi Hd Hq LJlo LJhi LJd LNX A1OK PR AR1 AR2 SLO SHI SD NX SCB BUD MI MU WM KA KB.
    msenv_open XOK. open_sc_in SCB. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. unfold WQ in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    wstep. wstep. rewrite ?sx32_of_Z_signed by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - clear KA. specialize (KB ltac:(lia)). cbv zeta in KB.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_qswap1 X Q XOK lo hi ltLo unLo unHi gtHi a1 sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact SCB| exact MI| apply munch_refl| apply wmono_refl|].
      intros m1 z5 z6 z7 z10 z13 z16 z17 z28. cbv zeta. intros AR1_1 SCB1 MI1 MU1 WM1 OK1 PR1.
      clear AR1 SCB MI. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_qswap2 X Q XOK lo hi ltLo unLo unHi gtHi _ sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| exact OK1| exact PR1| exact AR1_1| exact SCB1| exact MI1| apply munch_refl| apply wmono_refl|].
      intros m2 w5 w6 w7 w12 w13 w14 w16 w17. cbv zeta. intros AR1_2 SCB2 MI2 MU2 WM2 OK2 PR2.
      clear AR1_1 SCB1 MI1. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_qnext X Q XOK lo hi d ltLo unLo (gtHi - unHi)%Z qsp slo shi sd Jlo Jhi Jd nx sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact LJlo| exact LJhi| exact LJd| exact LNX| exact SLO| exact SHI| exact SD| exact NX
        | exact SCB2| exact MI2| apply munch_refl| apply wmono_refl|].
      intros m3 v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v29 nx'. cbv zeta.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [f0 f1] eqn:E1 end; cbv beta iota.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [g1 g2] eqn:E2 end; cbv beta iota.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [h0 h1] eqn:E3 end; cbv beta iota.
      destruct h0 as [[l0 u0] d0]. destruct h1 as [[l1 u1] d1]. destruct g2 as [[l2 u2] d2]. cbv beta iota in KB.
      intros SLO3 SHI3 SD3 LNX3 NX3 SCB3 MI3 MU3 WM3.
      clear SLO SHI SD NX SCB2 MI2. bz_params.
      transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (KB mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1_2| exact AR2| exact SLO3| exact SHI3| exact SD3| exact LNX3| exact NX3| exact SCB3| exact BUD| exact MI3
        | exact MU| exact WM| exact OK2| exact PR2].
    - (* [comment removed for export] *)
      clear KB. specialize (KA ltac:(lia)).
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok s0segs mm (p + 3704) _ (qsp - 1) _ SD ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
      wstep. ovw_store SD (qsp - 1)%Z (d + 1)%Z (apply unsigned_lit_mod32).
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KA mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| assumption| assumption| assumption| assumption| assumption| assumption| | | assumption| exact MU| exact WM].
      { match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end. }
      { match goal with H : rw_cells _ _ (p + 336)%Z _ |- _ => exact H end. }
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

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
  Lemma S0_iter : forall (qsp b lo hi d : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte) (nx : list word) (sb : scb)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    zget slo (qsp - 1) = lo -> zget shi (qsp - 1) = hi -> zget sd (qsp - 1) = d ->
    (1 <= qsp <= 51)%Z -> (0 <= lo)%Z -> (lo <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= b < 2147483648)%Z ->
    ((hi - lo < 20 \/ 14 < d)%Z -> (-2147483648 < snd (mainSimpleSort a1 a2 qo n lo hi d b))%Z) ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    k208 sb = Z_to_bv 64 (qsp - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr s0segs m (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    rw_cells s0segs m 210296 [CB 56 incs_bytes] -> apart A1 ARR1_SIZE 210296 56 ->
    munch WQ me m -> wmono s0segs me m ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' : zarr) (nx' : list word) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 : word),
      ITER a2 qo n q = MQS a1' qsp slo' shi' sd' nlo nhi nd b false ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      (forall i, 0 <= i < qsp -> zdef slo' i = true /\ zdef shi' i = true /\ zdef sd' i = true)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X sb) -> rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m' ->
      rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp y5 y6 y7 (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 NA2)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) (Z_to_bv 64 0) (Z_to_bv 64 A2) (Z_to_bv 64 2) (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) y24
                            (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1)))
                            y28 y29 y30 y31)
                       F (Z_to_bv 64 0x20f4c) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (nx' : list word) (w144' w152' w168' w176' w184' w232' w240' w248' w256' w288' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      ITER a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z -> (0 <= qsp')%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      (forall i, 0 <= i < qsp' -> zdef slo' i = true /\ zdef shi' i = true /\ zdef sd' i = true)%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) w144' w152' w168' w176' w184' (Z_to_bv 64 qsp') w232' w240' w248' w256' w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c0c) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' : zarr) (b' : Z) (w144' w152' w168' w176' w184' w208' w232' w240' w248' w256' w288' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      ITER a2 qo n q = MQS a1' (qsp - 1) slo shi sd nlo nhi nd b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd Jd 100) ->
      u32arr s0segs m' (p + 3668) nx ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) w144' w152' w168' w176' w184' w208' w232' w240' w248' w256' w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 NA2)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) (Z_to_bv 64 A2) (Z_to_bv 64 2) (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) x24
                          (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1)))
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x20f4c) fc None m (seg_rom s0segs)).
  Proof.
    intros qsp b lo hi d a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd nx sb xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 me m.
    intros q Elo Ehi Ed Hq Hlo Hlh Hhi Hd Hb BFIN A1OK A2OK PR DEF K208 LJlo LJhi LJd LNX AR1 AR2 SLO SHI SD NX SCB BUD MI IB API MU WM KA KB KC. subst q.
    msenv_open XOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. pose proof alloc_ceiling_ge as ACG. unfold apart in API. unfold WQ in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    cps_destruct (DEF (qsp - 1)%Z ltac:(lia)) as (Dlo & Dhi & Dd).
    destruct sb as [w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288].
    cbn [k208] in K208. subst w208.
    pose proof SCB as SCBo. open_sc_in SCBo.
    (* [comment removed for export] *)
    UKit.urun_to 0x20f50%Z. wstep; if_true_z.
    UKit.urun_to 0x20f8c%Z.
    (* [comment removed for export] *)
    rdstk SLO (qsp - 1)%Z Dlo. rewrite Elo. rdstk SHI (qsp - 1)%Z Dhi. rewrite Ehi.
    UKit.urun_to 0x20fa4%Z.
    rdstk SD (qsp - 1)%Z Dd. rewrite Ed.
    UKit.urun_to 0x20fb0%Z. clear SCBo.
    assert (LEAF : (hi - lo < 20 \/ 14 < d)%Z -> forall y10 : word,
      evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 NA2)
                          y10 (Z_to_bv 64 (hi - lo)) x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) (Z_to_bv 64 A2) (Z_to_bv 64 2) (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) (Z_to_bv 64 d)
                          (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1)))
                          x28 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x31)
                     F (Z_to_bv 64 0x21344) fc None m (seg_rom s0segs))).
    { intros Hleaf y10. specialize (BFIN Hleaf). clear KA.
      pose proof (ITER_leaf a2 qo n a1 qsp slo shi sd nlo nhi nd b) as IL. cbv zeta in IL. rewrite !Elo, !Ehi, !Ed in IL.
      specialize (IL ltac:(apply Bool.orb_true_iff; destruct Hleaf; [left | right]; apply Z.ltb_lt; lia)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (S0_cmp_msF.S0_mss X Q XOK XSEP d lo hi a1 a2 b w128 w136 w144 w152 w168 w176 w184 (Z_to_bv 64 (qsp - 1)) w232 w240 w248 w256 w288
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| exact BFIN| lia| exact AR1| exact AR2| exact SCB| exact BUD| exact MI| exact IB| exact API
        | apply munch_refl| apply wmono_refl| |].
      - intros m' w144' w152' w168' w176' w184' w232' w240' w248' w256' w288'
               z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z21 z22 z23 z25 z26 z27 z28 z29 z30 z31. cbv zeta.
        intros Hb' AR1' AR2' SCB' BUD' MI' IB' MU' WM' OK' PR' LE'.
        clear AR1 AR2 SCB BUD MI IB. transport_after_call s0segs m m' MU' WM'. clear MU' WM'.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (KB mm (fst (mainSimpleSort a1 a2 qo n lo hi d b)) slo shi sd nlo nhi nd (qsp - 1)%Z (snd (mainSimpleSort a1 a2 qo n lo hi d b)) nx
             w144' w152' w168' w176' w184' w232' w240' w248' w256' w288') end;
          [st_eq| | lia| lia| exact OK'| exact PR'| | exact AR1'| exact AR2'| exact SLO| exact SHI| exact SD| exact LNX| exact NX| exact SCB'| exact BUD'| exact MI'
          | exact IB'| exact MU| exact WM].
        + rewrite IL. replace (snd (mainSimpleSort a1 a2 qo n lo hi d b) <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        + intros i Hi. apply DEF. lia.
      - intros m' w144' w152' w168' w176' w184' w232' w240' w248' w256' w288'
               z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z21 z22 z23 z25 z26 z27 z28 z29 z30 z31. cbv zeta.
        intros Hb' AR1' AR2' SCB' BUD' MI' IB' MU' WM' OK' PR' LE'.
        clear AR1 AR2 SCB BUD MI IB. transport_after_call s0segs m m' MU' WM'. clear MU' WM'.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (KC mm (fst (mainSimpleSort a1 a2 qo n lo hi d b)) (snd (mainSimpleSort a1 a2 qo n lo hi d b))
             w144' w152' w168' w176' w184' (Z_to_bv 64 (qsp - 1)) w232' w240' w248' w256' w288') end;
          [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO| exact SHI| exact SD| exact NX| exact SCB'| exact BUD'| exact MI'
          | exact IB'| exact MU| exact WM].
        rewrite IL. replace (snd (mainSimpleSort a1 a2 qo n lo hi d b) <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    wstep; if_cases Kc1; zify_cond_z Kc1.
    { enter_with (LEAF ltac:(lia) _). st_eq. }
    UKit.urun_to 0x20fb8%Z.
    wstep; if_cases Kc2; zify_cond_z Kc2.
    { enter_with (LEAF ltac:(lia) _). st_eq. }
    clear LEAF BFIN.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_med lo hi d a1 a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
      [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| exact AR1| exact AR2| exact MI|].
    intros med x11' Hmed Hmr.
    pose proof (ITER_part a2 a1 qsp slo shi sd nlo nhi nd b med) as IP. cbv zeta in IP. rewrite !Elo, !Ehi, !Ed in IP.
    cps_destruct (IP Hlo ltac:(lia) Hmed) as (Epp & P1 & P2 & P3 & P4 & P5). clear IP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_part X Q XOK XSEP lo hi d med (Z.to_nat (hi - lo + 1)) a2 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (S (Z.to_nat (hi - lo + 1))) lo hi lo hi a1 _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| exact MI| apply munch_refl| apply wmono_refl|].
    intros m1 z5 z6 z7 z16 z17. cbv zeta. intros AR1_1 AR2_1 MI1 MU1 WM1 OK1 PR1 B1 B2 B3.
    clear AR1 AR2 MI. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    set (pp := mpart_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) a2 d med (MP a1 lo hi lo hi)) in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_apart lo hi d (mp_ltLo pp) (mp_unLo pp) (mp_unHi pp) (mp_gtHi pp) qsp b (mp_a1 pp) a2 slo shi sd Jlo Jhi Jd nx
                    (mkSCB w128 w136 w144 w152 w168 w176 w184 (Z_to_bv 64 (qsp - 1)) w232 w240 w248 w256 w288)
                    _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact LJlo| exact LJhi| exact LJd| exact LNX| exact OK1| exact PR1| exact AR1_1| exact AR2_1
      | exact SLO| exact SHI| exact SD| exact NX| exact SCB| exact BUD| exact MI1| apply munch_refl| apply wmono_refl| |].
    - (* [comment removed for export] *) intros Hlt m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 AR1_2 AR2_2 SLO2 SHI2 SD2 NX2 SCB2 BUD2 MI2 MU2 WM2. clear KB KC.
      clear SLO SHI SD NX SCB BUD AR1_1 AR2_1 MI1. unfold WQ in *. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      rewrite <- (ovw_zset_same slo (qsp - 1) Jlo 100 Dlo), Elo in SLO2. rewrite <- (ovw_zset_same shi (qsp - 1) Jhi 100 Dhi), Ehi in SHI2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (KA mm (mp_a1 pp) (zset slo (qsp - 1) lo) (zset shi (qsp - 1) hi) (zset sd (qsp - 1) (d + 1)) nx) end;
        [st_eq| | exact OK1| exact PR1| | exact AR1_2| exact AR2_2| exact SLO2| exact SHI2| exact SD2| exact LNX| exact NX2| exact SCB2| exact BUD2| exact MI2
        | exact IB| exact MU| exact WM].
      + pose proof (ITER_repush a2 qo n a1 qsp slo shi sd nlo nhi nd b pp) as IR. cbv zeta in IR. rewrite !Elo, !Ehi, !Ed in IR.
        apply IR; [| exact Epp| lia]. apply Bool.orb_false_iff; split; apply Z.ltb_ge; lia.
      + intros i Hi. rewrite !zdef_zset. cps_destruct (DEF i Hi) as (D1 & D2 & D3). rewrite D1, D2, D3, !Bool.orb_true_r. CmpFast.tauto_g.
    - (* [comment removed for export] *) intros Hle m2 nx' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31. clear KA KC. cbv zeta.
      pose proof (iter_push_shape a1 qsp slo shi sd nlo nhi nd b pp) as PS. cbv zeta in PS. rewrite !Elo, !Ehi, !Ed in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [f0 f1] eqn:E1 end; cbv beta iota; cbv beta iota in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [g1 g2] eqn:E2 end; cbv beta iota; cbv beta iota in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [h0 h1] eqn:E3 end; cbv beta iota; cbv beta iota in PS.
      destruct h0 as [[l0 u0] d0]. destruct h1 as [[l1 u1] d1]. destruct g2 as [[l2 u2] d2]. cbv beta iota in PS.
      cps_destruct PS as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
      intros AR1_2 AR2_2 SLO2 SHI2 SD2 LNX2 NX2 SCB2 BUD2 MI2 MU2 WM2 OK2 PR2.
      clear SLO SHI SD NX SCB BUD AR1_1 AR2_1 MI1. unfold WQ in *. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
      lazymatch type of AR1_2 with u8arr _ _ _ (zb8 ?a1x _) =>
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (KB mm a1x _ _ _ (mq_nlo (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp))))
                      (mq_nhi (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp))))
                      (mq_nd (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp)))) (qsp + 2)%Z b nx'
                      w144 w152 w168 w176 w184 w232 w240 w248 w256 w288) end end;
        [st_eq| | lia| lia| exact OK2| exact PR2| | exact AR1_2| exact AR2_2| exact SLO2| exact SHI2| exact SD2| exact LNX2| exact NX2| exact SCB2| exact BUD2| exact MI2
        | exact IB| exact MU| exact WM].
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
  Lemma S0_qloopH : forall (f : nat) (qsp b : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte) (nx : list word) (sb : scb)
      (xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    (1 <= qsp)%Z -> (0 <= b < 2147483648)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop f a2 qo n q) <= 0 \/ mq_exit (mqs_loop f a2 qo n q) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    k208 sb = Z_to_bv 64 (qsp - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr s0segs m (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    rw_cells s0segs m 210296 [CB 56 incs_bytes] -> apart A1 ARR1_SIZE 210296 56 ->
    munch WQ me m -> wmono s0segs me m ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (b' : Z) (nx' : list word) (w144' w152' w168' w176' w184' w232' w240' w248' w256' w288' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      mqs_loop f a2 qo n q = MQS a1' 0 slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) w144' w152' w168' w176' w184' (Z_to_bv 64 0) w232' w240' w248' w256' w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c18) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (nx' : list word) (w144' w152' w168' w176' w184' w208' w232' w240' w248' w256' w288' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      mqs_loop f a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) w144' w152' w168' w176' w184' w208' w232' w240' w248' w256' w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 (Z_to_bv 64 (p + 3668)) (Z_to_bv 64 NA2)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) (Z_to_bv 64 0) (Z_to_bv 64 A2) (Z_to_bv 64 2) (Z_to_bv 64 qsp) (Z_to_bv 64 (p + 4504 + 4 * (qsp - 1))) x24
                          (Z_to_bv 64 (4 * (qsp - 1))) (Z_to_bv 64 (p + 3704 + 4 * (qsp - 1))) (Z_to_bv 64 (p + 4104 + 4 * (qsp - 1)))
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x20f4c) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH].
    { intros qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd nx sb xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 me m q Hq Hb OKv FIN.
      exfalso. subst q. cbn [mqs_loop mq_sp mq_exit] in FIN. destruct FIN as [FIN|FIN]; [lia| discriminate]. }
    intros qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd nx sb xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 me m.
    intros q Hq Hb OKv FIN A1OK A2OK PR DEF K208 LJlo LJhi LJd LNX AR1 AR2 SLO SHI SD NX SCB BUD MI INC APT MU WM Kdone Kexit. subst q.
    msenv_open XOK.
    rewrite mqs_loop_step in FIN, Kdone, Kexit by lia.
    pose proof (OKv 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [mqs_loop] in F0. unfold mqsF in F0. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F0.
    cps_destruct F0 as (Fsp & Flo & Flh & Fhi & Fd & Fbud).
    eapply (S0_iter qsp b (zget slo (qsp - 1)) (zget shi (qsp - 1)) (zget sd (qsp - 1)) a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd nx sb
              xra x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 me m);
      [reflexivity| reflexivity| reflexivity| lia| lia| lia| lia| lia| lia| intros HL; apply Fbud; [exact HL| exact A1OK| exact PR| lia]
      | exact A1OK| exact A2OK| exact PR| exact DEF| exact K208| exact LJlo| exact LJhi| exact LJd| exact LNX
      | exact AR1| exact AR2| exact SLO| exact SHI| exact SD| exact NX| exact SCB| exact BUD| exact MI| exact INC| exact APT| exact MU| exact WM| | |].
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nx' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31
             EQ OK' PR' DEF' AR1' AR2' SLO' SHI' SD' LNX' NX' SCB' BUD' MI' INC' MU' WM'.
      rewrite EQ in FIN, Kdone, Kexit.
      eapply (IH qsp b a1' a2 slo' shi' sd' nlo nhi nd Jlo Jhi Jd nx' sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me m');
        [lia| lia| | exact FIN| exact OK'| exact A2OK| exact PR'| exact DEF'| exact K208| exact LJlo| exact LJhi| exact LJd| exact LNX'
        | exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact NX'| exact SCB'| exact BUD'| exact MI'| exact INC'| exact APT| exact MU'| exact WM'
        | exact Kdone | exact Kexit].
      intros v. pose proof (OKv (S v)) as O. cbv zeta in O. rewrite mqs_loop_step in O by lia. rewrite EQ in O. exact O.
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' nx' w144 w152 w168 w176 w184 w232 w240 w248 w256 w288
             y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.
      intros EQ Hb' Hq' OK' PR' DEF' AR1' AR2' SLO' SHI' SD' LNX' NX' SCB' BUD' MI' INC' MU' WM'.
      rewrite EQ in FIN, Kdone, Kexit.
      assert (OKv' : forall v, let q' := mqs_loop v a2 qo n (MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' false) in
                       (0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z).
      { intros v. pose proof (OKv (S v)) as O. cbv zeta in O. rewrite mqs_loop_step in O by lia. rewrite EQ in O. exact O. }
      clear OKv EQ AR1 AR2 SLO SHI SD NX SCB BUD MI INC MU WM DEF K208. unfold WQ in *.
      pose proof (zb8_length a1' ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
      pose proof (ovw_length slo' Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi' Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd' Jd 100 ltac:(lia)) as Ld.
      open_sc_in SCB'.
      assert (Hq51 : (qsp' <= 51)%Z).
      { destruct (Z_le_gt_dec qsp' 0); [lia|]. pose proof (OKv' 0%nat ltac:(cbn; lia) eq_refl) as F1. cbn [mqs_loop] in F1.
        unfold mqsF in F1. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F1. destruct F1 as (Fsp' & _). exact Fsp'. }
      (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Kz; [apply bgtz_taken in Kz; [|lia] | apply bgtz_not_taken in Kz; [|lia]].
      + (* [comment removed for export] *)
        do 19 wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH qsp' b' a1' a2 slo' shi' sd' nlo' nhi' nd' Jlo Jhi Jd nx'
                   (mkSCB (k128 sb) (k136 sb) w144 w152 w168 w176 w184 (Z_to_bv 64 (qsp' - 1)) w232 w240 w248 w256 w288)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| exact OKv'| exact FIN| exact OK'| exact A2OK| exact PR'| exact DEF'| reflexivity| exact LJlo| exact LJhi| exact LJd| exact LNX'
          | exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact NX'| | exact BUD'| exact MI'| exact INC'| exact APT| exact MU'| exact WM' | | ].
        * match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end.
        * intros m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' b'' nx'' v144 v152 v168 v176 v184 v232 v240 v248 v256 v288
                 z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31.
          intros EQf Hb'' OK'' PR'' AR1'' AR2'' SLO'' SHI'' SD'' LNX'' NX'' SCB'' BUD'' MI'' INC'' MU'' WM''. cbn [k128 k136] in SCB''.
          eapply (Kdone m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' b'' nx'' v144 v152 v168 v176 v184 v232 v240 v248 v256 v288);
            [exact EQf| lia| exact OK''| exact PR''| exact AR1''| exact AR2''| exact SLO''| exact SHI''| exact SD''
            | exact LNX''| exact NX''| exact SCB''| exact BUD''| exact MI''| exact INC''| exact MU''| exact WM''].
        * intros m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' qsp'' b'' nx'' v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
                 z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z19 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31.
          intros EQf Hb'' OK'' PR'' AR1'' AR2'' SLO'' SHI'' SD'' LNX'' NX'' SCB'' BUD'' MI'' INC'' MU'' WM''. cbn [k128 k136] in SCB''.
          eapply (Kexit m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' qsp'' b'' nx'' v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288);
            [exact EQf| lia| exact OK''| exact PR''| exact AR1''| exact AR2''| exact SLO''| exact SHI''| exact SD''
            | exact LNX''| exact NX''| exact SCB''| exact BUD''| exact MI''| exact INC''| exact MU''| exact WM''].
      + (* [comment removed for export] *)
        assert (qsp' = 0)%Z as Z0 by lia. subst qsp'.
        rewrite (mqs_loop_halt f) in Kdone by (cbn; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kdone mm a1' slo' shi' sd' nlo' nhi' nd' b' nx'
                   w144 w152 w168 w176 w184 w232 w240 w248 w256 w288
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact LNX'| exact NX'| | exact BUD'| exact MI'| exact INC'| exact MU'| exact WM'].
        match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end.
    - (* [comment removed for export] *)
      intros m' a1' b' w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288
             y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' NX' SCB' BUD' MI' INC' MU' WM'.
      rewrite EQ in Kexit. rewrite (mqs_loop_halt f) in Kexit by (cbn; right; reflexivity).
      eapply (Kexit m' a1' slo shi sd nlo nhi nd (qsp - 1)%Z b' nx w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288);
        [reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact LNX| exact NX'| exact SCB'| exact BUD'| exact MI'| exact INC'| exact MU'| exact WM'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
  Lemma S0_qloop : forall (f : nat) (qsp b : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte) (nx : list word) (sb : scb)
      (xra x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    (1 <= qsp)%Z -> (0 <= b < 2147483648)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop f a2 qo n q) <= 0 \/ mq_exit (mqs_loop f a2 qo n q) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr s0segs m (p + 4504) (ovw slo Jlo 100) -> u32arr s0segs m (p + 4104) (ovw shi Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx ->
    rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> mem_inv s0segs m ->
    rw_cells s0segs m 210296 [CB 56 incs_bytes] -> apart A1 ARR1_SIZE 210296 56 ->
    munch WQ me m -> wmono s0segs me m ->
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (b' : Z) (nx' : list word) (w144' w152' w168' w176' w184' w232' w240' w248' w256' w288' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      mqs_loop f a2 qo n q = MQS a1' 0 slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) w144' w152' w168' w176' w184' (Z_to_bv 64 0) w232' w240' w248' w256' w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c18) fc None m' (seg_rom s0segs))) ->
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (nx' : list word) (w144' w152' w168' w176' w184' w208' w232' w240' w248' w256' w288' : word)
            (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
      mqs_loop f a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr s0segs m' (p + 4504) (ovw slo' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw shi' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      Z.of_nat (length nx') = 9%Z -> u32arr s0segs m' (p + 3668) nx' ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB (k128 sb) (k136 sb) w144' w152' w168' w176' w184' w208' w232' w240' w248' w256' w288')) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> mem_inv s0segs m' -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      munch WQ me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y1 (Z_to_bv 64 p) gp tp y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 A1) y19 (Z_to_bv 64 A2) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x21c18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 p) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 A1) x19 (Z_to_bv 64 A2) x21 (Z_to_bv 64 qsp) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x20f00) fc None m (seg_rom s0segs)).
  Proof.
    intros f qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd nx sb xra x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m.
    intros q Hq Hb OKv FIN A1OK A2OK PR DEF LJlo LJhi LJd LNX AR1 AR2 SLO SHI SD NX SCB BUD MI INC APT MU WM Kdone Kexit. subst q.
    msenv_open XOK. unfold WQ in *.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    pose proof (OKv 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [mqs_loop] in F0. unfold mqsF in F0. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F0.
    destruct F0 as (Fsp & _).
    destruct sb as [w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288]. open_sc_in SCB.
    do 19 wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_qloopH f qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd nx
               (mkSCB w128 w136 w144 w152 w168 w176 w184 (Z_to_bv 64 (qsp - 1)) w232 w240 w248 w256 w288)
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
      [st_eq| lia| lia| exact OKv| exact FIN| exact A1OK| exact A2OK| exact PR| exact DEF| reflexivity| exact LJlo| exact LJhi| exact LJd| exact LNX
      | exact AR1| exact AR2| exact SLO| exact SHI| exact SD| exact NX| | exact BUD| exact MI| exact INC| exact APT| exact MU| exact WM| exact Kdone| exact Kexit].
    match goal with H : rw_cells _ _ (p + 120)%Z _ |- _ => exact H end.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End S0MS.

End ACeilS1.
