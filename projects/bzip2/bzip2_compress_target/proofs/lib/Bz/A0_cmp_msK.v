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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 BzCQsortM1 BzCQsortM2 BzCSewA AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msF A0_cmp_msH A0_cmp_msJ.
Local Ltac AsanKit.a_norm ::= rewrite ?zext32_id.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSX : amenv_sepx X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation SLO := (am_SLO Y). Notation SHI := (am_SHI Y). Notation SD := (am_SD Y).
  Notation WAP := [(A1, A1 + ARR1_SIZE); (P + 216, P + 384); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.
  Notation WQA := [(A1, A1 + ARR1_SIZE); (P + 216, P + 384); (P + 436, P + 440); (P - 16, P); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.

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

  (* [comment removed for export] *)
  Lemma A0_med : forall (lo hi d : Z) (a1 a2 : zarr) (sq : scq) (W : list ivl) (me : word -> option byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word) (m : word -> option byte),
    (0 <= lo)%Z -> (lo + 20 <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> q368 sq = Z_to_bv 64 lo -> q376 sq = Z_to_bv 64 hi ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) -> mem_inv a0segs m ->
    munch W me m -> frdW a0segs W me (P + 216) (scq_cells Y sq) ->
    shzW a0segs W me A1 (A1 + ARR1_SIZE) -> shzW a0segs W me A2 (A2 + ARR2_SIZE) ->
    (forall (med : Z) (x11' x17' : word),
      med = mmed3 (rd8 a2 (rd32 a1 lo + d)) (rd8 a2 (rd32 a1 hi + d)) (rd8 a2 (rd32 a1 (Z.shiftr (lo + hi) 1) + d)) -> (0 <= med < 256)%Z ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 hi) (Z_to_bv 64 med) (Z_to_bv 64 hi) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A1 + 4 * lo)) x11' (Z_to_bv 64 lo) x13 x14 x15 (Z_to_bv 64 lo) x17'
                            x18 cSB x20 x21 x22 x23 (Z_to_bv 64 d) x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x98c2c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 cSB x20 x21 x22 x23 (Z_to_bv 64 d) x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98b10) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi d a1 a2 sq W me x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x27 x28 x29 x30 x31 m
           Hlo Hlh Hhi Hd A1OK A2OK PR K368 K376 AR1 AR2 MI MU VQ SH1 SH2 K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR lo ltac:(lia)) as Pl. set (pl := rd32 a1 lo) in *. assert (Epl : rd32 a1 lo = pl) by reflexivity. clearbody pl.
    pose proof (PR hi ltac:(lia)) as Ph. set (ph := rd32 a1 hi) in *. assert (Eph : rd32 a1 hi = ph) by reflexivity. clearbody ph.
    pose proof (VQ m MU) as RO_. open_scq_in RO_. rewrite K368, K376 in RO_.
    (* [comment removed for export] *)
    arun. rdptr AR1 A1OK lo. rewrite Epl.
    arun. rdblk AR2 A2OK (pl + d)%Z.
    arun. rdptr AR1 A1OK hi. rewrite Eph.
    (* [comment removed for export] *)
    arun_to 0x98ba8%Z.
    set (mid := Z.shiftr (lo + hi) 1) in *.
    assert (Hmid : mid = ((hi + lo) / 2)%Z) by (subst mid; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1)%Z with 2%Z; f_equal; lia).
    rewrite land_dbl_m4 by lia. rewrite <- Hmid.
    pose proof (PR mid ltac:(lia)) as Pm. set (pm := rd32 a1 mid) in *. assert (Epm : rd32 a1 mid = pm) by reflexivity. clearbody pm.
    (* [comment removed for export] *)
    arun. rdblk AR2 A2OK (ph + d)%Z.
    arun. rdptr AR1 A1OK mid. rewrite Epm.
    arun_to 0x98be4%Z.
    unfold rd8 in K. set (c0 := zget a2 (pl + d)) in *. set (c1 := zget a2 (ph + d)) in *. clearbody c0 c1.
    (* [comment removed for export] *)
    assert (JOIN1 : evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 (Z_to_bv 64 (if c1 <? c0 then c1 else c0)) x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + lo * 4)) (Z_to_bv 64 (A2 + (pm + d))) (Z_to_bv 64 (if c1 <? c0 then c0 else c1)) x13 x14 x15 (Z_to_bv 64 c1) (Z_to_bv 64 0)
                          x18 cSB x20 x21 x22 x23 (Z_to_bv 64 d) x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98bf8) fc None m (seg_rom a0segs))).
    2:{ wstep. wstep; if_cases Kc1; zify_cond_z Kc1.
        - (* [comment removed for export] *)
          wstep; if_cases Kc2; zify_cond_z Kc2; [exfalso; lia|]. wstep.
          enter_with JOIN1. all: replace (c1 <? c0) with true by (symmetry; apply Z.ltb_lt; lia); st_eq.
        - wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
          + enter_with JOIN1. all: replace (c1 <? c0) with false by (symmetry; apply Z.ltb_ge; lia); st_eq.
          + (* [comment removed for export] *) wstep. enter_with JOIN1. all: replace (c1 <? c0) with false by (symmetry; apply Z.ltb_ge; lia); st_eq. }
    set (mx := if c1 <? c0 then c0 else c1) in *. set (mn := if c1 <? c0 then c1 else c0) in *.
    assert (Hmx : (0 <= mx < 256)%Z) by (subst mx; destruct (c1 <? c0); lia).
    assert (Hmn : (0 <= mn < 256)%Z) by (subst mn; destruct (c1 <? c0); lia).
    assert (Hmnx : (mn <= mx)%Z) by (subst mn mx; destruct (Z.ltb_spec c1 c0); lia).
    (* [comment removed for export] *)
    rdblk AR2 A2OK (pm + d)%Z.
    set (c2 := zget a2 (pm + d)) in *. clearbody c2.
    (* [comment removed for export] *)
    assert (MED : forall med, (med = if c2 <? mx then (if c2 <? mn then mn else c2) else mx)%Z ->
              med = mmed3 c0 c1 c2 /\ (0 <= med < 256)%Z).
    { intros med ->. unfold mmed3. subst mx mn. destruct (Z.ltb_spec c1 c0); destruct (Z.ltb_spec c2 c0); destruct (Z.ltb_spec c2 c1); split; try reflexivity; lia. }
    wstep; if_cases Kc3; zify_cond_z Kc3.
    - wstep; if_cases Kc4; zify_cond_z Kc4; [|exfalso; lia].
      arun. if_cases Kc5; zify_cond_z Kc5; [|exfalso; lia].
      destruct (MED mn) as [E1 E2]; [replace (c2 <? mx) with true by (symmetry; apply Z.ltb_lt; lia); replace (c2 <? mn) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
      enter_with (K mn _ _); [st_eq| exact E1| exact E2].
    - wstep. wstep; if_cases Kc4; zify_cond_z Kc4.
      + arun. if_cases Kc5; zify_cond_z Kc5; [|exfalso; lia].
        destruct (MED c2) as [E1 E2]; [replace (c2 <? mx) with true by (symmetry; apply Z.ltb_lt; lia); replace (c2 <? mn) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
        enter_with (K c2 _ _); [st_eq| exact E1| exact E2].
      + arun. if_cases Kc5; zify_cond_z Kc5; [|exfalso; lia].
        destruct (MED mx) as [E1 E2]; [replace (c2 <? mx) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity|].
        enter_with (K mx _ _); [st_eq| exact E1| exact E2].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_apart : forall (lo hi d ltLo unLo unHi gtHi qsp SHl SHh SHd : Z) (a1 a2 : zarr) (slo shi sd : zarr) (Jlo Jhi Jd : list byte)
      (q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 : word)
      (x6 x11 x12 x18 x21 x23 x25 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 51)%Z ->
    saddr (SLO + 4 * (qsp - 1)) SHl -> saddr (SHI + 4 * (qsp - 1)) SHh -> saddr (SD + 4 * (qsp - 1)) SHd ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr a0segs m SLO (ovw slo Jlo 100) -> u32arr a0segs m SHI (ovw shi Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344
                                   (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) (Z_to_bv 64 lo) (Z_to_bv 64 hi))) -> mem_inv a0segs m ->
    munch WAP me m -> wmono a0segs me m ->
    frdW a0segs WAP me (P + 152) [C8 (Z_to_bv 64 (A1 + 4))] ->
    shzW a0segs WAP me A1 (A1 + ARR1_SIZE) ->
    shzW a0segs WAP me SLO (SLO + 400) -> shzW a0segs WAP me SHI (SHI + 400) -> shzW a0segs WAP me SD (SD + 400) ->
    ((gtHi < ltLo)%Z -> forall m' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
      u8arr a0segs m' A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw slo Jlo 100) -> u32arr a0segs m' SHI (ovw shi Jhi 100) ->
      u32arr a0segs m' SD (ovw (zset sd (qsp - 1) (d + 1)) Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344
                                     (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) (Z_to_bv 64 lo) (Z_to_bv 64 hi))) -> mem_inv a0segs m' ->
      munch WAP me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 qsp) cSB (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23
                            (Z_to_bv 64 (d + 1)) x25 (Z_to_bv 64 A2) x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x98a9c) fc None m' (seg_rom a0segs))) ->
    ((ltLo <= gtHi)%Z -> forall m' (q376' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y28 y29 y30 y31 : word),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - (gtHi - unHi) + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1'' := mvswap (S (Z.to_nat mm)) a1' unLo (hi - mm + 1) mm in
      u8arr a0segs m' A1 (zb8 a1'' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr a0segs m' SHI (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr a0segs m' SD (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 (Z_to_bv 64 (qsp + 2)) q320 q328 q336 q344
                                     (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) (Z_to_bv 64 lo) q376')) -> mem_inv a0segs m' ->
      munch WAP me m' -> wmono a0segs me m' ->
      zbok a1'' -> pr n a1'' 0 (n - 1) ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 y22 x23 y24 x25 (Z_to_bv 64 A2) x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x99678) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 gtHi) x6 (Z_to_bv 64 unHi) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + 4 * lo)) x11 x12 (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                          x18 cSB (Z_to_bv 64 (SHI + 4 * (qsp - 1))) x21 (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23
                          (Z_to_bv 64 d) x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98e88) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi d ltLo unLo unHi gtHi qsp SHl SHh SHd a1 a2 slo shi sd Jlo Jhi Jd q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344
           x6 x11 x12 x18 x21 x23 x25 x27 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgt Hhi Hd Hq ASl ASh ASd LJlo LJhi LJd A1OK PR AR1 AR2 SLOB SHIB SDB SCQ MI MU WM V152 SH1 SHZl SHZh SHZd KA KB.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_SLO X Y YSX) as AP1a. pose proof (amsx_1_SHI X Y YSX) as AP1b. pose proof (amsx_1_SD X Y YSX) as AP1c.
    pose proof (amsx_2_SLO X Y YSX) as AP2a. pose proof (amsx_2_SHI X Y YSX) as AP2b. pose proof (amsx_2_SD X Y YSX) as AP2c. box_ors.
    bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    wstep. wstep. rewrite ?sx32_of_Z_signed by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *) clear KA. specialize (KB ltac:(lia)). cbv zeta in KB.
      set (sq := mkSCQ q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) (Z_to_bv 64 lo) (Z_to_bv 64 hi)) in *.
      assert (VQ : frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z m (P + 216) (scq_cells Y sq)).
      { apply frdW_intro; [exact SCQ|]. cbn [disjoint_from scq_cells cells_size csize length Nat.add]. lia. }
      assert (V152' : frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z m (P + 152) [C8 (Z_to_bv 64 (A1 + 4))]).
      { eapply (frdW_sub a0segs); [exact V152| exact MU| sub_fp_solve]. }
      assert (SH1' : shzW a0segs [(A1, A1 + ARR1_SIZE)]%Z m A1 (A1 + ARR1_SIZE)).
      { eapply (shzW_sub a0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_qswap1 X Y Q XOK lo hi ltLo unLo unHi gtHi a1 sq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| reflexivity| exact A1OK| exact PR| exact AR1| exact MI| apply munch_refl| apply wmono_refl| exact VQ| exact SH1'|].
      intros m1 z6 z10 z11 z12 z28 z29 z30. cbv zeta. intros AR1_1 MI1 MU1 WM1 OK1 PR1.
      assert (VQ1 : frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z m1 (P + 216) (scq_cells Y sq)) by (eapply (frdW_sub a0segs); [exact VQ| exact MU1| sub_fp_solve]).
      assert (V152_1 : frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z m1 (P + 152) [C8 (Z_to_bv 64 (A1 + 4))]) by (eapply (frdW_sub a0segs); [exact V152'| exact MU1| sub_fp_solve]).
      assert (SH1_1 : shzW a0segs [(A1, A1 + ARR1_SIZE)]%Z m1 A1 (A1 + ARR1_SIZE)) by (eapply (shzW_sub a0segs); [exact SH1'| exact MU1| sub_fp_solve| lia| lia]).
      clear AR1 MI VQ V152' SH1'. transport_after_call a0segs m m1 MU1 WM1. clear MU1 WM1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_qswap2 X Y Q XOK lo hi ltLo unLo unHi gtHi _ sq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| reflexivity| exact OK1| exact PR1| exact AR1_1| exact MI1| apply munch_refl| apply wmono_refl| exact VQ1| exact V152_1| exact SH1_1|].
      intros m2 w5 w6 w7 w10 w11 w28 w29. cbv zeta. intros AR1_2 MI2 MU2 WM2 OK2 PR2.
      clear AR1_1 MI1 VQ1 V152_1 SH1_1. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
      subst sq.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_qnext X Y Q XOK YOK lo hi d ltLo unLo (gtHi - unHi)%Z qsp SHl SHh SHd slo shi sd Jlo Jhi Jd
                      q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 (Z_to_bv 64 lo) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact ASl| exact ASh| exact ASd| exact LJlo| exact LJhi| exact LJd| exact SLOB| exact SHIB| exact SDB| exact SCQ| exact MI2
        | apply munch_refl| apply wmono_refl
        | eapply (shzW_sub a0segs); [exact SHZl| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs); [exact SHZh| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs); [exact SHZd| exact MU| sub_fp_solve| lia| lia] |].
      intros m3 q376' v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v18 v28 v29 v30 v31. cbv zeta.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [f0 f1] eqn:E1 end; cbv beta iota.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [g1 g2] eqn:E2 end; cbv beta iota.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [h0 h1] eqn:E3 end; cbv beta iota.
      destruct h0 as [[l0 u0] d0]. destruct h1 as [[l1 u1] d1]. destruct g2 as [[l2 u2] d2]. cbv beta iota in KB.
      intros SLO3 SHI3 SD3 SCQ3 MI3 MU3 WM3.
      clear SLOB SHIB SDB SCQ MI2. bz_params.
      transport_after_call a0segs m2 m3 MU3 WM3. clear MU3 WM3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KB mm q376' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1_2| exact AR2| exact SLO3| exact SHI3| exact SD3| exact SCQ3| exact MI3| exact MU| exact WM| exact OK2| exact PR2].
    - (* [comment removed for export] *)
      clear KB. specialize (KA ltac:(lia)).
      open_scq_in SCQ.
      arun.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (u32arr_store_ok a0segs mm SD _ (qsp - 1) _ SDB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
      wstep. ovw_store SDB (qsp - 1)%Z (d + 1)%Z (apply unsigned_lit_mod32).
      arun_to 0x98a9c%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KA mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SCQ| assumption| exact MU| exact WM].
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
  Ltac sub_frd VC MU := eapply (frdW_sub a0segs); [exact VC| exact MU| sub_fp_solve].
  Ltac sub_aco ACW MU := eapply acoW_sub; [exact ACW| exact MU| sub_fp_solve].
  Ltac sub_shz SH MU := eapply (shzW_sub a0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].
  Ltac sub_shp SH MU := eapply (shpW_sub a0segs); [exact SH| exact MU| sub_fp_solve| lia| lia].

  (* [comment removed for export] *)
  Definition qviews (me : word -> option byte) : Prop :=
    frdW a0segs WQA me (P + 384) (scc_cells X) /\ frdW a0segs WQA me (P + 152) [C8 (Z_to_bv 64 (A1 + 4))] /\ acoW WQA me /\
    shzW a0segs WQA me A1 (A1 + ARR1_SIZE) /\ shzW a0segs WQA me A2 (A2 + ARR2_SIZE) /\ shpW a0segs WQA me (P + 436) (P + 440) /\
    shzW a0segs WQA me 139040 139096 /\
    shzW a0segs WQA me SLO (SLO + 400) /\ shzW a0segs WQA me SHI (SHI + 400) /\ shzW a0segs WQA me SD (SD + 400).

  (* [comment removed for export] *)
  Lemma A0_iter : forall (qsp b lo hi d : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte) (sq : scq)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    zget slo (qsp - 1) = lo -> zget shi (qsp - 1) = hi -> zget sd (qsp - 1) = d ->
    (1 <= qsp <= 51)%Z -> (0 <= lo)%Z -> (lo <= hi + 1)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= b < 2147483648)%Z ->
    ((hi - lo < 20 \/ 14 < d)%Z -> (-2147483648 < snd (mainSimpleSort a1 a2 qo n lo hi d b))%Z) ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    q288 sq = Z_to_bv 64 (qsp - 1) -> q352 sq = Z_to_bv 64 (SLO + 4 * (qsp - 1)) -> q360 sq = Z_to_bv 64 qsp ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr a0segs m SLO (ovw slo Jlo 100) -> u32arr a0segs m SHI (ovw shi Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 216) (scq_cells Y sq) -> rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P -> mem_inv a0segs m ->
    munch WQA me m -> wmono a0segs me m -> qviews me ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' : zarr) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 : word),
      ITER a2 qo n q = MQS a1' qsp slo' shi' sd' nlo nhi nd b false ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      (forall i, 0 <= i < qsp -> zdef slo' i = true /\ zdef shi' i = true /\ zdef sd' i = true)%Z ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw slo' Jlo 100) -> u32arr a0segs m' SHI (ovw shi' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ (q216 sq) (q224 sq) (q232 sq) (q240 sq) (q256 sq) (q264 sq) (q272 sq) (q288 sq) (q320 sq) (q328 sq) (q336 sq) (q344 sq)
                                     (q352 sq) (q360 sq) (Z_to_bv 64 lo) (Z_to_bv 64 hi))) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WQA me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 qsp) cSB (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23
                            y24 x25 (Z_to_bv 64 A2) x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x98a9c) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (w216' w224' w232' w240' w320' w328' w336' w344' w352' w360' w368' w376' : word)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31 : word),
      ITER a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z -> (0 <= qsp')%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      (forall i, 0 <= i < qsp' -> zdef slo' i = true /\ zdef shi' i = true /\ zdef sd' i = true)%Z ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw slo' Jlo 100) -> u32arr a0segs m' SHI (ovw shi' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ w216' w224' w232' w240' (q256 sq) (q264 sq) (q272 sq) (Z_to_bv 64 qsp') w320' w328' w336' w344' w352' w360' w368' w376')) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WQA me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 y22 x23 y24 y25 y26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x99678) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' : zarr) (b' : Z) (w216' w224' w232' w240' w320' w328' w336' w344' w352' w360' w368' w376' : word)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31 : word),
      ITER a2 qo n q = MQS a1' (qsp - 1) slo shi sd nlo nhi nd b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw slo Jlo 100) -> u32arr a0segs m' SHI (ovw shi Jhi 100) -> u32arr a0segs m' SD (ovw sd Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ w216' w224' w232' w240' (q256 sq) (q264 sq) (q272 sq) (q288 sq) w320' w328' w336' w344' w352' w360' w368' w376')) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WQA me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 y22 x23 y24 y25 y26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a000) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 qsp) cSB (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23
                          x24 x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98a9c) fc None m (seg_rom a0segs)).
  Proof.
    intros qsp b lo hi d a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd sq x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 me m.
    intros q Elo Ehi Ed Hq Hlo Hlh Hhi Hd Hb BFIN A1OK A2OK PR DEF K288 K352 K360 LJlo LJhi LJd AR1 AR2 SLOB SHIB SDB SCQ BUD STK MI MU WM QV KA KB KC. subst q.
    destruct QV as (VC & V152 & ACW & SH1 & SH2 & SHB & SHINC & SHZl & SHZh & SHZd).
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    pose proof (amsx_1_SLO X Y YSX) as AP1a. pose proof (amsx_1_SHI X Y YSX) as AP1b. pose proof (amsx_1_SD X Y YSX) as AP1c.
    pose proof (amsx_2_SLO X Y YSX) as AP2a. pose proof (amsx_2_SHI X Y YSX) as AP2b. pose proof (amsx_2_SD X Y YSX) as AP2c. box_ors.
    bz_params. pose proof alloc_ceiling_range as ACR.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    cps_destruct (DEF (qsp - 1)%Z ltac:(lia)) as (Dlo & Dhi & Dd).
    destruct sq as [w216 w224 w232 w240 w256 w264 w272 w288 w320 w328 w336 w344 w352 w360 w368 w376].
    cbn [q288 q352 q360] in K288, K352, K360. subst w288 w352 w360. cbn [q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q352 q360 q368 q376] in KA, KB, KC.
    open_scq_in SCQ.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    arun. rdstk SLOB (qsp - 1)%Z Dlo. rewrite Elo.
    arun. rdstk SHIB (qsp - 1)%Z Dhi. rewrite Ehi.
    arun. rdstk SDB (qsp - 1)%Z Dd. rewrite Ed.
    (* [comment removed for export] *)
    pose proof (saddr_intro (SLO + 4 * (qsp - 1))) as ASl. set (SHl := ((SLO + 4 * (qsp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHl.
    pose proof (saddr_intro (SHI + 4 * (qsp - 1))) as ASh. set (SHh := ((SHI + 4 * (qsp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHh.
    pose proof (saddr_intro (SD + 4 * (qsp - 1))) as ASd. set (SHd := ((SD + 4 * (qsp - 1)) / 8 + 2147450880)%Z) in *. clearbody SHd.
    (* [comment removed for export] *)
    arun.
    assert (LEAF : (hi - lo < 20 \/ 14 < d)%Z -> forall y10,
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          y10 (Z_to_bv 64 (hi - lo)) (Z_to_bv 64 hi) (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) x16 x17
                          (Z_to_bv 64 qsp) cSB (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23
                          (Z_to_bv 64 d) x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98f50) fc None m (seg_rom a0segs))).
    { intros Hleaf y10. specialize (BFIN Hleaf). clear KA.
      pose proof (ITER_leaf a2 qo n a1 qsp slo shi sd nlo nhi nd b) as IL. cbv zeta in IL. rewrite !Elo, !Ehi, !Ed in IL.
      specialize (IL ltac:(apply Bool.orb_true_iff; destruct Hleaf; [left | right]; apply Z.ltb_lt; lia)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_mss X Y Q XOK XSEP YOK x23 x27 d lo hi a1 a2 b w216 w224 w232 w240 w256 w264 w272 (Z_to_bv 64 (qsp - 1)) w320 w328 w336 w344 (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp)
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| exact BFIN| lia| exact AR1| exact AR2| exact SCQ| exact BUD| exact STK| exact MI
        | apply munch_refl| apply wmono_refl| sub_frd VC MU| sub_aco ACW MU| sub_shz SH1 MU| sub_shz SH2 MU| sub_shp SHB MU| sub_shz SHINC MU| |].
      - intros m' w216' w224' w232' w240' w320' w328' w336' w344' w352' w360'
               z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z20 z21 z22 z25 z26 z28 z29 z30 z31. cbv zeta.
        intros Hb' AR1' AR2' SCQ' BUD' STK' MI' MU' WM' OK' PR' LE'.
        clear AR1 AR2 SCQ BUD STK MI. bz_params. transport_after_call a0segs m m' MU' WM'. clear MU' WM'.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (KB mm (fst (mainSimpleSort a1 a2 qo n lo hi d b)) slo shi sd nlo nhi nd (qsp - 1)%Z (snd (mainSimpleSort a1 a2 qo n lo hi d b))
             w216' w224' w232' w240' w320' w328' w336' w344' w352' w360' (Z_to_bv 64 lo) (Z_to_bv 64 hi)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| | lia| lia| exact OK'| exact PR'| | exact AR1'| exact AR2'| exact SLOB| exact SHIB| exact SDB| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU| exact WM].
        + rewrite IL. replace (snd (mainSimpleSort a1 a2 qo n lo hi d b) <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        + intros i Hi. apply DEF. lia.
      - intros m' w216' w224' w232' w240' w320' w328' w336' w344' w352' w360'
               z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z20 z21 z22 z25 z26 z28 z29 z30 z31. cbv zeta.
        intros Hb' AR1' AR2' SCQ' BUD' STK' MI' MU' WM' OK' PR' LE'.
        clear AR1 AR2 SCQ BUD STK MI. bz_params. transport_after_call a0segs m m' MU' WM'. clear MU' WM'.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (KC mm (fst (mainSimpleSort a1 a2 qo n lo hi d b)) (snd (mainSimpleSort a1 a2 qo n lo hi d b))
             w216' w224' w232' w240' w320' w328' w336' w344' w352' w360' (Z_to_bv 64 lo) (Z_to_bv 64 hi)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| | lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLOB| exact SHIB| exact SDB| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU| exact WM].
        rewrite IL. replace (snd (mainSimpleSort a1 a2 qo n lo hi d b) <? 0) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    if_cases Kc1; zify_cond_z Kc1.
    { enter_with (LEAF ltac:(lia) _). st_eq. }
    arun. if_cases Kc2; zify_cond_z Kc2.
    { enter_with (LEAF ltac:(lia) _). st_eq. }
    clear LEAF BFIN.
    set (sq1 := mkSCQ w216 w224 w232 w240 w256 w264 w272 (Z_to_bv 64 (qsp - 1)) w320 w328 w336 w344 (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) (Z_to_bv 64 lo) (Z_to_bv 64 hi)).
    assert (VQ0 : frdW a0segs [] m (P + 216) (scq_cells Y sq1)) by (apply frdW_intro; [exact SCQ| cbn [disjoint_from]; exact I]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_med lo hi d a1 a2 sq1 [] mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm) end;
      [st_eq| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| reflexivity| reflexivity| exact AR1| exact AR2| exact MI| apply munch_refl| exact VQ0
      | sub_shz SH1 MU| sub_shz SH2 MU|].
    intros med x11' x17' Hmed Hmr. clear VQ0.
    pose proof (ITER_part a2 a1 qsp slo shi sd nlo nhi nd b med) as IP. cbv zeta in IP. rewrite !Elo, !Ehi, !Ed in IP.
    cps_destruct (IP Hlo ltac:(lia) Hmed) as (Epp & P1 & P2 & P3 & P4 & P5). clear IP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_part X Y Q XOK XSEP lo hi d med (Z.to_nat (hi - lo + 1)) a2 _ _ _ _ _ _ _ _ _
                    (S (Z.to_nat (hi - lo + 1))) lo hi lo hi a1 _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact A2OK| exact PR| lia| exact AR1| exact AR2| exact MI| apply munch_refl| apply wmono_refl
      | sub_shz SH1 MU| sub_shz SH2 MU|].
    intros m1 z11 z12 z18 z21 z28 z29 z30 z31. cbv zeta. intros AR1_1 AR2_1 MI1 MU1 WM1 OK1 PR1 B1 B2 B3.
    clear AR1 AR2 MI. bz_params. transport_after_call a0segs m m1 MU1 WM1. clear MU1 WM1.
    set (pp := mpart_loop (S (Z.to_nat (hi - lo + 1))) (Z.to_nat (hi - lo + 1)) a2 d med (MP a1 lo hi lo hi)) in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (A0_apart lo hi d (mp_ltLo pp) (mp_unLo pp) (mp_unHi pp) (mp_gtHi pp) qsp SHl SHh SHd (mp_a1 pp) a2 slo shi sd Jlo Jhi Jd
                    w216 w224 w232 w240 w256 w264 w272 (Z_to_bv 64 (qsp - 1)) w320 w328 w336 w344
                    _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact ASl| exact ASh| exact ASd| exact LJlo| exact LJhi| exact LJd| exact OK1| exact PR1| exact AR1_1| exact AR2_1
      | exact SLOB| exact SHIB| exact SDB| exact SCQ| exact MI1| apply munch_refl| apply wmono_refl| sub_frd V152 MU| sub_shz SH1 MU| sub_shz SHZl MU| sub_shz SHZh MU| sub_shz SHZd MU| |].
    - (* [comment removed for export] *) intros Hlt m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AR1_2 AR2_2 SLO2 SHI2 SD2 SCQ2 MI2 MU2 WM2. clear KB KC.
      clear SLOB SHIB SDB SCQ AR1_1 AR2_1 MI1. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
      rewrite <- (ovw_zset_same slo (qsp - 1) Jlo 100 Dlo), Elo in SLO2. rewrite <- (ovw_zset_same shi (qsp - 1) Jhi 100 Dhi), Ehi in SHI2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (KA mm (mp_a1 pp) (zset slo (qsp - 1) lo) (zset shi (qsp - 1) hi) (zset sd (qsp - 1) (d + 1)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| | exact OK1| exact PR1| | exact AR1_2| exact AR2_2| exact SLO2| exact SHI2| exact SD2| exact SCQ2| exact BUD| exact STK| exact MI2| exact MU| exact WM].
      + pose proof (ITER_repush a2 qo n a1 qsp slo shi sd nlo nhi nd b pp) as IR. cbv zeta in IR. rewrite !Elo, !Ehi, !Ed in IR.
        apply IR; [| exact Epp| lia]. apply Bool.orb_false_iff; split; apply Z.ltb_ge; lia.
      + intros i Hi. rewrite !zdef_zset. cps_destruct (DEF i Hi) as (D1 & D2 & D3). rewrite D1, D2, D3, !Bool.orb_true_r. CmpFast.tauto_g.
    - (* [comment removed for export] *) intros Hle m2 q376' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y28 y29 y30 y31. clear KA KC. cbv zeta.
      pose proof (iter_push_shape a1 qsp slo shi sd nlo nhi nd b pp) as PS. cbv zeta in PS. rewrite !Elo, !Ehi, !Ed in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [f0 f1] eqn:E1 end; cbv beta iota; cbv beta iota in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [g1 g2] eqn:E2 end; cbv beta iota; cbv beta iota in PS.
      lazymatch goal with |- context [srt2 ?x ?y] => destruct (srt2 x y) as [h0 h1] eqn:E3 end; cbv beta iota; cbv beta iota in PS.
      destruct h0 as [[l0 u0] d0]. destruct h1 as [[l1 u1] d1]. destruct g2 as [[l2 u2] d2]. cbv beta iota in PS.
      cps_destruct PS as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
      intros AR1_2 AR2_2 SLO2 SHI2 SD2 SCQ2 MI2 MU2 WM2 OK2 PR2.
      clear SLOB SHIB SDB SCQ AR1_1 AR2_1 MI1. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
      lazymatch type of AR1_2 with u8arr _ _ _ (zb8 ?a1x _) =>
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (KB mm a1x _ _ _ (mq_nlo (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp))))
                      (mq_nhi (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp))))
                      (mq_nd (PUSH3 (net (Q2 (MQS a1 qsp slo shi sd nlo nhi nd b false) pp)))) (qsp + 2)%Z b
                      w216 w224 w232 w240 w320 w328 w336 w344 (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) (Z_to_bv 64 lo) q376'
                      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end end;
        [st_eq| | lia| lia| exact OK2| exact PR2| | exact AR1_2| exact AR2_2| exact SLO2| exact SHI2| exact SD2| exact SCQ2| exact BUD| exact STK| exact MI2| exact MU| exact WM].
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
  Lemma A0_qloop : forall (f : nat) (qsp b : Z) (a1 a2 slo shi sd nlo nhi nd : zarr) (Jlo Jhi Jd : list byte) (sq : scq)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    let q := MQS a1 qsp slo shi sd nlo nhi nd b false in
    (1 <= qsp)%Z -> (0 <= b < 2147483648)%Z ->
    (forall v, let q' := mqs_loop v a2 qo n q in 0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z ->
    (mq_sp (mqs_loop f a2 qo n q) <= 0 \/ mq_exit (mqs_loop f a2 qo n q) = true)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) ->
    (forall i, 0 <= i < qsp -> zdef slo i = true /\ zdef shi i = true /\ zdef sd i = true)%Z ->
    q288 sq = Z_to_bv 64 (qsp - 1) -> q352 sq = Z_to_bv 64 (SLO + 4 * (qsp - 1)) -> q360 sq = Z_to_bv 64 qsp ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr a0segs m A2 (zb8 a2 ARR2_SIZE) ->
    u32arr a0segs m SLO (ovw slo Jlo 100) -> u32arr a0segs m SHI (ovw shi Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 216) (scq_cells Y sq) -> rw_cells a0segs m (P + 436) [C4 (Z_to_bv 64 b)] -> stk a0segs m (me_lo X) P -> mem_inv a0segs m ->
    munch WQA me m -> wmono a0segs me m -> qviews me ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (b' : Z) (w216' w224' w232' w240' w320' w328' w336' w344' w352' w360' w368' w376' : word)
            (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31 : word),
      mqs_loop f a2 qo n q = MQS a1' 0 slo' shi' sd' nlo' nhi' nd' b' false -> (0 <= b' <= b)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw slo' Jlo 100) -> u32arr a0segs m' SHI (ovw shi' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ w216' w224' w232' w240' (q256 sq) (q264 sq) (q272 sq) (Z_to_bv 64 0) w320' w328' w336' w344' w352' w360' w368' w376')) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WQA me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 0) cSB y20 y21 y22 x23 y24 y25 y26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x99718) fc None m' (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    (forall m' (a1' slo' shi' sd' nlo' nhi' nd' : zarr) (qsp' b' : Z) (w288' : word) (w216' w224' w232' w240' w320' w328' w336' w344' w352' w360' w368' w376' : word)
            (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31 : word),
      mqs_loop f a2 qo n q = MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> pr n a1' 0 (n - 1) ->
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr a0segs m' A2 (zb8 a2 ARR2_SIZE) ->
      u32arr a0segs m' SLO (ovw slo' Jlo 100) -> u32arr a0segs m' SHI (ovw shi' Jhi 100) -> u32arr a0segs m' SD (ovw sd' Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ w216' w224' w232' w240' (q256 sq) (q264 sq) (q272 sq) w288' w320' w328' w336' w344' w352' w360' w368' w376')) ->
      rw_cells a0segs m' (P + 436) [C4 (Z_to_bv 64 b')] -> stk a0segs m' (me_lo X) P -> mem_inv a0segs m' ->
      munch WQA me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp y5 y6 y7 (me_sp X) (Z_to_bv 64 P)
                            y10 y11 y12 y13 y14 y15 y16 y17
                            y18 cSB y20 y21 y22 x23 y24 y25 y26 x27 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x9a000) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 qsp) cSB (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23
                          x24 x25 (Z_to_bv 64 A2) x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98a9c) fc None m (seg_rom a0segs)).
  Proof.
    induction f as [|f IH].
    { intros qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd sq x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 me m q Hq Hb OKv FIN.
      exfalso. subst q. cbn [mqs_loop mq_sp mq_exit] in FIN. destruct FIN as [FIN|FIN]; [lia| discriminate]. }
    intros qsp b a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd sq x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 me m.
    intros q Hq Hb OKv FIN A1OK A2OK PR DEF K288 K352 K360 LJlo LJhi LJd AR1 AR2 SLOB SHIB SDB SCQ BUD STK MI MU WM QV Kdone Kexit. subst q.
    msenv_open XOK. amenv_open YOK.
    rewrite mqs_loop_step in FIN, Kdone, Kexit by lia.
    pose proof (OKv 0%nat ltac:(cbn; lia) eq_refl) as F0. cbn [mqs_loop] in F0. unfold mqsF in F0. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F0.
    cps_destruct F0 as (Fsp & Flo & Flh & Fhi & Fd & Fbud).
    eapply (A0_iter qsp b (zget slo (qsp - 1)) (zget shi (qsp - 1)) (zget sd (qsp - 1)) a1 a2 slo shi sd nlo nhi nd Jlo Jhi Jd sq
              x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x27 x28 x29 x30 x31 me m);
      [reflexivity| reflexivity| reflexivity| lia| lia| lia| lia| lia| lia| intros HL; apply Fbud; [exact HL| exact A1OK| exact PR| lia]
      | exact A1OK| exact A2OK| exact PR| exact DEF| exact K288| exact K352| exact K360| exact LJlo| exact LJhi| exact LJd
      | exact AR1| exact AR2| exact SLOB| exact SHIB| exact SDB| exact SCQ| exact BUD| exact STK| exact MI| exact MU| exact WM| exact QV| | |].
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 EQ OK' PR' DEF' AR1' AR2' SLO' SHI' SD' SCQ' BUD' STK' MI' MU' WM'.
      rewrite EQ in FIN, Kdone, Kexit.
      eapply (IH qsp b a1' a2 slo' shi' sd' nlo nhi nd Jlo Jhi Jd
                (mkSCQ (q216 sq) (q224 sq) (q232 sq) (q240 sq) (q256 sq) (q264 sq) (q272 sq) (q288 sq) (q320 sq) (q328 sq) (q336 sq) (q344 sq) (q352 sq) (q360 sq)
                       (Z_to_bv 64 (zget slo (qsp - 1))) (Z_to_bv 64 (zget shi (qsp - 1))))
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me m');
        [lia| lia| | exact FIN| exact OK'| exact A2OK| exact PR'| exact DEF'| exact K288| exact K352| exact K360| exact LJlo| exact LJhi| exact LJd
        | exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact QV
        | exact Kdone | exact Kexit].
      intros v. pose proof (OKv (S v)) as O. cbv zeta in O. rewrite mqs_loop_step in O by lia. rewrite EQ in O. exact O.
    - (* [comment removed for export] *)
      intros m' a1' slo' shi' sd' nlo' nhi' nd' qsp' b' w216 w224 w232 w240 w320 w328 w336 w344 w352 w360 w368 w376
             y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' Hq' OK' PR' DEF' AR1' AR2' SLO' SHI' SD' SCQ' BUD' STK' MI' MU' WM'.
      rewrite EQ in FIN, Kdone, Kexit.
      assert (OKv' : forall v, let q' := mqs_loop v a2 qo n (MQS a1' qsp' slo' shi' sd' nlo' nhi' nd' b' false) in
                       (0 < mq_sp q' -> mq_exit q' = false -> mqsF a2 qo n q')%Z).
      { intros v. pose proof (OKv (S v)) as O. cbv zeta in O. rewrite mqs_loop_step in O by lia. rewrite EQ in O. exact O. }
      clear OKv EQ AR1 AR2 SLOB SHIB SDB SCQ BUD STK MI MU WM DEF K288 K352 K360.
      pose proof (zb8_length a1' ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
      pose proof (ovw_length slo' Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi' Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd' Jd 100 ltac:(lia)) as Ld.
      open_scq_in SCQ'.
      assert (Hq51 : (qsp' <= 51)%Z).
      { destruct (Z_le_gt_dec qsp' 0); [lia|]. pose proof (OKv' 0%nat ltac:(cbn; lia) eq_refl) as F1. cbn [mqs_loop] in F1.
        unfold mqsF in F1. cbn [mq_sp mq_slo mq_shi mq_sd mq_a1 mq_budget] in F1. destruct F1 as (Fsp' & _). exact Fsp'. }
      (* [comment removed for export] *)
      wstep. wstep.
      wstep; if_cases Kz; [apply bgtz_taken in Kz; [|lia] | apply bgtz_not_taken in Kz; [|lia]].
      + (* [comment removed for export] *)
        destruct QV as (VC & QV').
        pose proof (VC m' MU') as RO_. unfold scc_cells in RO_.
        wstep. replace (qsp' + -1)%Z with (qsp' - 1)%Z by lia. wstep. wstep. wstep. wstep.
        replace (SLO + (qsp' - 1) * 4)%Z with (SLO + 4 * (qsp' - 1))%Z by lia.
        arun_to 0x98a9c%Z. clear RO_.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH qsp' b' a1' a2 slo' shi' sd' nlo' nhi' nd' Jlo Jhi Jd
                   (mkSCQ w216 w224 w232 w240 (q256 sq) (q264 sq) (q272 sq) (Z_to_bv 64 (qsp' - 1)) w320 w328 w336 w344 (Z_to_bv 64 (SLO + 4 * (qsp' - 1))) (Z_to_bv 64 qsp') w368 w376)
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me mm) end;
          [st_eq| lia| lia| exact OKv'| exact FIN| exact OK'| exact A2OK| exact PR'| exact DEF'| reflexivity| reflexivity| reflexivity| exact LJlo| exact LJhi| exact LJd
          | exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| | exact BUD'| | | | | exact (conj VC QV') | | ].
        * match goal with H : rw_cells _ _ (P + 216)%Z _ |- _ => exact H end.
        * assumption. * assumption. * assumption. * assumption.
        * intros m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' b'' v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376
                 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z20 z21 z22 z24 z25 z26 z28 z29 z30 z31.
          intros EQf Hb'' OK'' PR'' AR1'' AR2'' SLO'' SHI'' SD'' SCQ'' BUD'' STK'' MI'' MU'' WM''. cbn [q256 q264 q272] in SCQ''.
          eapply (Kdone m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' b'' v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376);
            [exact EQf| lia| exact OK''| exact PR''| exact AR1''| exact AR2''| exact SLO''| exact SHI''| exact SD''
            | exact SCQ''| exact BUD''| exact STK''| exact MI''| exact MU''| exact WM''].
        * intros m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' qsp'' b'' v288 v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376
                 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z18 z20 z21 z22 z24 z25 z26 z28 z29 z30 z31.
          intros EQf Hb'' OK'' PR'' AR1'' AR2'' SLO'' SHI'' SD'' SCQ'' BUD'' STK'' MI'' MU'' WM''. cbn [q256 q264 q272] in SCQ''.
          eapply (Kexit m'' a1'' slo'' shi'' sd'' nlo'' nhi'' nd'' qsp'' b'' v288 v216 v224 v232 v240 v320 v328 v336 v344 v352 v360 v368 v376);
            [exact EQf| lia| exact OK''| exact PR''| exact AR1''| exact AR2''| exact SLO''| exact SHI''| exact SD''
            | exact SCQ''| exact BUD''| exact STK''| exact MI''| exact MU''| exact WM''].
      + (* [comment removed for export] *)
        assert (qsp' = 0)%Z as Z0 by lia. subst qsp'.
        rewrite (mqs_loop_halt f) in Kdone by (cbn; lia).
        wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (Kdone mm a1' slo' shi' sd' nlo' nhi' nd' b'
                   w216 w224 w232 w240 w320 w328 w336 w344 w352 w360 w368 w376
                   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| | exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'].
        match goal with H : rw_cells _ _ (P + 216)%Z _ |- _ => exact H end.
    - (* [comment removed for export] *)
      intros m' a1' b' w216 w224 w232 w240 w320 w328 w336 w344 w352 w360 w368 w376 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y22 y24 y25 y26 y28 y29 y30 y31.
      intros EQ Hb' OK' PR' AR1' AR2' SLO' SHI' SD' SCQ' BUD' STK' MI' MU' WM'.
      rewrite EQ in Kexit. rewrite (mqs_loop_halt f) in Kexit by (cbn; right; reflexivity).
      eapply (Kexit m' a1' slo shi sd nlo nhi nd (qsp - 1)%Z b' (q288 sq) w216 w224 w232 w240 w320 w328 w336 w344 w352 w360 w368 w376); [reflexivity| lia| exact OK'| exact PR'| exact AR1'| exact AR2'| exact SLO'| exact SHI'| exact SD'| exact SCQ'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
