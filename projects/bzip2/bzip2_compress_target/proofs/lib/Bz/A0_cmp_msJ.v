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
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_msI.
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
  Notation WST := [(P + 216, P + 384); (SLO, SLO + 400); (SHI, SHI + 400); (SD, SD + 400)]%Z.

  (* [comment removed for export] *)
  Lemma A0_push3 : forall (qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d SHl SHh SHd : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte)
      (q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q368 q376 : word)
      (xra x10 x18 x21 x23 x24 x25 x26 x27 x29 : word) (me m : word -> option byte),
    (1 <= qsp <= 98)%Z ->
    (forall v, In v [v0l; v0h; v0d; v1l; v1h; v1d; v2l; v2h; v2d] -> - 2147483648 <= v < 2147483648)%Z ->
    saddr (SLO + 4 * (qsp - 1)) SHl -> saddr (SHI + 4 * (qsp - 1)) SHh -> saddr (SD + 4 * (qsp - 1)) SHd ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr a0segs m SLO (ovw slo Jlo 100) -> u32arr a0segs m SHI (ovw shi Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344
                                   (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) q368 q376)) -> mem_inv a0segs m ->
    munch WST me m -> wmono a0segs me m ->
    shzW a0segs WST me SLO (SLO + 400) -> shzW a0segs WST me SHI (SHI + 400) -> shzW a0segs WST me SD (SD + 400) ->
    (forall m' (x10' x12' x13' x14' x15' x18' : word),
      u32arr a0segs m' SLO (ovw (zset (zset (zset slo (qsp - 1) v0l) qsp v1l) (qsp + 1) v2l) Jlo 100) ->
      u32arr a0segs m' SHI (ovw (zset (zset (zset shi (qsp - 1) v0h) qsp v1h) (qsp + 1) v2h) Jhi 100) ->
      u32arr a0segs m' SD (ovw (zset (zset (zset sd (qsp - 1) v0d) qsp v1d) (qsp + 1) v2d) Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 (Z_to_bv 64 (qsp + 2)) q320 q328 q336 q344
                                     (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) q368 q376)) ->
      mem_inv a0segs m' -> munch WST me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp (Z_to_bv 64 v0d) (Z_to_bv 64 v1h) (Z_to_bv 64 v1l) (me_sp X) (Z_to_bv 64 P)
                            x10' (Z_to_bv 64 v2d) x12' x13' x14' x15' (Z_to_bv 64 v2h) (Z_to_bv 64 v1d)
                            x18' cSB (Z_to_bv 64 (SHI + 4 * (qsp - 1))) x21 (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23 x24 x25 x26 x27
                            (Z_to_bv 64 v0l) x29 (Z_to_bv 64 qsp) (Z_to_bv 64 v0h))
                       F (Z_to_bv 64 0x99678) fc None m' (seg_rom a0segs))) ->
    forall (x18o x30o : word),
    evt a0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp (Z_to_bv 64 v0d) (Z_to_bv 64 v1h) (Z_to_bv 64 v1l) (me_sp X) (Z_to_bv 64 P)
                          x10 (Z_to_bv 64 v2d) (Z_to_bv 64 v2l) (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) (Z_to_bv 64 v2h) (Z_to_bv 64 v1d)
                          x18o cSB (Z_to_bv 64 (SHI + 4 * (qsp - 1))) x21 (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23 x24 x25 x26 x27
                          (Z_to_bv 64 v0l) x29 x30o (Z_to_bv 64 v0h))
                     F (Z_to_bv 64 0x99590) fc None m (seg_rom a0segs)).
  Proof.
    intros qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d SHl SHh SHd slo shi sd Jlo Jhi Jd q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q368 q376
           xra x10 x18 x21 x23 x24 x25 x26 x27 x29 me m
           Hq HV ASl ASh ASd LJlo LJhi LJd SLOB SHIB SDB SCQ MI MU WM SHZl SHZh SHZd K x18o x30o.
    msenv_open XOK. amenv_open YOK. open_scq_in SCQ.
    assert (R0l := HV v0l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R0h := HV v0h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R0d := HV v0d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])).
    assert (R1l := HV v1l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R1h := HV v1h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R1d := HV v1d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])).
    assert (R2l := HV v2l ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R2h := HV v2h ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). assert (R2d := HV v2d ltac:(cbn; first [ solve [ repeat first [ left; reflexivity | right ] ] | tauto ])). clear HV.
    pose proof (ovw_length slo Jlo 100 ltac:(lia)) as Llo. pose proof (ovw_length shi Jhi 100 ltac:(lia)) as Lhi. pose proof (ovw_length sd Jd 100 ltac:(lia)) as Ld.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SLO _ (qsp - 1) _ SLOB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SLOB (qsp - 1)%Z v0l (apply unsigned_lit_mod32).
    try clear SO.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SHI _ (qsp - 1) _ SHIB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SHIB (qsp - 1)%Z v0h (apply unsigned_lit_mod32). try clear SO.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SD _ (qsp - 1) _ SDB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SDB (qsp - 1)%Z v0d (apply unsigned_lit_mod32). try clear SO.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SLO _ (qsp) _ SLOB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SLOB (qsp)%Z v1l (apply unsigned_lit_mod32). try clear SO.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SHI _ (qsp) _ SHIB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SHIB (qsp)%Z v1h (apply unsigned_lit_mod32). try clear SO.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SD _ (qsp) _ SDB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SDB (qsp)%Z v1d (apply unsigned_lit_mod32). try clear SO.
    (* [comment removed for export] *)
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SLO _ (qsp + 1) _ SLOB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SLOB (qsp + 1)%Z v2l (apply unsigned_lit_mod32). try clear SO.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SHI _ (qsp + 1) _ SHIB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SHIB (qsp + 1)%Z v2h (apply unsigned_lit_mod32). try clear SO.
    arun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok a0segs mm SD _ (qsp + 1) _ SDB ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO end.
    wstep. ovw_store SDB (qsp + 1)%Z v2d (apply unsigned_lit_mod32). try clear SO.
    (* [comment removed for export] *)
    arun_to 0x99678%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _) end;
      [st_eq| exact SLOB| exact SHIB| exact SDB| exact SCQ| assumption| assumption| assumption].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_qnext : forall (lo hi d ltLo unLo gu qsp SHl SHh SHd : Z) (slo shi sd : zarr) (Jlo Jhi Jd : list byte)
      (q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q368 : word)
      (xra x5 x6 x7 x10 x11 x18 x23 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo <= hi + 1)%Z -> (0 <= gu <= hi + 1 - unLo)%Z -> (hi < n)%Z -> (0 <= d <= 14)%Z ->
    (1 <= qsp <= 98)%Z ->
    saddr (SLO + 4 * (qsp - 1)) SHl -> saddr (SHI + 4 * (qsp - 1)) SHh -> saddr (SD + 4 * (qsp - 1)) SHd ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z ->
    u32arr a0segs m SLO (ovw slo Jlo 100) -> u32arr a0segs m SHI (ovw shi Jhi 100) -> u32arr a0segs m SD (ovw sd Jd 100) ->
    rw_cells a0segs m (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344
                                   (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) q368 (Z_to_bv 64 hi))) -> mem_inv a0segs m ->
    munch WST me m -> wmono a0segs me m ->
    shzW a0segs WST me SLO (SLO + 400) -> shzW a0segs WST me SHI (SHI + 400) -> shzW a0segs WST me SD (SD + 400) ->
    (forall m' (q376' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x28' x29' x30' x31' : word),
      let kn := (lo + unLo - ltLo - 1)%Z in let km := (hi - gu + 1)%Z in
      let '(f0, f1) := srt2 (lo, kn, d) (km, hi, d) in
      let '(g1, g2) := srt2 f1 (kn + 1, km - 1, d + 1)%Z in
      let '(h0, h1) := srt2 f0 g1 in
      let '(l0, u0, d0) := h0 in let '(l1, u1, d1) := h1 in let '(l2, u2, d2) := g2 in
      u32arr a0segs m' SLO (ovw (zset (zset (zset slo (qsp - 1) l0) qsp l1) (qsp + 1) l2) Jlo 100) ->
      u32arr a0segs m' SHI (ovw (zset (zset (zset shi (qsp - 1) u0) qsp u1) (qsp + 1) u2) Jhi 100) ->
      u32arr a0segs m' SD (ovw (zset (zset (zset sd (qsp - 1) d0) qsp d1) (qsp + 1) d2) Jd 100) ->
      rw_cells a0segs m' (P + 216) (scq_cells Y (mkSCQ q216 q224 q232 q240 q256 q264 q272 (Z_to_bv 64 (qsp + 2)) q320 q328 q336 q344
                                     (Z_to_bv 64 (SLO + 4 * (qsp - 1))) (Z_to_bv 64 qsp) q368 q376')) ->
      mem_inv a0segs m' -> munch WST me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' cSB (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 lo) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23 (Z_to_bv 64 d) x25 x26 x27
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0x99678) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR xra (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 (Z_to_bv 64 gu) (Z_to_bv 64 SHl) (Z_to_bv 64 SHh) (Z_to_bv 64 SHd) (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                          x18 cSB (Z_to_bv 64 (SHI + 4 * (qsp - 1))) (Z_to_bv 64 lo) (Z_to_bv 64 (SD + 4 * (qsp - 1))) x23 (Z_to_bv 64 d) x25 x26 x27
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0x990ec) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi d ltLo unLo gu qsp SHl SHh SHd slo shi sd Jlo Jhi Jd q216 q224 q232 q240 q256 q264 q272 q288 q320 q328 q336 q344 q368
           xra x5 x6 x7 x10 x11 x18 x23 x25 x26 x27 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgu Hhi Hd Hq ASl ASh ASd LJlo LJhi LJd SLOB SHIB SDB SCQ MI MU WM SHZl SHZh SHZd K.
    msenv_open XOK. amenv_open YOK. open_scq_in SCQ.
    cbv zeta in K.
    set (kn := (lo + unLo - ltLo - 1)%Z) in K. set (km := (hi - gu + 1)%Z) in K. unfold srt2 in K. cbv beta iota delta [nsz] in K.
    (* [comment removed for export] *)
    Ltac qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd v0l v0h v0d v1l v1h v1d v2l v2h v2d :=
      arun_to 0x99590%Z;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_push3 qsp v0l v0h v0d v1l v1h v1d v2l v2h v2d SHl SHh SHd slo shi sd Jlo Jhi Jd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| intros v Hv; cbn in Hv; lia| exact ASl| exact ASh| exact ASd| exact LJlo| exact LJhi| exact LJd| exact SLOB| exact SHIB| exact SDB| exact SCQ| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub a0segs); [exact SHZl| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs); [exact SHZh| exact MU| sub_fp_solve| lia| lia]
        | eapply (shzW_sub a0segs); [exact SHZd| exact MU| sub_fp_solve| lia| lia] | ];
      let m' := fresh "m'" in
      intros m' ? ? ? ? ? ?; intros SLO' SHI' SD' SCQ' MI' MU' WM';
      clear SLOB SHIB SDB SCQ MI;
      lazymatch goal with MUx : munch _ ?m0 m', MUo : munch _ _ ?m0 |- _ => transport_after_call a0segs m0 m' MU' WM' end;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact SLO'| exact SHI'| exact SD'| exact SCQ'| exact MI'| exact MU| exact WM].
    (* [comment removed for export] *)
    arun. if_cases Kc1; zify_cond_z Kc1.
    - replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
      arun. if_cases Kc2; zify_cond_z Kc2.
      + replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        arun. if_cases Kc3; zify_cond_z Kc3.
        * replace (kn - lo <? hi - km) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
        * replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
      + replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        arun. if_cases Kc3; zify_cond_z Kc3.
        * replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z.
        * replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z.
    - replace (kn - lo <? hi - km) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
      arun. if_cases Kc2; zify_cond_z Kc2.
      + replace (kn - lo <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
        arun. if_cases Kc3; zify_cond_z Kc3.
        * replace (hi - km <? kn - lo) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
        * replace (hi - km <? kn - lo) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (lo)%Z (kn)%Z (d)%Z (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z.
      + replace (kn - lo <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
        arun. if_cases Kc3; zify_cond_z Kc3.
        * replace (hi - km <? km - 1 - (kn + 1)) with false in K by (symmetry; apply Z.ltb_ge; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (km)%Z (hi)%Z (d)%Z (kn + 1)%Z (km - 1)%Z (d + 1)%Z (lo)%Z (kn)%Z (d)%Z.
        * replace (hi - km <? km - 1 - (kn + 1)) with true in K by (symmetry; apply Z.ltb_lt; lia). cbv beta iota delta [nsz] in K.
          qn_leaf K SLOB SHIB SDB SCQ MI MU WM ASl ASh ASd LJlo LJhi LJd SHZl SHZh SHZd qsp SHl SHh SHd slo shi sd Jlo Jhi Jd (kn + 1)%Z (km - 1)%Z (d + 1)%Z (km)%Z (hi)%Z (d)%Z (lo)%Z (kn)%Z (d)%Z.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_qswap1 : forall (lo hi ltLo unLo unHi gtHi : Z) (a1 : zarr) (sq : scq)
      (x6 x11 x12 x13 x14 x15 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    q368 sq = Z_to_bv 64 lo ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> mem_inv a0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono a0segs me m ->
    frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z me (P + 216) (scq_cells Y sq) -> shzW a0segs [(A1, A1 + ARR1_SIZE)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x6' x10' x11' x12' x28' x29' x30' : word),
      let nn := mmin (ltLo - lo) (unLo - ltLo) in let a1' := mvswap (S (Z.to_nat nn)) a1 lo (unLo - nn) nn in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> mem_inv a0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono a0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 gtHi) x6' (Z_to_bv 64 unHi) (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13 x14 x15 (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                            (Z_to_bv 64 1) cSB x20 (Z_to_bv 64 lo) x22 x23 x24 x25 x26 x27 x28' x29' x30' x31)
                       F (Z_to_bv 64 0x99040) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 gtHi) x6 (Z_to_bv 64 unHi) (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (A1 + 4 * lo)) x11 x12 x13 x14 x15 (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                          x18 cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x98fa0) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi a1 sq x6 x11 x12 x13 x14 x15 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgt Hhi K368 A1OK PR AR1 MI MU WM VQ SH1 K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    pose proof (VQ m MU) as RO_. open_scq_in RO_. rewrite K368 in RO_. wstep. clear RO_. wstep. wstep.
    assert (JOIN :
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 gtHi) x6 (Z_to_bv 64 unHi) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 (A1 + 4 * lo)) (Z_to_bv 64 (unLo - ltLo)) x12 x13 x14 x15 (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                            x18 cSB x20 (Z_to_bv 64 lo) x22 x23 x24 x25 x26 x27 (Z_to_bv 64 (mmin (ltLo - lo) (unLo - ltLo))) x29 x30 x31)
                       F (Z_to_bv 64 0x98fb4) fc None m (seg_rom a0segs))).
    2:{ wstep; if_cases Kc; zify_cond_z Kc.
        - enter_with JOIN. unfold mmin. replace (ltLo - lo <? unLo - ltLo) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep. enter_with JOIN. unfold mmin. replace (ltLo - lo <? unLo - ltLo) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    set (nn := mmin (ltLo - lo) (unLo - ltLo)) in *.
    assert (Hnn : (nn <= ltLo - lo /\ nn <= unLo - ltLo /\ (nn = ltLo - lo \/ nn = unLo - ltLo))%Z).
    { subst nn. unfold mmin. destruct (Z.ltb_spec (ltLo - lo) (unLo - ltLo)); lia. }
    clearbody nn.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - (* [comment removed for export] *)
      rewrite mvswap_S in K. replace (0 <? nn) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact MI| exact MU| exact WM| exact A1OK| exact PR].
    - (* [comment removed for export] *)
      arun_to 0x98fd4%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (A0_vswap1 X Y Q XOK lo hi (S (Z.to_nat nn)) nn lo (unLo - nn)%Z a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub a0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia] |].
      intros m' x29' x30'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      clear AR1 MI. transport_after_call a0segs m m' MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _) end;
        [st_eq| exact AR1'| exact MI'| exact MU| exact WM| exact OK'| exact PR'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma A0_qswap2 : forall (lo hi ltLo unLo unHi gtHi : Z) (a1 : zarr) (sq : scq)
      (x6 x10 x11 x12 x13 x14 x15 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (0 <= lo)%Z -> (lo <= ltLo <= unLo)%Z -> (unLo = unHi + 1)%Z -> (unHi <= gtHi <= hi)%Z -> (hi < n)%Z ->
    q376 sq = Z_to_bv 64 hi ->
    zbok a1 -> pr n a1 0 (n - 1) ->
    u8arr a0segs m A1 (zb8 a1 ARR1_SIZE) -> mem_inv a0segs m ->
    munch [(A1, A1 + ARR1_SIZE)]%Z me m -> wmono a0segs me m ->
    frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z me (P + 216) (scq_cells Y sq) -> frdW a0segs [(A1, A1 + ARR1_SIZE)]%Z me (P + 152) [C8 (Z_to_bv 64 (A1 + 4))] ->
    shzW a0segs [(A1, A1 + ARR1_SIZE)]%Z me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x5' x6' x7' x10' x11' x28' x29' : word),
      let mm := mmin (hi - gtHi) (gtHi - unHi) in let a1' := mvswap (S (Z.to_nat mm)) a1 unLo (hi - mm + 1) mm in
      u8arr a0segs m' A1 (zb8 a1' ARR1_SIZE) -> mem_inv a0segs m' ->
      munch [(A1, A1 + ARR1_SIZE)]%Z me m' -> wmono a0segs me m' -> zbok a1' -> pr n a1' 0 (n - 1) ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' (Z_to_bv 64 (gtHi - unHi)) x13 x14 x15 (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                            (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 x28' x29' x30 x31)
                       F (Z_to_bv 64 0x990ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 gtHi) x6 (Z_to_bv 64 unHi) (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                          (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x99040) fc None m (seg_rom a0segs)).
  Proof.
    intros lo hi ltLo unLo unHi gtHi a1 sq x6 x10 x11 x12 x13 x14 x15 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 me m
           Hlo Hlt Hun Hgt Hhi K376 A1OK PR AR1 MI MU WM VQ V152 SH1 K.
    msenv_open XOK. bz_params.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1.
    cbv zeta in K.
    (* [comment removed for export] *)
    pose proof (VQ m MU) as RO_. open_scq_in RO_. rewrite K376 in RO_. wstep. wstep. wstep.
    assert (JOIN :
      evt a0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp (Z_to_bv 64 gtHi) x6 (Z_to_bv 64 unHi) (me_sp X) (Z_to_bv 64 P)
                            (Z_to_bv 64 hi) (Z_to_bv 64 (mmin (hi - gtHi) (gtHi - unHi))) (Z_to_bv 64 (gtHi - unHi)) x13 x14 x15 (Z_to_bv 64 ltLo) (Z_to_bv 64 unLo)
                            (Z_to_bv 64 1) cSB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x99054) fc None m (seg_rom a0segs))).
    2:{ wstep; if_cases Kc; zify_cond_z Kc.
        - enter_with JOIN. unfold mmin. replace (hi - gtHi <? gtHi - unHi) with true by (symmetry; apply Z.ltb_lt; lia). st_eq.
        - wstep. enter_with JOIN. unfold mmin. replace (hi - gtHi <? gtHi - unHi) with false by (symmetry; apply Z.ltb_ge; lia). st_eq. }
    set (mm := mmin (hi - gtHi) (gtHi - unHi)) in *.
    assert (Hmm : (mm <= hi - gtHi /\ mm <= gtHi - unHi /\ (mm = hi - gtHi \/ mm = gtHi - unHi))%Z).
    { subst mm. unfold mmin. destruct (Z.ltb_spec (hi - gtHi) (gtHi - unHi)); lia. }
    clearbody mm.
    (* [comment removed for export] *)
    wstep; if_cases Kz; [apply blez_taken in Kz; [|lia] | apply blez_not_taken in Kz; [|lia]].
    - rewrite mvswap_S in K. replace (0 <? mm) with false in K by (symmetry; apply Z.ltb_ge; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact MI| exact MU| exact WM| exact A1OK| exact PR].
    - (* [comment removed for export] *)
      pose proof (V152 m MU) as RO2_. arun_to 0x99080%Z. clear RO_ RO2_.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) =>
        enter_with (A0_vswap2 X Y Q XOK lo hi (S (Z.to_nat mm)) mm unLo (hi - mm + 1)%Z a1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm0 mm0) end;
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact A1OK| exact PR| exact AR1| exact MI| apply munch_refl| apply wmono_refl
        | eapply (shzW_sub a0segs); [exact SH1| exact MU| sub_fp_solve| lia| lia] |].
      intros m' x28' x29'. cbv zeta. intros AR1' MI' MU' WM' OK' PR'.
      clear AR1 MI. transport_after_call a0segs m m' MU' WM'.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm0 _) => enter_with (K mm0 _ _ _ _ _ _ _) end;
        [st_eq| exact AR1'| exact MI'| exact MU| exact WM| exact OK'| exact PR'].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0MS.

End ACeilS1.
