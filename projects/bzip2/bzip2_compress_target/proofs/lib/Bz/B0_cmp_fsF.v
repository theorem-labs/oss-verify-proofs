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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_fsW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Section B0FS.
  Variable X : fsenv. Variable Y : afenv. Variable Q : machine_state -> Prop. Variables Hh qsp l1 r1 nnd : Z.
  Variables SHlo SHhi : Z.
  Hypothesis XOK : fsenv_ok X. Hypothesis XSEP : fsenv_sep X. Hypothesis YOK : afenv_ok X Y. Hypothesis YSEP : afenv_sep X Y.
  Notation usp := (bv_unsigned (fe_sp X)). Notation P := (ae_P Y). Notation SLO := (ae_SLO Y). Notation SHI := (ae_SHI Y).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X).
  Hypothesis ASlo : saddr (SLO + 4 * (qsp - 1)) SHlo. Hypothesis AShi : saddr (SHI + 4 * (qsp - 1)) SHhi.
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NA2 := (18446744073709551615 - fe_A2 X)%Z.
  (* [comment removed for export] *)
  Notation QS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 1) (Z_to_bv 64 A2) (Z_to_bv 64 r1) (Z_to_bv 64 A1) cSB (Z_to_bv 64 1) (Z_to_bv 64 FT) (Z_to_bv 64 (-1)) (Z_to_bv 64 l1) (Z_to_bv 64 NA2) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation SCf rr lt gt := (SCb X Y nnd Hh (Z_to_bv 64 rr) lt gt (Z_to_bv 64 SHhi) (Z_to_bv 64 SHlo) (Z_to_bv 64 qsp)).
  Definition med_idx (r3 lo hi : Z) : Z := if (r3 =? 0)%Z then lo else if (r3 =? 1)%Z then ((lo + hi) / 2)%Z else hi.
  Notation WM := [(P + 112, P + 144)]%Z.
  (* [comment removed for export] *)

  Ltac prep XOK XSEP fm ec :=
    fsenv_open XOK; afenv_open YOK;
    let SP := fresh "SP" in pose proof XSEP as SP; unfold fsenv_sep, apartv in SP; cps_destruct SP as (?AP12 & _ & _);
    let L1 := fresh "L1" in let L2 := fresh "L2" in
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1; pose proof (zb8_length ec ARR2_SIZE ltac:(lia)) as L2.
  Ltac rd_fm fm j AR1 FMOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 b0segs mm A1 fm ARR1_SIZE j _ AR1 ltac:(lia) ltac:(lia) FMOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac rd_ec ec x AR2 ECOK :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zb8_read4 b0segs mm A2 ec ARR2_SIZE x _ AR2 ltac:(lia) ltac:(lia) ECOK ltac:(unfold wa; f_equal; lia)) as RD end;
    wstep; clear RD.
  Ltac st_fm fm i AR1 :=
    let SO := fresh "SO" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_storeN_ok b0segs mm A1 _ (4 * i) 4 _ AR1 ltac:(lia) ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end;
    wstep; zb8_store4 AR1 i; try clear SO.
  (* [comment removed for export] *)
  Ltac key_leftB B i :=
    try lazymatch goal with |- context [Z_to_bv 64 (?x + B)] => replace (x + B)%Z with (B + 4 * i)%Z by lia end.

  (* [comment removed for export] *)
  Lemma B0_qmed : forall (hi lo rr : Z) (fm ec : zarr) (me m : word -> option byte) (ra t0 t1 t2 a0 a1 a2 a3 a7 t3 t4 t5 t6 v128 v136 : word),
    (0 <= lo)%Z -> (lo + 10 <= hi < nb)%Z -> (0 <= rr < 32768)%Z -> (1 <= qsp <= 99)%Z ->
    fm_range fm nb -> ec_range ec nb -> zbok fm -> zbok ec ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m A2 (zb8 ec ARR2_SIZE) -> rw_cells b0segs m (P + 72) (SCf rr v128 v136) -> mem_inv b0segs m ->
    munch WM me m -> wmono b0segs me m ->
    shzW b0segs WM me A1 (A1 + ARR1_SIZE) -> shzW b0segs WM me A2 (A2 + ARR2_SIZE) ->
    (forall m' (x12 x13 x17 : word), let r' := ((rr * 7621 + 1) mod 32768)%Z in let med := rd32 ec (rd32 fm (med_idx (r' mod 3) lo hi)) in
      u8arr b0segs m' A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 ec ARR2_SIZE) -> rw_cells b0segs m' (P + 72) (SCf r' (Z_to_bv 64 lo) (Z_to_bv 64 hi)) -> mem_inv b0segs m' ->
      munch WM me m' -> wmono b0segs me m' -> (0 <= med < nb)%Z ->
      evt b0segs Q (MS (QS ra t0 (Z_to_bv 64 lo) (Z_to_bv 64 hi) a0 a1 x12 x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (qsp - 1)) x17 t3 t4 (Z_to_bv 64 med) t6)
                       F (Z_to_bv 64 0xa611c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (qsp - 1)) a7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa5f90) fc None m (seg_rom b0segs)).
  Proof.
    intros hi lo rr fm ec me m ra t0 t1 t2 a0 a1 a2 a3 a7 t3 t4 t5 t6 v128 v136 Hlo Hhi Hrr Hq FMR ECR FMOK' ECOK' AR1 AR2 SCH MI MU WMo SH1 SH2 K. cbv zeta in K.
    prep XOK XSEP fm ec. bz_params. unfold SCb in SCH, K.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. rewrite lcg_hi15 by lia.
    try replace (7621 * rr + 1)%Z with (rr * 7621 + 1)%Z by lia.
    set (r' := ((rr * 7621 + 1) mod 32768)%Z) in *. assert (Hr' : (0 <= r' < 32768)%Z) by (subst r'; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. rewrite lcg_div3 by lia. try replace (7621 * rr + 1)%Z with (rr * 7621 + 1)%Z by lia. fold r'.
    assert (Hq3 : (0 <= r' / 3 < 10923)%Z) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Z.div_mod r' 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound r' 3 ltac:(lia)) as Hm3.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.div_mul (r' - r' / 3 - r' / 3 * 2) 281474976710656) by lia.
    replace (r' - r' / 3 - r' / 3 * 2)%Z with (r' mod 3)%Z by lia.
    (* [comment removed for export] *)
    assert (TAIL : forall m1 (idx : Z) (x13 x17 : word), idx = med_idx (r' mod 3) lo hi ->
      rw_cells b0segs m1 (P + 72) (SCf r' v128 v136) ->
      u8arr b0segs m1 A1 (zb8 fm ARR1_SIZE) -> u8arr b0segs m1 A2 (zb8 ec ARR2_SIZE) -> mem_inv b0segs m1 -> munch WM me m1 -> wmono b0segs me m1 ->
      evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 (Z_to_bv 64 (A1 + 4 * idx)) x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (qsp - 1)) x17 t3 t4 t5 t6)
                       F (Z_to_bv 64 0xa60c4) fc None m1 (seg_rom b0segs))).
    { intros m1 idx x13 x17 Hidx SC1 AR1' AR2' MI1 MU1 WM1. unfold SCb in SC1.
      assert (Hix : (lo <= idx <= hi)%Z).
      { subst idx. unfold med_idx. destruct (Z.eqb_spec (r' mod 3) 0); [lia|]. destruct (Z.eqb_spec (r' mod 3) 1); [|lia].
        split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]. }
      pose proof (proj2 FMR idx ltac:(lia)) as Fi. pose proof (ECR (rd32 fm idx) ltac:(lia)) as Ei.
      (* [comment removed for export] *)
      rd_fm fm idx AR1' FMOK'. try rewrite (zx32_of_Z (rd32 fm idx)) by lia.
      (* [comment removed for export] *)
      brun_to 0xa60d0%Z. key_leftB (fe_A2 X) (rd32 fm idx).
      (* [comment removed for export] *)
      brun. rd_ec ec (rd32 fm idx) AR2' ECOK'. try rewrite (sx32_of_Z (rd32 ec (rd32 fm idx))) by lia.
      (* [comment removed for export] *)
      wstep. wstep. rewrite (Z.div_mul (qsp - 1) 4294967296) by lia || rewrite (Z.div_mul (qsp + -1) 4294967296) by lia || idtac.
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      subst idx. enter_with (K _ _ _ _); [st_eq| exact AR1'| exact AR2'| exact SC1| exact MI1| exact MU1| exact WM1| lia]. }
    (* [comment removed for export] *)
    wstep; if_cases K1; zify_cond_z K1.
    - (* [comment removed for export] *)
      brun_to 0xa6034%Z.
      replace (Z.shiftr (lo + hi) 1) with ((lo + hi) / 2)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity) || idtac.
      assert (Hmid : (lo <= (lo + hi) / 2 <= hi)%Z) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]).
      (* [comment removed for export] *)
      brun_to 0xa60c4%Z.
      enter_with (TAIL _ ((lo + hi) / 2)%Z _ _); [st_eq| unfold med_idx; destruct (Z.eqb_spec (r' mod 3) 0); [lia|]; destruct (Z.eqb_spec (r' mod 3) 1); [reflexivity| lia]| exact SCH| exact AR1| exact AR2| exact MI| exact MU| exact WMo].
    - (* [comment removed for export] *)
      wstep; if_cases K2; zify_cond_z K2.
      + (* [comment removed for export] *)
        brun_to 0xa60c4%Z.
        enter_with (TAIL _ hi _ _); [st_eq| unfold med_idx; destruct (Z.eqb_spec (r' mod 3) 0); [lia|]; destruct (Z.eqb_spec (r' mod 3) 1); [lia| reflexivity]| exact SCH| exact AR1| exact AR2| exact MI| exact MU| exact WMo].
      + (* [comment removed for export] *)
        brun_to 0xa60c4%Z.
        enter_with (TAIL _ lo _ _); [st_eq| unfold med_idx; rewrite K2; reflexivity| exact SCH| exact AR1| exact AR2| exact MI| exact MU| exact WMo].
  Qed.

  Notation WS := [(A1, A1 + ARR1_SIZE)]%Z.

  (* [comment removed for export] *)
  Lemma B0_vsw1 : forall (c : nat) (y1 y2 rr : Z) (fm : zarr) (me m : word -> option byte) (ra t0 t1 t2 a0 a1 a4 a5 a7 t3 t4 v128 v136 : word),
    (1 <= c)%nat -> (0 <= y1)%Z -> (y1 + Z.of_nat c <= nb)%Z -> (0 <= y2)%Z -> (y2 + Z.of_nat c <= nb)%Z ->
    fm_range fm nb -> zbok fm ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> rw_cells b0segs m (P + 72) (SCf rr v128 v136) -> mem_inv b0segs m -> munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x1 x5 x6 x12 x13 x16 x17 x28 x30 x31 : word), let fm' := fvswap c fm y1 y2 (Z.of_nat c) in
      u8arr b0segs m' A1 (zb8 fm' ARR1_SIZE) -> rw_cells b0segs m' (P + 72) (SCf rr v128 v136) -> mem_inv b0segs m' -> munch WS me m' -> wmono b0segs me m' ->
      fm_range fm' nb -> zbok fm' ->
      evt b0segs Q (MS (QS x1 x5 x6 t2 a0 a1 x12 x13 a4 a5 x16 x17 x28 t4 x30 x31)
                       F (Z_to_bv 64 0xa65d0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 t2 a0 a1 (Z_to_bv 64 (A1 + 4 * y1)) (Z_to_bv 64 y2) a4 a5 (Z_to_bv 64 (A1 + 4 * y1)) a7 t3 t4 (Z_to_bv 64 (Z.of_nat c + 1)) (Z_to_bv 64 y1))
                     F (Z_to_bv 64 0xa650c) fc None m (seg_rom b0segs)).
  Proof.
    induction c as [|c IH]; intros y1 y2 rr fm me m ra t0 t1 t2 a0 a1 a4 a5 a7 t3 t4 v128 v136 Hc Hy1 Hy1c Hy2 Hy2c FMR FMOK' AR1 SCH MI MU WMo SH1 K; cbv zeta in K; [lia|].
    fsenv_open XOK. afenv_open YOK. bz_params. pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. unfold SCb in SCH, K.
    rewrite fvswap_S in K. replace (0 <? Z.of_nat (S c))%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (proj2 FMR y1 ltac:(lia)) as F1. pose proof (proj2 FMR y2 ltac:(lia)) as F2.
    (* [comment removed for export] *)
    brun_to 0xa653c%Z. try rewrite (sx32_of_Z y2) by lia. key_leftB (fe_A1 X) y2.
    (* [comment removed for export] *)
    brun. rd_fm fm y1 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y1)) by lia.
    (* [comment removed for export] *)
    brun. rd_fm fm y2 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y2)) by lia.
    (* [comment removed for export] *)
    st_fm fm y1 AR1. rewrite (unsigned_lit (rd32 fm y2)) in AR1 by lia.
    pose proof (zb8_length (wr32 fm y1 (rd32 fm y2)) ARR1_SIZE ltac:(lia)) as L1'.
    st_fm (wr32 fm y1 (rd32 fm y2)) y2 AR1. rewrite (unsigned_lit (rd32 fm y1)) in AR1 by lia.
    change (wr32 (wr32 fm y1 (rd32 fm y2)) y2 (rd32 fm y1)) with (fswap fm y1 y2) in AR1.
    assert (FMR1 : fm_range (fswap fm y1 y2) nb) by (apply fswap_range; [exact FMR| lia| lia]).
    assert (FMOK1 : zbok (fswap fm y1 y2)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
    (* [comment removed for export] *)
    brun_to 0xa65a8%Z.
    try rewrite (sx32_of_Z (Z.of_nat c + 1 - 1)) by lia. try rewrite (sx32_of_Z (Z.of_nat (S c) + 1 - 1)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - replace (Z.of_nat (S c) - 1)%Z with (Z.of_nat c) in K by lia.
      enter_with (IH (y1 + 1)%Z (y2 + 1)%Z rr (fswap fm y1 y2) me); [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact FMOK1| exact AR1| exact SCH| exact MI| exact MU| exact WMo| exact SH1|].
      intros m' x1 x5 x6 x12 x13 x16 x17 x28 x30 x31. cbv zeta. exact (K m' x1 x5 x6 x12 x13 x16 x17 x28 x30 x31).
    - assert (c = 0)%nat by lia. subst c. cbn [fvswap Z.of_nat] in K. replace (0 <? 1 - 1)%Z with false in K by reflexivity.
      (* [comment removed for export] *)
      wstep.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact SCH| exact MI| exact MU| exact WMo| exact FMR1| exact FMOK1].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_vsw2 : forall (c : nat) (y1 y2 rr : Z) (fm : zarr) (me m : word -> option byte) (ra t0 t1 a0 a1 a3 a4 a5 a6 a7 t4 v128 v136 : word),
    (1 <= c)%nat -> (0 <= y1)%Z -> (y1 + Z.of_nat c <= nb)%Z -> (0 <= y2)%Z -> (y2 + Z.of_nat c <= nb)%Z ->
    fm_range fm nb -> zbok fm ->
    u8arr b0segs m A1 (zb8 fm ARR1_SIZE) -> rw_cells b0segs m (P + 72) (SCf rr v128 v136) -> mem_inv b0segs m -> munch WS me m -> wmono b0segs me m ->
    shzW b0segs WS me A1 (A1 + ARR1_SIZE) ->
    (forall m' (x1 x5 x6 x7 x12 x13 x17 x28 x30 x31 : word), let fm' := fvswap c fm y1 y2 (Z.of_nat c) in
      u8arr b0segs m' A1 (zb8 fm' ARR1_SIZE) -> rw_cells b0segs m' (P + 72) (SCf rr v128 v136) -> mem_inv b0segs m' -> munch WS me m' -> wmono b0segs me m' ->
      fm_range fm' nb -> zbok fm' ->
      evt b0segs Q (MS (QS x1 x5 x6 x7 a0 a1 x12 x13 a4 a5 a6 x17 x28 t4 x30 x31)
                       F (Z_to_bv 64 0xa66f0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS ra t0 t1 (Z_to_bv 64 (A1 + 4 * y1)) a0 a1 (Z_to_bv 64 (A1 + 4 * y1)) a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat c + 1)) t4 (Z_to_bv 64 y2) (Z_to_bv 64 y1))
                     F (Z_to_bv 64 0xa662c) fc None m (seg_rom b0segs)).
  Proof.
    induction c as [|c IH]; intros y1 y2 rr fm me m ra t0 t1 a0 a1 a3 a4 a5 a6 a7 t4 v128 v136 Hc Hy1 Hy1c Hy2 Hy2c FMR FMOK' AR1 SCH MI MU WMo SH1 K; cbv zeta in K; [lia|].
    fsenv_open XOK. afenv_open YOK. bz_params. pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1. unfold SCb in SCH, K.
    rewrite fvswap_S in K. replace (0 <? Z.of_nat (S c))%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (proj2 FMR y1 ltac:(lia)) as F1. pose proof (proj2 FMR y2 ltac:(lia)) as F2.
    (* [comment removed for export] *)
    brun_to 0xa6658%Z. key_leftB (fe_A1 X) y2.
    (* [comment removed for export] *)
    brun. rd_fm fm y1 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y1)) by lia.
    (* [comment removed for export] *)
    brun. rd_fm fm y2 AR1 FMOK'. try rewrite (sx32_of_Z (rd32 fm y2)) by lia.
    (* [comment removed for export] *)
    st_fm fm y1 AR1. rewrite (unsigned_lit (rd32 fm y2)) in AR1 by lia.
    pose proof (zb8_length (wr32 fm y1 (rd32 fm y2)) ARR1_SIZE ltac:(lia)) as L1'.
    st_fm (wr32 fm y1 (rd32 fm y2)) y2 AR1. rewrite (unsigned_lit (rd32 fm y1)) in AR1 by lia.
    change (wr32 (wr32 fm y1 (rd32 fm y2)) y2 (rd32 fm y1)) with (fswap fm y1 y2) in AR1.
    assert (FMR1 : fm_range (fswap fm y1 y2) nb) by (apply fswap_range; [exact FMR| lia| lia]).
    assert (FMOK1 : zbok (fswap fm y1 y2)) by (unfold fswap; apply zbok_wr32, zbok_wr32; exact FMOK').
    (* [comment removed for export] *)
    brun_to 0xa66c8%Z.
    try rewrite (sx32_of_Z (Z.of_nat c + 1 - 1)) by lia. try rewrite (sx32_of_Z (Z.of_nat (S c) + 1 - 1)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - replace (Z.of_nat (S c) - 1)%Z with (Z.of_nat c) in K by lia.
      enter_with (IH (y1 + 1)%Z (y2 + 1)%Z rr (fswap fm y1 y2) me); [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact FMOK1| exact AR1| exact SCH| exact MI| exact MU| exact WMo| exact SH1|].
      intros m' x1 x5 x6 x7 x12 x13 x17 x28 x30 x31. cbv zeta. exact (K m' x1 x5 x6 x7 x12 x13 x17 x28 x30 x31).
    - assert (c = 0)%nat by lia. subst c. cbn [fvswap Z.of_nat] in K. replace (0 <? 1 - 1)%Z with false in K by reflexivity.
      (* [comment removed for export] *)
      wstep.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact SCH| exact MI| exact MU| exact WMo| exact FMR1| exact FMOK1].
  Qed.

  (* [comment removed for export] *)
  Definition qtail (lo hi rr' : Z) (slo shi : zarr) (pf : fpart) : fqs :=
    let fm := fp_fm pf in let unLo := fp_unLo pf in let unHi := fp_unHi pf in let ltLo := fp_ltLo pf in let gtHi := fp_gtHi pf in
    if (gtHi <? ltLo)%Z then FQS fm (qsp - 1) slo shi rr'
    else
      let n := fmin (ltLo - lo) (unLo - ltLo) in
      let fm1 := fvswap (S (Z.to_nat n)) fm lo (unLo - n) n in
      let m := fmin (hi - gtHi) (gtHi - unHi) in
      let fm2 := fvswap (S (Z.to_nat m)) fm1 unLo (hi - m + 1) m in
      let n' := (lo + unLo - ltLo - 1)%Z in
      let m' := (hi - (gtHi - unHi) + 1)%Z in
      let q2 := FQS fm2 (qsp - 1) slo shi rr' in
      if (hi - m' <? n' - lo)%Z then fpush (fpush q2 lo n') m' hi else fpush (fpush q2 m' hi) lo n'.

  (* [comment removed for export] *)
  Definition stk_def (slo shi : zarr) (k : Z) : Prop := forall i, (0 <= i < k)%Z -> zdef slo i = true /\ zdef shi i = true.

  Lemma ovw_skip_redundant : forall a J n i v j w, zdef a i = true -> zget a i = v ->
    ovw (zset (zset a i v) j w) J n = ovw (zset a j w) J n.
  Proof.
    intros a J n i v j w Hd Hg. apply ovw_ext. intros k Hk. rewrite !zdef_zset, !zget_zset.
    destruct (Z.eqb_spec k j); [split; reflexivity|]. destruct (Z.eqb_spec k i) as [->|]; [rewrite Hd, Hg; split; reflexivity| split; reflexivity].
  Qed.

  Notation WQ := [(A1, A1 + ARR1_SIZE); (P + 112, P + 216); (SLO, SLO + 400); (SHI, SHI + 400)]%Z.
  Notation cA0 := (Z_to_bv 64 (SLO + 4 * (qsp - 1))). Notation cA1 := (Z_to_bv 64 (SHI + 4 * (qsp - 1))). Notation cA6 := (Z_to_bv 64 (qsp - 1)).
  Ltac store_addr E' :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?ad ?bs) _) =>
      replace (write_to_mem m0 ad bs) with (write_to_mem m0 (wa E') bs) by (f_equal; unfold wa; f_equal; lia) end.
  (* [comment removed for export] *)
  Ltac sub_chk := wstep; wstep; (wstep; notrap); demod.

  (* [comment removed for export] *)
  Lemma B0_qpush : forall (pf : fpart) (med hi lo rr' : Z) (slo shi : zarr) (Jlo Jhi : list byte) (me m : word -> option byte) (x1 x5 x6 x12 x13 x17 x28 x31 : word),
    (0 <= lo)%Z -> (lo + 10 <= hi < nb)%Z -> (1 <= qsp <= 98)%Z -> fp_ok lo hi pf -> (fp_unHi pf < fp_unLo pf)%Z ->
    fm_range (fp_fm pf) nb -> zbok (fp_fm pf) -> stk_def slo shi qsp -> zget slo (qsp - 1) = lo -> zget shi (qsp - 1) = hi ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z ->
    u8arr b0segs m A1 (zb8 (fp_fm pf) ARR1_SIZE) -> rw_cells b0segs m (P + 72) (SCf rr' (Z_to_bv 64 (fp_ltLo pf)) (Z_to_bv 64 (fp_gtHi pf))) ->
    u32arr b0segs m SHI (ovw shi Jhi 100) -> u32arr b0segs m SLO (ovw slo Jlo 100) -> mem_inv b0segs m ->
    munch WQ me m -> wmono b0segs me m ->
    shzW b0segs WQ me A1 (A1 + ARR1_SIZE) -> shzW b0segs WQ me SLO (SLO + 400) -> shzW b0segs WQ me SHI (SHI + 400) ->
    (forall m' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y17 y28 y29 y30 y31 : word), let q' := qtail lo hi rr' slo shi pf in
      u8arr b0segs m' A1 (zb8 (fq_fm q') ARR1_SIZE) -> rw_cells b0segs m' (P + 72) (SCf rr' (Z_to_bv 64 (fp_ltLo pf)) (Z_to_bv 64 (fp_gtHi pf))) ->
      u32arr b0segs m' SHI (ovw (fq_shi q') Jhi 100) -> u32arr b0segs m' SLO (ovw (fq_slo q') Jlo 100) -> mem_inv b0segs m' ->
      munch WQ me m' -> wmono b0segs me m' ->
      fm_range (fq_fm q') nb -> zbok (fq_fm q') -> stk_def (fq_slo q') (fq_shi q') (fq_sp q') -> (0 <= fq_sp q' <= qsp + 1)%Z -> fq_r q' = rr' ->
      evt b0segs Q (MS (QS y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 (Z_to_bv 64 (fq_sp q')) y17 y28 y29 y30 y31)
                       F (Z_to_bv 64 0xa6838) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (QS x1 x5 x6 (Z_to_bv 64 (fp_unHi pf)) cA0 cA1 x12 x13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) cA6 x17 x28 (Z_to_bv 64 (fp_unLo pf)) (Z_to_bv 64 med) x31)
                     F (Z_to_bv 64 0xa64ac) fc None m (seg_rom b0segs)).
  Proof.
    intros pf med hi lo rr' slo shi Jlo Jhi me m x1 x5 x6 x12 x13 x17 x28 x31 Hlo Hhi Hq OK Hbr FMR FMOK' SD Glo Ghi LJlo LJhi AR1 SCH SHIc SLOc MI MU WMo SH1 SHl SHh K. cbv zeta in K.
    destruct pf as [fm unLo unHi ltLo gtHi]. unfold fp_ok in OK. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in *.
    fsenv_open XOK. afenv_open YOK. pose proof YSEP as SPY. unfold afenv_sep, apartv in SPY. cps_destruct SPY as (AP1B & _ & _).
    bz_params. pose proof (SCb_rd128 b0segs m _ _ _ _ _ _ _ _ _ _ SCH) as RD1. pose proof (SCb_rd136 b0segs m _ _ _ _ _ _ _ _ _ _ SCH) as RD2.
    unfold SCb in SCH, K. unfold qtail in K. cbn [fp_fm fp_unLo fp_unHi fp_ltLo fp_gtHi] in K.
    pose proof (zb8_length fm ARR1_SIZE ltac:(lia)) as L1.
    pose proof (ovw_length shi Jhi 100 ltac:(lia)) as LH. pose proof (ovw_length slo Jlo 100 ltac:(lia)) as LL.
    (* [comment removed for export] *)
    wstep. clear RD1. try rewrite (sx32_of_Z ltLo) by lia. wstep. clear RD2. try rewrite (sx32_of_Z gtHi) by lia. try rewrite (sx32_of_Z_signed gtHi) by lia.
    wstep; if_cases Kg; zify_cond_z Kg.
    { (* [comment removed for export] *)
      replace (gtHi <? ltLo)%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
      enter_with (K m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1| exact SCH| exact SHIc| exact SLOc| exact MI| exact MU| exact WMo| exact FMR| exact FMOK'| | lia| reflexivity].
      intros i Hi. apply SD. lia. }
    replace (gtHi <? ltLo)%Z with false in K by (symmetry; apply Z.ltb_ge; lia).
    set (n := fmin (ltLo - lo) (unLo - ltLo)) in K.
    assert (Hn : ((ltLo - lo < unLo - ltLo)%Z /\ n = (ltLo - lo)%Z) \/ ((unLo - ltLo <= ltLo - lo)%Z /\ n = (unLo - ltLo)%Z)) by (subst n; unfold fmin; destruct (Z.ltb_spec (ltLo - lo) (unLo - ltLo)); lia).
    set (mm := fmin (hi - gtHi) (gtHi - unHi)) in K.
    assert (Hm : ((hi - gtHi < gtHi - unHi)%Z /\ mm = (hi - gtHi)%Z) \/ ((gtHi - unHi <= hi - gtHi)%Z /\ mm = (gtHi - unHi)%Z)) by (subst mm; unfold fmin; destruct (Z.ltb_spec (hi - gtHi) (gtHi - unHi)); lia).
    set (fm1 := fvswap (S (Z.to_nat n)) fm lo (unLo - n) n) in K.
    set (fm2 := fvswap (S (Z.to_nat mm)) fm1 unLo (hi - mm + 1) mm) in K.
    set (n' := (lo + unLo - ltLo - 1)%Z) in K. set (m' := (hi - (gtHi - unHi) + 1)%Z) in K.
    clearbody n mm.
    (* [comment removed for export] *)
    assert (T3 : forall m3 (y1 y5 y6 y7 y12 y13 y17 y28 y30 y31 : word),
      u8arr b0segs m3 A1 (zb8 fm2 ARR1_SIZE) -> mem_inv b0segs m3 ->
      munch WQ me m3 -> wmono b0segs me m3 -> fm_range fm2 nb -> zbok fm2 ->
      rw_cells b0segs m3 (P + 72) (SCf rr' (Z_to_bv 64 ltLo) (Z_to_bv 64 gtHi)) ->
      u32arr b0segs m3 SHI (ovw shi Jhi 100) -> u32arr b0segs m3 SLO (ovw slo Jlo 100) ->
      evt b0segs Q (MS (QS y1 y5 y6 y7 cA0 cA1 y12 y13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (gtHi - unHi)) y17 y28 (Z_to_bv 64 unLo) y30 y31)
                       F (Z_to_bv 64 0xa66f0) fc None m3 (seg_rom b0segs))).
    { intros m3 y1 y5 y6 y7 y12 y13 y17 y28 y30 y31 AR1' MI3 MU3 WM3 FMR2 FMOK2 SC3 SHI3 SLO3. unfold SCb in SC3.
      (* [comment removed for export] *)
      sub_chk.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (lo + unLo)) by lia. wstep. sub_chk.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z_signed (lo + unLo - ltLo - 1)) by lia. try rewrite (sx32_of_Z_signed (lo + unLo - ltLo + -1)) by lia.
      wstep. try rewrite (sx32_of_Z (lo + unLo - ltLo)) by lia. (wstep; notrap).
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (gtHi - unHi)) by lia. sub_chk.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (hi - (gtHi - unHi) + 1)) by lia. wstep. try rewrite (sx32_of_Z (hi - (gtHi - unHi))) by lia. (wstep; notrap).
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z_signed (lo + unLo - ltLo - 1 - lo)) by lia. try rewrite (sx32_of_Z_signed (lo + unLo - ltLo + -1 - lo)) by lia. wstep. (wstep; notrap).
      (* [comment removed for export] *)
      sub_chk. wstep. try rewrite (sx32_of_Z_signed (hi - (hi - (gtHi - unHi) + 1))) by lia.
      (* [comment removed for export] *)
      wstep. wstep. wstep. rewrite (Z.div_mul qsp 4294967296) by lia || idtac.
      (* [comment removed for export] *)
      wstep; if_cases Kp; zify_cond_z Kp.
      - (* [comment removed for export] *)
        replace (hi - m' <? n' - lo)%Z with false in K by (symmetry; apply Z.ltb_ge; subst n' m'; lia).
        (* [comment removed for export] *)
        brun.
        pose proof (u32arr_store_ok b0segs m3 SLO _ (qsp - 1) _ SLO3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
        wstep. store_addr (SLO + 4 * (qsp - 1))%Z. ovw_store SLO3 (qsp - 1)%Z m' (subst m'; wval_lit). try clear SO.
        (* [comment removed for export] *)
        brun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok b0segs mm SLO _ qsp _ SLO3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
        wstep. store_addr (SLO + 4 * qsp)%Z. ovw_store SLO3 qsp lo wval_lit. try clear SO2.
        (* [comment removed for export] *)
        brun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok b0segs mm SHI _ qsp _ SHI3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
        wstep. store_addr (SHI + 4 * qsp)%Z. ovw_store SHI3 qsp n' (subst n'; rewrite unsigned_lit_mod32; Z.div_mod_to_equations; lia). try clear SO3.
        (* [comment removed for export] *)
        wstep. wstep.
        rewrite <- (ovw_skip_redundant shi Jhi 100 (qsp - 1) hi qsp n') in SHI3 by (try apply SD; try exact Ghi; lia).
        unfold fpush in K. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
        enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact SC3| | | exact MI3| exact MU3| exact WM3| exact FMR2| exact FMOK2| | lia| reflexivity].
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SHI3.
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SLO3.
        + intros i Hi. rewrite !zdef_zset. destruct (Z.eqb_spec i (qsp - 1 + 1)); [split; reflexivity|]. destruct (Z.eqb_spec i (qsp - 1)); [split; reflexivity|]. cbn [orb]. apply SD. lia.
      - (* [comment removed for export] *)
        replace (hi - m' <? n' - lo)%Z with true in K by (symmetry; apply Z.ltb_lt; subst n' m'; lia).
        (* [comment removed for export] *)
        brun.
        pose proof (u32arr_store_ok b0segs m3 SHI _ (qsp - 1) _ SHI3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO.
        wstep. store_addr (SHI + 4 * (qsp - 1))%Z. ovw_store SHI3 (qsp - 1)%Z n' (subst n'; rewrite unsigned_lit_mod32; Z.div_mod_to_equations; lia). try clear SO.
        (* [comment removed for export] *)
        brun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok b0segs mm SLO _ qsp _ SLO3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO2 end.
        wstep. store_addr (SLO + 4 * qsp)%Z. ovw_store SLO3 qsp m' (subst m'; wval_lit). try clear SO2.
        (* [comment removed for export] *)
        brun.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u32arr_store_ok b0segs mm SHI _ qsp _ SHI3 ltac:(rewrite ovw_length_nat; lia) eq_refl) as SO3 end.
        wstep. store_addr (SHI + 4 * qsp)%Z. ovw_store SHI3 qsp hi wval_lit. try clear SO3.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        rewrite <- (ovw_skip_redundant slo Jlo 100 (qsp - 1) lo qsp m') in SLO3 by (try apply SD; try exact Glo; lia).
        unfold fpush in K. cbn [fq_fm fq_sp fq_slo fq_shi fq_r] in K.
        enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact SC3| | | exact MI3| exact MU3| exact WM3| exact FMR2| exact FMOK2| | lia| reflexivity].
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SHI3.
        + replace (qsp - 1 + 1)%Z with qsp by lia. exact SLO3.
        + intros i Hi. rewrite !zdef_zset. destruct (Z.eqb_spec i (qsp - 1 + 1)); [split; reflexivity|]. destruct (Z.eqb_spec i (qsp - 1)); [split; reflexivity|]. cbn [orb]. apply SD. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    sub_chk. sub_chk. wstep. try rewrite (sx32_of_Z (unLo - ltLo)) by lia. wstep. try rewrite (sx32_of_Z (ltLo - lo)) by lia.
    (* [comment removed for export] *)
    assert (T1 : forall (x13' : word),
      evt b0segs Q (MS (QS x1 (Z_to_bv 64 gtHi) x6 (Z_to_bv 64 unHi) cA0 cA1 (Z_to_bv 64 (unLo - ltLo)) x13' (Z_to_bv 64 hi) (Z_to_bv 64 lo) cA6 (Z_to_bv 64 ltLo) x28 (Z_to_bv 64 unLo) (Z_to_bv 64 n) x31)
                       F (Z_to_bv 64 0xa64e0) fc None m (seg_rom b0segs))).
    2:{ wstep; if_cases Kn; zify_cond_z Kn.
        - enter_with (T1 _); st_eq.
        - wstep. enter_with (T1 _); st_eq. }
    intros x13'.
    (* [comment removed for export] *)
    assert (T2 : forall m2 (y1 y5 y6 y12 y13 y16 y17 y28 y30 y31 : word),
      u8arr b0segs m2 A1 (zb8 fm1 ARR1_SIZE) -> mem_inv b0segs m2 ->
      munch WQ me m2 -> wmono b0segs me m2 -> fm_range fm1 nb -> zbok fm1 ->
      rw_cells b0segs m2 (P + 72) (SCf rr' (Z_to_bv 64 ltLo) (Z_to_bv 64 gtHi)) ->
      u32arr b0segs m2 SHI (ovw shi Jhi 100) -> u32arr b0segs m2 SLO (ovw slo Jlo 100) ->
      evt b0segs Q (MS (QS y1 y5 y6 (Z_to_bv 64 unHi) cA0 cA1 y12 y13 (Z_to_bv 64 hi) (Z_to_bv 64 lo) y16 y17 y28 (Z_to_bv 64 unLo) y30 y31)
                       F (Z_to_bv 64 0xa65d0) fc None m2 (seg_rom b0segs))).
    { intros m2 y1 y5 y6 y12 y13 y16 y17 y28 y30 y31 AR1' MI2 MU2 WM2 FMR1 FMOK1 SC2 SHI2 SLO2. unfold SCb in SC2.
      pose proof (zb8_length fm1 ARR1_SIZE ltac:(lia)) as L1'.
      (* [comment removed for export] *)
      wstep. sub_chk. sub_chk. wstep. try rewrite (sx32_of_Z (gtHi - unHi)) by lia. wstep. try rewrite (sx32_of_Z (hi - gtHi)) by lia.
      (* [comment removed for export] *)
      assert (T2b :
        evt b0segs Q (MS (QS y1 y5 y6 (Z_to_bv 64 unHi) cA0 cA1 (Z_to_bv 64 (hi - gtHi)) (Z_to_bv 64 (gtHi - unHi)) (Z_to_bv 64 hi) (Z_to_bv 64 lo) (Z_to_bv 64 (gtHi - unHi)) (Z_to_bv 64 gtHi) (Z_to_bv 64 mm) (Z_to_bv 64 unLo) y30 y31)
                         F (Z_to_bv 64 0xa65fc) fc None m2 (seg_rom b0segs))).
      2:{ wstep; if_cases Km; zify_cond_z Km.
          - enter_with T2b; st_eq.
          - wstep. enter_with T2b; st_eq. }
      (* [comment removed for export] *)
      sub_chk. wstep. try rewrite (sx32_of_Z (hi - mm)) by lia. wstep. try rewrite (sx32_of_Z (hi - mm + 1)) by lia. (wstep; notrap).
      (* [comment removed for export] *)
      wstep; if_cases Kz; zify_cond_z Kz.
      - (* [comment removed for export] *)
        assert (Efm2 : fm2 = fm1) by (subst fm2; apply fvswap_le0; lia).
        enter_with (T3 m2 _ _ _ _ _ _ _ _ _ _); rewrite ?Efm2; [st_eq| exact AR1'| exact MI2| exact MU2| exact WM2| exact FMR1| exact FMOK1| exact SC2| exact SHI2| exact SLO2].
      - try (apply Bool.andb_false_iff in Kz; destruct Kz as [Kz|Kz]; [apply Z.ltb_ge in Kz| apply Z.ltb_ge in Kz; exfalso; lia]).
        (* [comment removed for export] *)
        wstep. wstep. wstep. wstep. wstep.
        enter_with (B0_vsw2 (Z.to_nat mm) unLo (hi - mm + 1)%Z rr' fm1 m2 m2);
          [st_eq| lia| lia| lia| lia| lia| exact FMR1| exact FMOK1| exact AR1'| exact SC2| exact MI2| apply munch_refl| apply wmono_refl| |].
        { eapply shzW_sub; [exact SH1| exact MU2| sub_fp_solve| lia| lia]. }
        intros m3 z1 z5 z6 z7 z12 z13 z17 z28 z30 z31. cbv zeta. intros AR1'' SC3 MI3 MU3 WM3 FMR2 FMOK2. bz_params. clear AR1' MI2 SC2.
        transport_after_call b0segs m2 m3 MU3 WM3.
        assert (Efm2 : fm2 = fvswap (Z.to_nat mm) fm1 unLo (hi - mm + 1) (Z.of_nat (Z.to_nat mm))).
        { subst fm2. replace (fvswap (S (Z.to_nat mm)) fm1 unLo (hi - mm + 1) mm) with (fvswap (S (Z.to_nat mm)) fm1 unLo (hi - mm + 1) (Z.of_nat (Z.to_nat mm))) by (f_equal; lia). apply fvswap_fuel. }
        rewrite <- Efm2 in AR1'', FMR2, FMOK2.
        enter_with (T3 m3 _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1''| exact MI3| exact MU2| exact WM2| exact FMR2| exact FMOK2| exact SC3| exact SHI2| exact SLO2]. }
    (* [comment removed for export] *)
    sub_chk. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mq end.
    (* [comment removed for export] *)
    wstep; if_cases Kz; zify_cond_z Kz.
    - (* [comment removed for export] *)
      assert (Efm1 : fm1 = fm) by (subst fm1; apply fvswap_le0; lia).
      enter_with (T2 mq _ _ _ _ _ _ _ _ _ _); rewrite ?Efm1; [st_eq| exact AR1| exact MI| exact MU| exact WMo| exact FMR| exact FMOK'| exact SCH| exact SHIc| exact SLOc].
    - try (apply Bool.andb_false_iff in Kz; destruct Kz as [Kz|Kz]; [apply Z.ltb_ge in Kz| apply Z.ltb_ge in Kz; exfalso; lia]).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep.
      enter_with (B0_vsw1 (Z.to_nat n) lo (unLo - n)%Z rr' fm mq mq);
        [st_eq| lia| lia| lia| lia| lia| exact FMR| exact FMOK'| exact AR1| exact SCH| exact MI| apply munch_refl| apply wmono_refl| |].
      { eapply shzW_sub; [exact SH1| exact MU| sub_fp_solve| lia| lia]. }
      intros m2 z1 z5 z6 z12 z13 z16 z17 z28 z30 z31. cbv zeta. intros AR1' SC2 MI2 MU2 WM2 FMR1 FMOK1. bz_params. clear AR1 MI SCH.
      transport_after_call b0segs mq m2 MU2 WM2.
      assert (Efm1 : fm1 = fvswap (Z.to_nat n) fm lo (unLo - n) (Z.of_nat (Z.to_nat n))).
      { subst fm1. replace (fvswap (S (Z.to_nat n)) fm lo (unLo - n) n) with (fvswap (S (Z.to_nat n)) fm lo (unLo - n) (Z.of_nat (Z.to_nat n))) by (f_equal; lia). apply fvswap_fuel. }
      rewrite <- Efm1 in AR1', FMR1, FMOK1.
      enter_with (T2 m2 _ _ _ _ _ _ _ _ _ _); [st_eq| exact AR1'| exact MI2| exact MU| exact WMo| exact FMR1| exact FMOK1| exact SC2| exact SHIc| exact SLOc].
  Qed.
End B0FS.
End ACeilS1.
