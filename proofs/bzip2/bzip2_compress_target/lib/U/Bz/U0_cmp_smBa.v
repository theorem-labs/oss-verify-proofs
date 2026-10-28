(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpSmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCFactsSmB BzCFactsSmB2.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section U0SMBA.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (ra gp tp t2 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzu :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?x 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia
    | |- context [bv_wrap 32 ?x] => change (bv_wrap 32 x) with (Z.modulo x 4294967296)
    | |- context [Z.modulo ?x 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
    | |- context [bv_swrap 32 ?x] => rewrite (swrap32_id x) by lia
    | |- context [bv_signed (Z_to_bv 64 ?x)] => rewrite (signed_lit_small x) by lia
    | |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (unsigned_lit x) by lia
    | |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (sx32_of_Z x) by lia
    | |- context [Z.lxor ?x 9223372036854775808] => rewrite (lxor_sign_small x) by (change (2^63)%Z with 9223372036854775808%Z; lia)
    | |- context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) by (change (2^64)%Z with 18446744073709551616%Z; lia)
    end; zb_fold_lits.
  Ltac lstep := zstep; bzu.
  Ltac FT := lstep;
    repeat match goal with
    | |- context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_eq x y)) by mlia
    | |- context [Z.ltb ?x ?y] => rewrite (proj2 (Z.ltb_lt x y)) by mlia
    | |- context [Z.leb ?x ?y] => rewrite (proj2 (Z.leb_le x y)) by mlia
    end; cbn [Z.b2z andb orb negb]; zb_fold_lits.
  Ltac FF := lstep;
    repeat match goal with
    | |- context [Z.eqb ?x ?y] => rewrite (proj2 (Z.eqb_neq x y)) by mlia
    | |- context [Z.ltb ?x ?y] => rewrite (proj2 (Z.ltb_ge x y)) by mlia
    | |- context [Z.leb ?x ?y] => rewrite (proj2 (Z.leb_gt x y)) by mlia
    end; cbn [Z.b2z andb orb negb]; zb_fold_lits.
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.

  Notation RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  Notation GU t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 := (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BEST (cost : zarr) (k : nat) : Z * Z := sm_best k cost 0 999999999 (-1).
  Lemma BEST_range : forall cost k, (1 <= k)%nat -> (forall t, 0 <= t < Z.of_nat k -> 0 <= zget cost t <= 65535)%Z ->
    (0 <= fst (BEST cost k) <= 65535)%Z /\ (0 <= snd (BEST cost k) < Z.of_nat k)%Z.
  Proof.
    intros cost k Hk HC. unfold BEST. pose proof (HC 0%Z ltac:(lia)) as H0. split.
    - apply (sm_best_fst_bound k cost 0 999999999 (-1) 65535 Hk ltac:(lia)). intros t' Ht'. apply HC. lia.
    - pose proof (sm_best_hit k cost 0 999999999 (-1) Hk ltac:(lia)). lia.
  Qed.
  Lemma BEST_snoc : forall cost k, BEST cost (S k) = (if (zget cost (Z.of_nat k) <? fst (BEST cost k))%Z then (zget cost (Z.of_nat k), Z.of_nat k) else BEST cost k).
  Proof. intros cost k. unfold BEST. rewrite sm_best_snoc. cbv zeta. rewrite Z.add_0_l. reflexivity. Qed.
  Lemma BEST_1 : forall cost, (0 <= zget cost 0 <= 65535)%Z -> BEST cost 1 = (zget cost 0, 0%Z).
  Proof. intros cost H. unfold BEST. cbn [sm_best]. replace (zget cost 0 <? 999999999)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac RDC COST CBOK CREL t :=
    let RD := fresh "RD" in let Ct := fresh "Ct" in
    pose proof (CREL t ltac:(lia)) as Ct;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (zb8_read2 s0segs mm (SP + 1084) _ 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD end;
    rewrite Ct in RD; lstep; clear RD; rewrite (zx16_lit (zget _ t)) by lia.

  (* [comment removed for export] *)
  Lemma U0_bt01 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word),
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 2))) (Z_to_bv 64 (fst (BEST cost 2))) a2 (Z_to_bv 64 (zget cost 1)) a4 a5 a6 a7)
                     F (Z_to_bv 64 0x19888) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (GU t0 t1 a0 a1 a2 a3 a4 a5 a6 a7)
                     F (Z_to_bv 64 0x19870) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 COST [CBOK CREL] HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof (zb8_length_nat cb 12) as LC.
    pose proof (HC 0%Z ltac:(lia)) as C0. pose proof (HC 1%Z ltac:(lia)) as C1.
    rewrite (BEST_snoc cost 1), (BEST_1 cost C0) in K. change (Z.of_nat 1) with 1%Z in K. cbn [fst snd] in K.
    (* [comment removed for export] *)
    RDC COST CBOK CREL 0%Z. RDC COST CBOK CREL 1%Z. lstep.
    (* [comment removed for export] *)
    lstep; if_cases K1; zify_cond_z K1.
    - replace (zget cost 1 <? zget cost 0)%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      FF. enter_with K; [st_eq].
    - lstep. destruct (Z.ltb_spec (zget cost 1) (zget cost 0)) as [LT|GEQ]; cbn [fst snd] in K.
      + FT. enter_with K; [st_eq].
      + FF. enter_with K; [st_eq].
  Qed.

  (* [comment removed for export] *)
  Lemma U0_bt2 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 a2 a3 a4 a5 a6 a7 : word),
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG -> (3 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 3))) (Z_to_bv 64 (fst (BEST cost 2))) a2 (Z_to_bv 64 (fst (BEST cost 3))) a4 (Z_to_bv 64 (zget cost 2)) a6 a7)
                     F (Z_to_bv 64 0x198ac) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 2))) (Z_to_bv 64 (fst (BEST cost 2))) a2 a3 a4 a5 a6 a7)
                     F (Z_to_bv 64 0x19894) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m t0 t1 a2 a3 a4 a5 a6 a7 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof (zb8_length_nat cb 12) as LC.
    pose proof (HC 2%Z ltac:(lia)) as Ct0.
    pose proof (BEST_range cost 2 ltac:(lia) ltac:(intros; apply HC; lia)) as [BR1 BR2].
    rewrite (BEST_snoc cost 2) in K. change (Z.of_nat 2) with 2%Z in K.
    (* [comment removed for export] *)
    RDC COST CBOK CREL 2%Z. lstep.
    lstep; if_cases K1; zify_cond_z K1.
    - replace (zget cost 2 <? fst (BEST cost 2))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      lstep; if_cases K2; zify_cond_z K2; [| exfalso; lia]. enter_with K; [st_eq].
    - lstep. lstep; if_cases K2; zify_cond_z K2.
      + replace (zget cost 2 <? fst (BEST cost 2))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with K; [st_eq].
      + replace (zget cost 2 <? fst (BEST cost 2))%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K.
        lstep. enter_with K; [st_eq].
  Qed.

  Lemma U0_bt3 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 a1 a2 a4 a5 a6 a7 : word),
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG -> (4 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 4))) (Z_to_bv 64 (fst (BEST cost 4))) a2 (Z_to_bv 64 (fst (BEST cost 3))) a4 (Z_to_bv 64 (zget cost 3)) a6 a7)
                     F (Z_to_bv 64 0x198d4) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 3))) a1 a2 (Z_to_bv 64 (fst (BEST cost 3))) a4 a5 a6 a7)
                     F (Z_to_bv 64 0x198bc) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m t0 t1 a1 a2 a4 a5 a6 a7 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof (zb8_length_nat cb 12) as LC.
    pose proof (HC 3%Z ltac:(lia)) as Ct0.
    pose proof (BEST_range cost 3 ltac:(lia) ltac:(intros; apply HC; lia)) as [BR1 BR2].
    rewrite (BEST_snoc cost 3) in K. change (Z.of_nat 3) with 3%Z in K.
    RDC COST CBOK CREL 3%Z. lstep.
    lstep; if_cases K1; zify_cond_z K1.
    - replace (zget cost 3 <? fst (BEST cost 3))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      lstep; if_cases K2; zify_cond_z K2; [| exfalso; lia]. enter_with K; [st_eq].
    - lstep. lstep; if_cases K2; zify_cond_z K2.
      + replace (zget cost 3 <? fst (BEST cost 3))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with K; [st_eq].
      + replace (zget cost 3 <? fst (BEST cost 3))%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K.
        lstep. enter_with K; [st_eq].
  Qed.

  Lemma U0_bt4 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 a2 a3 a4 a5 a6 a7 : word),
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG -> (5 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 5))) (Z_to_bv 64 (fst (BEST cost 4))) a2 (Z_to_bv 64 (fst (BEST cost 5))) a4 (Z_to_bv 64 (zget cost 4)) a6 a7)
                     F (Z_to_bv 64 0x198f4) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 4))) (Z_to_bv 64 (fst (BEST cost 4))) a2 a3 a4 a5 a6 a7)
                     F (Z_to_bv 64 0x198dc) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m t0 t1 a2 a3 a4 a5 a6 a7 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof (zb8_length_nat cb 12) as LC.
    pose proof (HC 4%Z ltac:(lia)) as Ct0.
    pose proof (BEST_range cost 4 ltac:(lia) ltac:(intros; apply HC; lia)) as [BR1 BR2].
    rewrite (BEST_snoc cost 4) in K. change (Z.of_nat 4) with 4%Z in K.
    RDC COST CBOK CREL 4%Z. lstep.
    lstep; if_cases K1; zify_cond_z K1.
    - replace (zget cost 4 <? fst (BEST cost 4))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      lstep; if_cases K2; zify_cond_z K2; [| exfalso; lia]. enter_with K; [st_eq].
    - lstep. lstep; if_cases K2; zify_cond_z K2.
      + replace (zget cost 4 <? fst (BEST cost 4))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with K; [st_eq].
      + replace (zget cost 4 <? fst (BEST cost 4))%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K.
        lstep. enter_with K; [st_eq].
  Qed.

  Lemma U0_bt5 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 a1 a2 a4 a5 a6 a7 : word),
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG -> (6 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 6))) (Z_to_bv 64 (fst (BEST cost 6))) a2 (Z_to_bv 64 (fst (BEST cost 5))) a4 (Z_to_bv 64 (zget cost 5)) a6 a7)
                     F (Z_to_bv 64 0x19914) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost 5))) a1 a2 (Z_to_bv 64 (fst (BEST cost 5))) a4 a5 a6 a7)
                     F (Z_to_bv 64 0x198fc) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m t0 t1 a1 a2 a4 a5 a6 a7 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof (zb8_length_nat cb 12) as LC.
    pose proof (HC 5%Z ltac:(lia)) as Ct0.
    pose proof (BEST_range cost 5 ltac:(lia) ltac:(intros; apply HC; lia)) as [BR1 BR2].
    rewrite (BEST_snoc cost 5) in K. change (Z.of_nat 5) with 5%Z in K.
    RDC COST CBOK CREL 5%Z. lstep.
    lstep; if_cases K1; zify_cond_z K1.
    - replace (zget cost 5 <? fst (BEST cost 5))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
      lstep; if_cases K2; zify_cond_z K2; [| exfalso; lia]. enter_with K; [st_eq].
    - lstep. lstep; if_cases K2; zify_cond_z K2.
      + replace (zget cost 5 <? fst (BEST cost 5))%Z with false in K by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd] in K.
        enter_with K; [st_eq].
      + replace (zget cost 5 <? fst (BEST cost 5))%Z with true in K by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd] in K.
        lstep. enter_with K; [st_eq].
  Qed.

  (* [comment removed for export] *)
  Lemma U0_sm_bt : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word),
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    frdW s0segs [] m (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    (forall (a3 a5 : word),
      evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (snd (BEST cost (Z.to_nat nG)))) (Z_to_bv 64 (fst (BEST cost (Z.to_nat nG)))) a2 a3 a4 a5 (Z_to_bv 64 nG) a7)
                       F (Z_to_bv 64 0x19920) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (GU t0 t1 a0 a1 a2 a3 a4 a5 a6 a7)
                     F (Z_to_bv 64 0x19870) fc None m (seg_rom s0segs)).
  Proof.
    intros cb cost m t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 COST CR HC V928 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    apply (U0_bt01 cb cost m); [exact COST| exact CR| exact HC|].
    (* [comment removed for export] *)
    pose proof (V928 m (munch_refl [] m)) as RO. lstep. clear RO. lstep. lstep; if_cases K2; zify_cond_z K2.
    { replace (Z.to_nat nG) with 2%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (U0_bt2 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K3; zify_cond_z K3.
    2:{ lstep. lstep. replace (Z.to_nat nG) with 3%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (U0_bt3 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K4; zify_cond_z K4.
    { replace (Z.to_nat nG) with 4%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (U0_bt4 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K5; zify_cond_z K5.
    { lstep. lstep. replace (Z.to_nat nG) with 5%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (U0_bt5 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K6; zify_cond_z K6; [| exfalso; lia].
    replace (Z.to_nat nG) with 6%nat in K by lia. enter_with (K _ _); [st_eq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstepA := zstep; bzl.
  Notation Wc := [(SP + 1084, SP + 1096)]%Z.
  Notation NLEN t := (Z_to_bv 64 (18446744073709551615 - (E + 37708) - 258 * t)).
  Lemma U0_sm_csti : forall (n : nat) (t icv : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (t0 t1 a0 a2 a4 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat -> (0 <= icv < A)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv s0segs m -> munch Wc mf m -> wmono s0segs mf m ->
    (forall m' cb' (t0 t1 : word),
      u8arr s0segs m' (SP + 1084) (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow_t n cost len icv t) nG ->
      mem_inv s0segs m' -> munch Wc mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GU t0 t1 a0 (Z_to_bv 64 (258 * nG)) a2 (Z_to_bv 64 icv) a4 (Z_to_bv 64 (E + 37708 + icv)) (Z_to_bv 64 (SP + 1084 + 2 * nG)) (NLEN nG))
                       F (Z_to_bv 64 0x19864) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GU t0 t1 a0 (Z_to_bv 64 (258 * t)) a2 (Z_to_bv 64 icv) a4 (Z_to_bv 64 (E + 37708 + icv)) (Z_to_bv 64 (SP + 1084 + 2 * t)) (NLEN t))
                     F (Z_to_bv 64 0x19820) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t icv cb cost len m mf t0 t1 a0 a2 a4 Ht Ht0 Hn Hicv LF VLEN COST [CBOK CREL] MI MU WM K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    pose proof (zb8_length_nat cb 12) as LC. pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    pose proof (CREL t ltac:(lia)) as Ct. pose proof (zbok_rd16 cb (2 * t) CBOK) as Rt. rewrite Ct in Rt.
    destruct (LF t icv ltac:(lia) ltac:(lia)) as [Dl Rl].
    rewrite sm_cost_slow_t_S in K.
    (* [comment removed for export] *)
    urun_to 0x19844%Z.
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m (SP + 1084) cb 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD.
    rewrite Ct in RD. lstepA. clear RD.
    (* [comment removed for export] *)
    pose proof (VLEN m MU) as LEN.
    pose proof (ovb_read1 s0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + icv) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    lstepA. clear RD LEN.
    (* [comment removed for export] *)
    lstepA. lstepA. lstepA. rewrite (unsigned_lit8 (zget len (258 * t + icv))) by lia.
    pose proof (u8arr_storeN_ok s0segs _ (SP + 1084) _ (2 * t) 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstepA. store_addr (SP + 1084 + 2 * t)%Z. zb8_store2 COST (2 * t)%Z.
    pose proof (COSTREL_set cb cost nG t (bv_unsigned (Z_to_bv 64 (bv_unsigned (sx16 (Z_to_bv 64 (zget cost t))) + zget len (258 * t + icv)))) (conj CBOK CREL) ltac:(lia)) as CR'.
    rewrite (cost_upd_mod (zget cost t) (zget len (258 * t + icv))) in CR' by lia.
    (* [comment removed for export] *)
    lstepA. lstepA; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z icv _ _ len _ mf); [st_eq| lia| lia| lia| lia| exact LF| exact VLEN| exact COST| exact CR'| assumption| assumption| assumption| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow_t] in K.
      enter_with (K _ _ _ _); [st_eq| exact COST| exact CR'| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_sm_csto : forall (n : nat) (i ge : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (t0 t1 a1 a2 a3 a4 a5 a6 a7 : word),
    (i + Z.of_nat n = ge + 1)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wc mf m' -> u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv s0segs m -> munch Wc mf m -> wmono s0segs mf m ->
    frdW s0segs Wc mf (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wc mf (SP + 1008) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wc mf (SP + 1016) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wc mf (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] ->
    frdW s0segs Wc mf (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' cb' (t0 t1 a3 a5 a6 a7 : word),
      u8arr s0segs m' (SP + 1084) (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow n cost len arr1 nG i) nG ->
      mem_inv s0segs m' -> munch Wc mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 (ge + 1)) a2 a3 a4 a5 a6 a7)
                       F (Z_to_bv 64 0x19870) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7)
                     F (Z_to_bv 64 0x197c4) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i ge cb cost len m mf t0 t1 a1 a2 a3 a4 a5 a6 a7 Hi Hi0 Hn Hge LF VAR1 VLEN COST CR MI MU WM V992 V1008 V1016 V1024 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    pose proof (MV i ltac:(lia)) as MVi.
    rewrite sm_cost_slow_S in K.
    (* [comment removed for export] *)
    poseV V1032 R1032. poseV V1016 R1016. poseV V1008 R1008. poseV V992 R992.
    urun_to 0x1980c%Z.
    pose proof (VAR1 m MU) as AR1.
    pose proof (zb8_read2 s0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstepA. clear RD AR1. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    urun_to 0x19820%Z. clear R1032 R1016 R1008 R992.
    enter_with (U0_sm_csti (Z.to_nat nG) 0 (mtfv_at arr1 i) cb cost len m mf);
      [st_eq| lia| lia| lia| lia| exact LF| exact VLEN| exact COST| exact CR| exact MI| exact MU| exact WM|].
    clear COST CR MI. intros m1 cb1 yt0 yt1 COST CR MI MU1 WM1. clear MU WM.
    (* [comment removed for export] *)
    poseV V1024 R1024. lstepA. lstepA. clear R1024. lstepA; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ge cb1 _ len m1 mf);
        [st_eq| lia| lia| lia| lia| exact LF| exact VAR1| exact VLEN| exact COST| exact CR| exact MI| exact MU1| exact WM1| exact V992| exact V1008| exact V1016| exact V1024| exact V1032| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow] in K.
      enter_with (K m1 cb1 _ _ _ _ _ _); [st_eq| exact COST| exact CR| exact MI| exact MU1| exact WM1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_sm_csg : forall (gs ge : Z) (cb cost len : zarr) (m mf : word -> option byte)
      (t0 t1 a1 a2 a3 a5 a6 a7 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wc mf m' -> u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr s0segs m (SP + 1084) (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv s0segs m -> munch Wc mf m -> wmono s0segs mf m ->
    frdW s0segs Wc mf (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wc mf (SP + 1008) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wc mf (SP + 1016) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wc mf (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] ->
    frdW s0segs Wc mf (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' cb' (t0 t1 a0 a1 a3 a5 a6 a7 : word),
      u8arr s0segs m' (SP + 1084) (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow (Z.to_nat (ge + 1 - gs)) cost len arr1 nG gs) nG ->
      mem_inv s0segs m' -> munch Wc mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GU t0 t1 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7)
                       F (Z_to_bv 64 0x19870) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (ge + 1)) a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7)
                     F (Z_to_bv 64 0x197bc) fc None m (seg_rom s0segs)).
  Proof.
    intros gs ge cb cost len m mf t0 t1 a1 a2 a3 a5 a6 a7 Hgs Hge LF VAR1 VLEN COST CR MI MU WM V992 V1008 V1016 V1024 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    (* [comment removed for export] *)
    lstepA; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    lstepA.
    enter_with (U0_sm_csto (Z.to_nat (ge + 1 - gs)) gs ge cb cost len m mf);
      [st_eq| lia| lia| lia| lia| exact LF| exact VAR1| exact VLEN| exact COST| exact CR| exact MI| exact MU| exact WM| exact V992| exact V1008| exact V1016| exact V1024| exact V1032|].
    intros m' cb' y0 y1 y3 y5 y6 y7 COST' CR' MI' MU' WM'.
    enter_with (K m' cb' _ _ _ _ _ _ _ _); [st_eq| exact COST'| exact CR'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  Notation ROWF t := (E + 45448 + 1032 * t)%Z.
  Lemma U0_sm_rfsl : forall (n : nat) (i ge bt B : Z) (rf : zarr) (m mf : word -> option byte)
      (t0 t1 a2 a6 a7 : word),
    (0 <= i)%Z -> (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (ge < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + Z.of_nat n <= 2000000000)%Z ->
    (forall m', munch Wrf mf m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv s0segs m -> munch Wrf mf m -> wmono s0segs mf m ->
    frdW s0segs Wrf mf (SP + 1008) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wrf mf (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wrf mf (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] -> frdW s0segs Wrf mf (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' rf' (t0 a2 a6 a7 : word),
      u32arr s0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc n rf arr1 bt i -> RFrow rf' bt A (B + Z.of_nat n) ->
      mem_inv s0segs m' -> munch Wrf mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (ROWF bt)) (Z_to_bv 64 (A1 + 2 * (ge + 1))) a2 (NOT (ROWF bt)) (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 (A1 + 2 * (ge + 1))) a6 a7)
                       F (Z_to_bv 64 0x1b310) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 (ROWF bt)) (Z_to_bv 64 (A1 + 2 * i)) a2 (NOT (ROWF bt)) (Z_to_bv 64 i) (Z_to_bv 64 (A1 + 2 * i)) a6 a7)
                     F (Z_to_bv 64 0x1b290) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i ge bt B rf m mf t0 t1 a2 a6 a7 Hi0 Hn Hend Hge Hbt HB HBn VAR1 RFQ RFF MI MU WM V1008 V1016 V1024 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rf (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    pose proof (MV i ltac:(lia)) as MVi. destruct (RFF (mtfv_at arr1 i) MVi) as [Dr Rr].
    (* [comment removed for export] *)
    poseV V1008 R1008. poseV V1016 R1016. poseV V1032 R1032.
    urun_to 0x1b2c8%Z.
    pose proof (VAR1 m MU) as AR1.
    pose proof (zb8_read2 s0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstepA. clear RD AR1. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    urun_to 0x1b2e8%Z.
    pose proof (ovw_read s0segs m (E + 45448) rf (jseg J 45448 6192) 1548 (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(lia) Dr ltac:(unfold wa; f_equal; lia)) as RD.
    lstepA. clear RD. rewrite (sx32_of_Z (zget rf (258 * bt + mtfv_at arr1 i))) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    urun_to 0x1b2f8%Z. clear R1008 R1016 R1032.
    pose proof (u32arr_store_ok s0segs m (E + 45448) _ (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstepA. store_addr (E + 45448 + 4 * (258 * bt + mtfv_at arr1 i))%Z.
    ovw_store RFQ (258 * bt + mtfv_at arr1 i)%Z (zget rf (258 * bt + mtfv_at arr1 i) + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset rf (258 * bt + mtfv_at arr1 i) (zget rf (258 * bt + mtfv_at arr1 i) + 1)) with (zincr rf (258 * bt + mtfv_at arr1 i)) in RFQ.
    pose proof (RFrow_incr rf bt A B (mtfv_at arr1 i) RFF MVi) as RFF'.
    rewrite sm_rfreq_inc_S in K.
    (* [comment removed for export] *)
    poseV V1024 R1024. lstepA. lstepA. lstepA. lstepA. clear R1024. lstepA; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ge bt (B + 1)%Z _ _ mf);
        [st_eq| lia| lia| lia| lia| lia| lia| lia| exact VAR1| exact RFQ| exact RFF'| assumption| assumption| assumption| exact V1008| exact V1016| exact V1024| exact V1032|].
      intros m' rf' y0 ya2 y6 y7 RFQ' E' RFF2 MI' MU' WM'.
      enter_with (K m' rf' y0 ya2 y6 y7); [st_eq| exact RFQ'| exact E'| eapply RFrow_weaken; [exact RFF2| lia]| exact MI'| exact MU'| exact WM'].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_inc] in K.
      enter_with (K _ _ _ _ _ _); [st_eq| exact RFQ| reflexivity| eapply RFrow_weaken; [exact RFF'| lia]| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_sm_rfsg : forall (gs ge bt B : Z) (rf : zarr) (m mf : word -> option byte)
      (t0 t1 a2 a3 a5 a6 a7 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + (ge + 1 - gs) <= 2000000000)%Z ->
    (forall m', munch Wrf mf m' -> u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv s0segs m -> munch Wrf mf m -> wmono s0segs mf m ->
    frdW s0segs Wrf mf (SP + 944) [C8 (NOT (E + 45448))] -> frdW s0segs Wrf mf (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    frdW s0segs Wrf mf (SP + 1008) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wrf mf (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wrf mf (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] -> frdW s0segs Wrf mf (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' rf' (t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 : word),
      u32arr s0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc (Z.to_nat (ge + 1 - gs)) rf arr1 bt gs -> RFrow rf' bt A (B + (ge + 1 - gs)) ->
      mem_inv s0segs m' -> munch Wrf mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GU t0 t1 a0 a1 a2 a3 a4 a5 a6 a7)
                       F (Z_to_bv 64 0x1b310) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GU t0 t1 (Z_to_bv 64 bt) (Z_to_bv 64 (ge + 1)) a2 a3 (Z_to_bv 64 gs) a5 a6 a7)
                     F (Z_to_bv 64 0x1b250) fc None m (seg_rom s0segs)).
  Proof.
    intros gs ge bt B rf m mf t0 t1 a2 a3 a5 a6 a7 Hgs Hge Hbt HB HBn VAR1 RFQ RFF MI MU WM V944 V952 V1008 V1016 V1024 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    (* [comment removed for export] *)
    lstepA; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    (* [comment removed for export] *)
    poseV V944 R944. poseV V952 R952. poseV V1032 R1032. urun_to 0x1b290%Z. clear R944 R952 R1032.
    enter_with (U0_sm_rfsl (Z.to_nat (ge + 1 - gs)) gs ge bt B rf m mf);
      [st_eq| lia| lia| lia| lia| lia| lia| lia| exact VAR1| exact RFQ| exact RFF| exact MI| exact MU| exact WM| exact V1008| exact V1016| exact V1024| exact V1032|].
    intros m' rf' y0 ya2 y6 y7 RFQ' E' RFF' MI' MU' WM'.
    enter_with (K m' rf' _ _ _ _ _ _ _ _ _ _); [st_eq| exact RFQ'| exact E'| replace (B + (ge + 1 - gs))%Z with (B + Z.of_nat (Z.to_nat (ge + 1 - gs)))%Z by lia; exact RFF'| exact MI'| exact MU'| exact WM'].
  Qed.
End U0SMBA.
End ACeilS1.
