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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV B0_cmp_sdV B0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GBB.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis COL : (0 < CO)%Z. Hypothesis COH : (CO + 12 <= CEIL)%Z. Hypothesis FVL : (0 < FV)%Z. Hypothesis FVH : (FV + 24 <= CEIL)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  (* [comment removed for export] *)
  Hypothesis SEFV : id ((c_E cx + 55768 <= FV)%Z \/ (FV + 24 <= c_E cx)%Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis MV : forall i, (0 <= i < nMTF)%Z -> (0 <= mtfv_at arr1 i < A)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
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
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.

  (* [comment removed for export] *)
  Notation GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 :=
    (mkR (Z_to_bv 64 (E + 51640)) cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
         (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
  Notation HIT v32 v48 v56 v88 v20 v28 :=
    (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
  Ltac openHI H := unfold sd_hi in H; cbv zeta in H; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in H.

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
    pose proof (zb8_read2 b0segs mm CO _ 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD end;
    rewrite Ct in RD; lstep; clear RD; rewrite (zx16_lit (zget _ t)) by lia.

  (* [comment removed for export] *)
  Lemma B0_bt01 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 2))) (Z_to_bv 64 (snd (BEST cost 2))) (Z_to_bv 64 (zget cost 1)) a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f938) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f920) fc None m (seg_rom b0segs)).
  Proof.
    intros cb cost m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 COST [CBOK CREL] HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. pose proof (zb8_length_nat cb 12) as LC.
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
  Lemma B0_bt2 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG -> (3 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 2))) (Z_to_bv 64 (snd (BEST cost 3))) (Z_to_bv 64 (fst (BEST cost 3))) (Z_to_bv 64 (zget cost 2)) a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f95c) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 2))) (Z_to_bv 64 (snd (BEST cost 2))) a2 a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f944) fc None m (seg_rom b0segs)).
  Proof.
    intros cb cost m t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 t3 t4 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. pose proof (zb8_length_nat cb 12) as LC.
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

  Lemma B0_bt3 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 t2 a0 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG -> (4 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 4))) (Z_to_bv 64 (snd (BEST cost 4))) (Z_to_bv 64 (fst (BEST cost 3))) (Z_to_bv 64 (zget cost 3)) a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f984) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 (snd (BEST cost 3))) (Z_to_bv 64 (fst (BEST cost 3))) a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f96c) fc None m (seg_rom b0segs)).
  Proof.
    intros cb cost m t0 t1 t2 a0 a3 a4 a5 a6 a7 s10 t3 t4 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. pose proof (zb8_length_nat cb 12) as LC.
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

  Lemma B0_bt4 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG -> (5 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 4))) (Z_to_bv 64 (snd (BEST cost 5))) (Z_to_bv 64 (fst (BEST cost 5))) (Z_to_bv 64 (zget cost 4)) a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f9a4) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 4))) (Z_to_bv 64 (snd (BEST cost 4))) a2 a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f98c) fc None m (seg_rom b0segs)).
  Proof.
    intros cb cost m t0 t1 t2 a2 a3 a4 a5 a6 a7 s10 t3 t4 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. pose proof (zb8_length_nat cb 12) as LC.
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

  Lemma B0_bt5 : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 t2 a0 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG -> (6 <= nG)%Z ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost 6))) (Z_to_bv 64 (snd (BEST cost 6))) (Z_to_bv 64 (fst (BEST cost 5))) (Z_to_bv 64 (zget cost 5)) a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f9c4) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 (snd (BEST cost 5))) (Z_to_bv 64 (fst (BEST cost 5))) a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f9ac) fc None m (seg_rom b0segs)).
  Proof.
    intros cb cost m t0 t1 t2 a0 a3 a4 a5 a6 a7 s10 t3 t4 COST [CBOK CREL] HT HC K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. pose proof (zb8_length_nat cb 12) as LC.
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
  Lemma B0_sm_bt : forall (cb cost : zarr) (m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    (forall t, 0 <= t < nG -> 0 <= zget cost t <= 65535)%Z ->
    frdW b0segs [] m (P + 1480) [C8 (Z_to_bv 64 nG)] ->
    (forall (a2 a3 : word),
      evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (fst (BEST cost (Z.to_nat nG)))) (Z_to_bv 64 (snd (BEST cost (Z.to_nat nG)))) a2 a3 a4 (Z_to_bv 64 nG) a6 a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8f9d0) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f920) fc None m (seg_rom b0segs)).
  Proof.
    intros cb cost m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 COST CR HC V1480 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    apply (B0_bt01 cb cost m); [exact COST| exact CR| exact HC|].
    (* [comment removed for export] *)
    pose proof (V1480 m (munch_refl [] m)) as RO. lstep. clear RO. lstep. lstep; if_cases K2; zify_cond_z K2.
    { replace (Z.to_nat nG) with 2%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (B0_bt2 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K3; zify_cond_z K3.
    2:{ lstep. lstep. replace (Z.to_nat nG) with 3%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (B0_bt3 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K4; zify_cond_z K4.
    { replace (Z.to_nat nG) with 4%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (B0_bt4 cb cost m); [exact COST| exact CR| lia| exact HC|].
    (* [comment removed for export] *)
    lstep. lstep; if_cases K5; zify_cond_z K5.
    { lstep. lstep. replace (Z.to_nat nG) with 5%nat in K by lia. enter_with (K _ _); [st_eq]. }
    apply (B0_bt5 cb cost m); [exact COST| exact CR| lia| exact HC|].
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
  Notation Wc := [(CO, CO + 12)]%Z.
  Notation NLEN t := (Z_to_bv 64 (18446744073709551615 - (E + 37708) - 258 * t)).
  Lemma B0_sm_csti : forall (n : nat) (t icv : Z) (cb cost len : zarr) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (t2 a1 a4 a6 s10 t3 t4 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat -> (0 <= icv < A)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv b0segs m -> munch Wc mf m -> wmono b0segs mf m ->
    shzW b0segs Wc mf E (E + ESTATE_SIZE) -> shpW b0segs Wc mf CO (CO + 12) ->
    frdW b0segs Wc mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' cb' (t2 t3 t4 : word),
      u8arr b0segs m' CO (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow_t n cost len icv t) nG ->
      mem_inv b0segs m' -> munch Wc mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB (Z_to_bv 64 (CO + 2 * nG)) (NLEN nG) t2 (Z_to_bv 64 (CO + 2 * nG)) a1 (Z_to_bv 64 (258 * nG)) (Z_to_bv 64 icv) a4 (Z_to_bv 64 (E + 37708 + icv)) a6 (Z_to_bv 64 (E + 37708 + icv)) s10 t3 t4)
                       F (Z_to_bv 64 0x8f904) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB (Z_to_bv 64 (CO + 2 * t)) (NLEN t) t2 (Z_to_bv 64 (CO + 2 * t)) a1 (Z_to_bv 64 (258 * t)) (Z_to_bv 64 icv) a4 (Z_to_bv 64 (E + 37708 + icv)) a6 (Z_to_bv 64 (E + 37708 + icv)) s10 t3 t4)
                     F (Z_to_bv 64 0x8f874) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t icv cb cost len v32 v48 v56 v88 v20 v28 m mf t2 a1 a4 a6 s10 t3 t4 Ht Ht0 Hn Hicv LF VLEN COST [CBOK CREL] MI MU WM SHe SHc VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. unfold ESTATE_SIZE in SHe.
    pose proof (zb8_length_nat cb 12) as LC. pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    pose proof (CREL t ltac:(lia)) as Ct. pose proof (zbok_rd16 cb (2 * t) CBOK) as Rt. rewrite Ct in Rt.
    destruct (LF t icv ltac:(lia) ltac:(lia)) as [Dl Rl].
    rewrite sm_cost_slow_t_S in K.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. brun_to 0x8f8b8%Z. clear RO. ack_rd (CO + 2 * t)%Z 2%Z.
    (* [comment removed for export] *)
    pose proof (VLEN m MU) as LEN.
    pose proof (ovb_read1 b0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t + icv) _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD.
    lstepA. clear RD LEN.
    ack_merge.
    (* [comment removed for export] *)
    pose proof (zb8_read2 b0segs m CO cb 12 (2 * t) _ COST ltac:(lia) ltac:(lia) CBOK ltac:(unfold wa; f_equal; lia)) as RD.
    rewrite Ct in RD. lstepA. clear RD.
    (* [comment removed for export] *)
    lstepA. lstepA. lstepA. lstepA. rewrite (unsigned_lit8 (zget len (258 * t + icv))) by lia.
    pose proof (u8arr_storeN_ok b0segs _ CO _ (2 * t) 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstepA. store_addr (CO + 2 * t)%Z. zb8_store2 COST (2 * t)%Z.
    pose proof (COSTREL_set cb cost nG t (bv_unsigned (Z_to_bv 64 (bv_unsigned (sx16 (Z_to_bv 64 (zget cost t))) + zget len (258 * t + icv)))) (conj CBOK CREL) ltac:(lia)) as CR'.
    rewrite (cost_upd_mod (zget cost t) (zget len (258 * t + icv))) in CR' by lia.
    (* [comment removed for export] *)
    lstepA. lstepA; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z icv _ _ len v32 v48 v56 v88 v20 v28 _ mf); [st_eq| lia| lia| lia| lia| exact LF| exact VLEN| exact COST| exact CR'| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact SHc| exact VHI| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow_t] in K. lstepA.
      enter_with (K _ _ _ _ _); [st_eq| exact COST| exact CR'| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation HITg v32 v48 v56 v88 v20 := (HIT v32 v48 v56 v88 v20 (Z_to_bv 64 (E + 37708))).
  Lemma B0_sm_csto : forall (n : nat) (i ge : Z) (cb cost len : zarr) (v32 v48 v56 v88 v20 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a2 a3 a5 a6 a7 s10 t3 t4 : word),
    (i + Z.of_nat n = ge + 1)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wc mf m' -> u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv b0segs m -> munch Wc mf m -> wmono b0segs mf m ->
    shzW b0segs Wc mf A1 (A1 + ARR1_SIZE) -> shzW b0segs Wc mf E (E + ESTATE_SIZE) -> shpW b0segs Wc mf CO (CO + 12) ->
    frdW b0segs Wc mf (P + 1384) (HITg v32 v48 v56 v88 v20) ->
    (forall m' cb' (t0 t1 t2 a0 a2 a3 a5 a7 t3 t4 : word),
      u8arr b0segs m' CO (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow n cost len arr1 nG i) nG ->
      mem_inv b0segs m' -> munch Wc mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 (ge + 1)) a2 a3 (Z_to_bv 64 (ge + 1)) a5 a6 a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8f920) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 i) a2 a3 (Z_to_bv 64 (ge + 1)) a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f800) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i ge cb cost len v32 v48 v56 v88 v20 m mf t0 t1 t2 a0 a2 a3 a5 a6 a7 s10 t3 t4 Hi Hi0 Hn Hge LF VAR1 VLEN COST CR MI MU WM SHa SHe SHc VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'. unfold ESTATE_SIZE in SHe.
    pose proof (MV i ltac:(lia)) as MVi.
    rewrite sm_cost_slow_S in K.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. brun.
    pose proof (VAR1 m MU) as AR1.
    pose proof (zb8_read2 b0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstepA. clear RD AR1. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    brun_to 0x8f874%Z. clear RO.
    enter_with (B0_sm_csti (Z.to_nat nG) 0 (mtfv_at arr1 i) cb cost len v32 v48 v56 v88 v20 (Z_to_bv 64 (E + 37708)) m m);
      [st_eq| lia| lia| lia| lia| exact LF| | exact COST| exact CR| exact MI| apply munch_refl| apply wmono_refl| | | |].
    { apply (vw_sub _ Wc Wc mf m VLEN MU). a_sub_fp. }
    { eapply (shzW_sub b0segs Wc Wc mf m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
    { eapply (shpW_sub b0segs Wc Wc mf m); [exact SHc| exact MU| a_sub_fp| lia| lia]. }
    { eapply (frdW_sub b0segs Wc Wc mf m); [exact VHI| exact MU| a_sub_fp]. }
    clear COST CR MI. intros m1 cb1 yt2 yt3 yt4 COST CR MI MU1 WM1.
    transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    lstepA. lstepA; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z ge cb1 _ len v32 v48 v56 v88 v20 m1 mf); [st_eq| lia| lia| lia| lia| exact LF| exact VAR1| exact VLEN| exact COST| exact CR| exact MI| exact MU| exact WM| exact SHa| unfold ESTATE_SIZE; exact SHe| exact SHc| exact VHI| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_cost_slow] in K. lstepA.
      enter_with (K m1 cb1 _ _ _ _ _ _ _ _ _ _); [st_eq| exact COST| exact CR| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_csg : forall (gs ge : Z) (cb cost len : zarr) (v32 v48 v56 v88 v20 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a5 a7 s10 t3 t4 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    (forall m', munch Wc mf m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    (forall m', munch Wc mf m' -> u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548)) ->
    u8arr b0segs m CO (zb8 cb 12) -> COSTREL cb cost nG ->
    mem_inv b0segs m -> munch Wc mf m -> wmono b0segs mf m ->
    shzW b0segs Wc mf A1 (A1 + ARR1_SIZE) -> shzW b0segs Wc mf E (E + ESTATE_SIZE) -> shpW b0segs Wc mf CO (CO + 12) ->
    frdW b0segs Wc mf (P + 1384) (HITg v32 v48 v56 v88 v20) ->
    (forall m' cb' (t0 t1 t2 a0 a2 a3 a5 a7 t3 t4 : word),
      u8arr b0segs m' CO (zb8 cb' 12) -> COSTREL cb' (sm_cost_slow (Z.to_nat (ge + 1 - gs)) cost len arr1 nG gs) nG ->
      mem_inv b0segs m' -> munch Wc mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 (ge + 1)) a2 a3 (Z_to_bv 64 (ge + 1)) a5 (Z_to_bv 64 gs) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8f920) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (ge + 1)) a5 (Z_to_bv 64 gs) a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f7f8) fc None m (seg_rom b0segs)).
  Proof.
    intros gs ge cb cost len v32 v48 v56 v88 v20 m mf t0 t1 t2 a0 a1 a2 a3 a5 a7 s10 t3 t4 Hgs Hge LF VAR1 VLEN COST CR MI MU WM SHa SHe SHc VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    (* [comment removed for export] *)
    lstepA; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    lstepA.
    enter_with (B0_sm_csto (Z.to_nat (ge + 1 - gs)) gs ge cb cost len v32 v48 v56 v88 v20 m mf);
      [st_eq| lia| lia| lia| lia| exact LF| exact VAR1| exact VLEN| exact COST| exact CR| exact MI| exact MU| exact WM| exact SHa| exact SHe| exact SHc| exact VHI|].
    intros m' cb' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 COST' CR' MI' MU' WM'.
    enter_with (K m' cb' _ _ _ _ _ _ _ _ _ _); [st_eq| exact COST'| exact CR'| exact MI'| exact MU'| exact WM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  Notation ROWF t := (E + 45448 + 1032 * t)%Z.
  Lemma B0_sm_rfsl : forall (n : nat) (i bt B : Z) (rf : zarr) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a1 a7 s10 t3 t4 : word),
    (0 <= i)%Z -> (1 <= n)%nat -> (i + Z.of_nat n <= nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + Z.of_nat n <= 2000000000)%Z ->
    (forall m', munch Wrf mf m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    u32arr b0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv b0segs m -> munch Wrf mf m -> wmono b0segs mf m ->
    shzW b0segs Wrf mf A1 (A1 + ARR1_SIZE) -> shzW b0segs Wrf mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wrf mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' rf' (t0 t1 a1 a7 : word),
      u32arr b0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc n rf arr1 bt i -> RFrow rf' bt A (B + Z.of_nat n) ->
      mem_inv b0segs m' -> munch Wrf mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (A1 + 2 * (i + Z.of_nat n))) a1 (Z_to_bv 64 (ROWF bt)) (Z_to_bv 64 (A1 + 2 * (i + Z.of_nat n))) (Z_to_bv 64 (i + Z.of_nat n)) (NOT (ROWF bt))
                            (Z_to_bv 64 (i + Z.of_nat n)) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x91d9c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 (A1 + 2 * i)) a1 (Z_to_bv 64 (ROWF bt)) (Z_to_bv 64 (A1 + 2 * i)) (Z_to_bv 64 (i + Z.of_nat n)) (NOT (ROWF bt)) (Z_to_bv 64 i) a7 s10 t3 t4)
                     F (Z_to_bv 64 0x91cc8) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros i bt B rf v32 v48 v56 v88 v20 v28 m mf t0 t1 t2 a1 a7 s10 t3 t4 Hi0 Hn Hend Hbt HB HBn VAR1 RFQ RFF MI MU WM SHa SHe VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rf (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    pose proof (MV i ltac:(lia)) as MVi. destruct (RFF (mtfv_at arr1 i) MVi) as [Dr Rr].
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. brun.
    pose proof (VAR1 m MU) as AR1.
    pose proof (zb8_read2 b0segs m A1 arr1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 arr1 (2 * i)) with (mtfv_at arr1 i) in RD.
    lstepA. clear RD AR1. rewrite (zx16_lit (mtfv_at arr1 i)) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs m (E + 45448) rf (jseg J 45448 6192) 1548 (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(lia) Dr ltac:(unfold wa; f_equal; lia)) as RD.
    lstepA. clear RD. rewrite (sx32_of_Z (zget rf (258 * bt + mtfv_at arr1 i))) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    brun. clear RO.
    pose proof (u32arr_store_ok b0segs m (E + 45448) _ (258 * bt + mtfv_at arr1 i) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    lstepA. store_addr (E + 45448 + 4 * (258 * bt + mtfv_at arr1 i))%Z.
    ovw_store RFQ (258 * bt + mtfv_at arr1 i)%Z (zget rf (258 * bt + mtfv_at arr1 i) + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset rf (258 * bt + mtfv_at arr1 i) (zget rf (258 * bt + mtfv_at arr1 i) + 1)) with (zincr rf (258 * bt + mtfv_at arr1 i)) in RFQ.
    pose proof (RFrow_incr rf bt A B (mtfv_at arr1 i) RFF MVi) as RFF'.
    rewrite sm_rfreq_inc_S in K.
    (* [comment removed for export] *)
    lstepA. lstepA. lstepA. lstepA; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (i + 1)%Z bt (B + 1)%Z _ v32 v48 v56 v88 v20 v28 _ mf);
        [st_eq| lia| lia| lia| lia| lia| lia| exact VAR1| exact RFQ| exact RFF'| assumption| assumption| assumption| exact SHa| unfold ESTATE_SIZE; exact SHe| exact VHI|].
      intros m' rf' y0 y1 ya1 y7 RFQ' E' RFF2 MI' MU' WM'.
      enter_with (K m' rf' y0 y1 ya1 y7); [st_eq| exact RFQ'| exact E'| eapply RFrow_weaken; [exact RFF2| lia]| exact MI'| exact MU'| exact WM'].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_inc] in K. lstepA.
      enter_with (K _ _ _ _ _ _); [st_eq| exact RFQ| reflexivity| eapply RFrow_weaken; [exact RFF'| lia]| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_rfsg : forall (gs ge bt B : Z) (rf : zarr) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a2 a3 a5 a7 s10 t3 t4 : word),
    (0 <= gs <= ge)%Z -> (ge < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= B)%Z -> (B + (ge + 1 - gs) <= 2000000000)%Z ->
    (forall m', munch Wrf mf m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    u32arr b0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) -> RFrow rf bt A B ->
    mem_inv b0segs m -> munch Wrf mf m -> wmono b0segs mf m ->
    shzW b0segs Wrf mf A1 (A1 + ARR1_SIZE) -> shzW b0segs Wrf mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wrf mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' rf' (t0 t1 a0 a1 a2 a3 a5 a7 : word),
      u32arr b0segs m' (E + 45448) (ovw rf' (jseg J 45448 6192) 1548) -> rf' = sm_rfreq_inc (Z.to_nat (ge + 1 - gs)) rf arr1 bt gs -> RFrow rf' bt A (B + (ge + 1 - gs)) ->
      mem_inv b0segs m' -> munch Wrf mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (ge + 1)) a5 (Z_to_bv 64 (ge + 1)) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x91d9c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 bt) a2 a3 (Z_to_bv 64 (ge + 1)) a5 (Z_to_bv 64 gs) a7 s10 t3 t4)
                     F (Z_to_bv 64 0x91c8c) fc None m (seg_rom b0segs)).
  Proof.
    intros gs ge bt B rf v32 v48 v56 v88 v20 v28 m mf t0 t1 t2 a0 a2 a3 a5 a7 s10 t3 t4 Hgs Hge Hbt HB HBn VAR1 RFQ RFF MI MU WM SHa SHe VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    (* [comment removed for export] *)
    lstepA; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. brun_to 0x91cc8%Z. clear RO.
    enter_with (B0_sm_rfsl (Z.to_nat (ge + 1 - gs)) gs bt B rf v32 v48 v56 v88 v20 v28 m m);
      [st_eq| lia| lia| lia| lia| lia| lia| | exact RFQ| exact RFF| exact MI| apply munch_refl| apply wmono_refl| | | |].
    { apply (vw_sub _ Wrf Wrf mf m VAR1 MU). a_sub_fp. }
    { eapply (shzW_sub b0segs Wrf Wrf mf m); [exact SHa| exact MU| a_sub_fp| lia| lia]. }
    { eapply (shzW_sub b0segs Wrf Wrf mf m); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
    { eapply (frdW_sub b0segs Wrf Wrf mf m); [exact VHI| exact MU| a_sub_fp]. }
    clear RFQ RFF MI. intros m' rf' y0 y1 ya1 y7 RFQ E' RFF MI MU1 WM1.
    transport_after_call b0segs m m' MU1 WM1. clear MU1 WM1.
    enter_with (K m' rf' _ _ _ _ _ _ _ _); [st_eq| exact RFQ| exact E'| replace (B + (ge + 1 - gs))%Z with (B + Z.of_nat (Z.to_nat (ge + 1 - gs)))%Z by lia; exact RFF| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac lit_store2 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?v)) _) => change (Z_to_le_bytes 2 v) with (le2 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Notation Wh := [(P + 1384, P + 1568); (CO, CO + 12)]%Z.
  Lemma B0_sm_head : forall (gs : Z) (jc : list byte) (v32 v48 v88 v20 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s10 t3 t4 : word),
    (0 <= gs < nMTF)%Z -> length jc = 12%nat ->
    u8arr b0segs m CO jc ->
    rw_cells b0segs m (P + 1384) (HIT v32 v48 (Z_to_bv 64 nMTF) v88 v20 v28) ->
    mem_inv b0segs m -> munch Wh mf m -> wmono b0segs mf m ->
    (forall m' (a0 a1 : word), let ge := GE nMTF gs in fastb nG nMTF gs = true ->
      u8arr b0segs m' CO (zb8 znew 12) ->
      rw_cells b0segs m' (P + 1384) (HIT (Z_to_bv 64 ge) v48 (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) v20 v28) ->
      mem_inv b0segs m' -> munch Wh mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (ge + 1)) a5 (Z_to_bv 64 gs) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8c820) fc None m' (seg_rom b0segs))) ->
    (forall m' (a0 a1 : word), let ge := GE nMTF gs in fastb nG nMTF gs = false ->
      u8arr b0segs m' CO (zb8 znew 12) ->
      rw_cells b0segs m' (P + 1384) (HIT (Z_to_bv 64 ge) v48 (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) v20 v28) ->
      mem_inv b0segs m' -> munch Wh mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (ge + 1)) a5 (Z_to_bv 64 gs) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8f7f8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8c7a4) fc None m (seg_rom b0segs)).
  Proof.
    intros gs jc v32 v48 v88 v20 v28 m mf t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s10 t3 t4 Hgs Ljc COST HI MI MU WM KF KS.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof COH as COH'. unfold CEIL in COH'.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    openHI HI.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    (* [comment removed for export] *)
    lstep. lstep; lit_store. brun_to 0x8c7c4%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (GEd : forall (xa0 : word),
      evt b0segs Q (MS (GRB t0 t1 t2 xa0 (Z_to_bv 64 (gs + 50)) a2 a3 (Z_to_bv 64 (GE nMTF gs + 1)) a5 (Z_to_bv 64 gs) a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8c7cc) fc None mm (seg_rom b0segs))) end.
    2:{ lstep; if_cases K1; zify_cond_z K1.
        - enter_with (GEd _); [st_eq; try (unfold GE, BZ_G_SIZE; destruct (Z.leb_spec nMTF (gs + 50 - 1)); lia)].
        - lstep. enter_with (GEd _); [st_eq; try (unfold GE, BZ_G_SIZE; destruct (Z.leb_spec nMTF (gs + 50 - 1)); lia)]. }
    intros xa0. set (ge := GE nMTF gs) in *.
    cps_destruct (cost_cells_of_junk6 b0segs _ CO jc COST Ljc) as (c1 & c2 & c3 & c4 & c5 & c6 & CC). clear COST.
    (* [comment removed for export] *)
    lstep. lstep; lit_store. lstep.
    (* [comment removed for export] *)
    do 5 ((lstep; lit_store2); lstep; lstep; if_cases Kl; zify_cond_z Kl; [clear Kl| exfalso; lia]).
    (lstep; lit_store2). lstep. lstep; if_cases Kl; zify_cond_z Kl; [exfalso; lia| clear Kl].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (cost_zero_cells6 b0segs mm CO CC) as COST end. clear CC.
    (* [comment removed for export] *)
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    lstep. lstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
      brun_to 0x8c818%Z.
      lstep; if_cases K50; zify_cond_z K50.
      + assert (FB : fastb nG nMTF gs = true) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KF mm _ _ FB) end;
          [st_eq| exact COST| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
      + lstep.
        assert (FB : fastb nG nMTF gs = false) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ _ FB) end;
          [st_eq| exact COST| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
      lstep.
      assert (FB : fastb nG nMTF gs = false) by (unfold fastb; replace (nG =? 6)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ _ FB) end;
        [st_eq| exact COST| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wpo := [(E + 1704, E + 19706); (P + 1384, P + 1568); (FV, FV + 24)]%Z.
  Lemma B0_sm_post : forall (gs bt bc totc nSel : Z) (fave sel : zarr) (v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a2 a3 a7 s10 t3 t4 : word),
    (0 <= gs < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= bc <= 65535)%Z -> (0 <= totc)%Z -> (totc + bc < 2147483648)%Z -> (0 <= nSel < 18002)%Z ->
    (0 <= zget fave bt <= 18001)%Z ->
    u32arr b0segs m FV (zw32 fave 6) ->
    u8arr b0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    rw_cells b0segs m (P + 1384) (HIT (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 totc) (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 nSel) v28) ->
    mem_inv b0segs m -> munch Wpo mf m -> wmono b0segs mf m ->
    shzW b0segs Wpo mf FV (FV + 24) -> shzW b0segs Wpo mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wpo mf (P + 1264) (sm_set cx FV) ->
    (forall m' (a0 a2 a3 : word), fastb nG nMTF gs = true ->
      u32arr b0segs m' FV (zw32 (zincr fave bt) 6) ->
      u8arr b0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells b0segs m' (P + 1384) (HIT (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 (totc + bc)) (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 nSel) v28) ->
      mem_inv b0segs m' -> munch Wpo mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 (1032 * bt)) a2 a3 (Z_to_bv 64 (GE nMTF gs + 1)) (Z_to_bv 64 (zget fave bt)) (Z_to_bv 64 gs) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8fadc) fc None m' (seg_rom b0segs))) ->
    (forall m' (a0 a2 a3 : word), fastb nG nMTF gs = false ->
      u32arr b0segs m' FV (zw32 (zincr fave bt) 6) ->
      u8arr b0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells b0segs m' (P + 1384) (HIT (Z_to_bv 64 (GE nMTF gs)) (Z_to_bv 64 (totc + bc)) (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 nSel) v28) ->
      mem_inv b0segs m' -> munch Wpo mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 (Z_to_bv 64 bt) a2 a3 (Z_to_bv 64 (GE nMTF gs + 1)) (Z_to_bv 64 (zget fave bt)) (Z_to_bv 64 gs) a7 s10 t3 t4)
                       F (Z_to_bv 64 0x91c8c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 (Z_to_bv 64 bc) (Z_to_bv 64 bt) a2 a3 (Z_to_bv 64 (GE nMTF gs + 1)) (Z_to_bv 64 nG) (Z_to_bv 64 gs) a7 s10 t3 t4)
                     F (Z_to_bv 64 0x8f9d0) fc None m (seg_rom b0segs)).
  Proof.
    intros gs bt bc totc nSel fave sel v28 m mf t0 t1 t2 a2 a3 a7 s10 t3 t4 Hgs Hbt Hbc Htc Htb HnS Hfv FAVE SEL HI MI MU WM SHf SHe VSET KF KS.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof FVH as FVH'. unfold CEIL in FVH'. unfold ESTATE_SIZE in SHe.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3). set (ge := GE nMTF gs) in *.
    pose proof (zw32_length_nat fave 6) as LFV. pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length sel (jseg J 1704 18002) 18002 ltac:(lia)) as LSL.
    openHI HI.
    (* [comment removed for export] *)
    pose proof (rw_cells_lw_C8 b0segs m (P + 1384) [_; _; _; _; _; _; _; _] _ _ _ HI ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD.
    lstep. clear RD.
    (* [comment removed for export] *)
    lstep. lstep. lstep; lit_store.
    (* [comment removed for export] *)
    poseV VSET RO. unfold sm_set in RO; cbv zeta in RO. brun.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read b0segs mm FV fave 6 bt _ FAVE ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    lstep. clear RD. try rewrite (sx32_of_Z (zget fave bt)) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    brun. clear RO.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm FV _ bt _ FAVE ltac:(rewrite zw32_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    lstep. store_addr (FV + 4 * bt)%Z. zw32_store FAVE bt (zget fave bt + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset fave bt (zget fave bt + 1)) with (zincr fave bt) in FAVE.
    (* [comment removed for export] *)
    poseV VSET RO. unfold sm_set in RO; cbv zeta in RO. brun. clear RO.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok b0segs mm (E + 1704) _ nSel _ SEL ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    lstep. store_addr (E + 1704 + nSel)%Z. ovb_store1 SEL nSel.
    replace (wr8 sel nSel (bv_unsigned (Z_to_bv 64 bt))) with (zset sel nSel (bt mod 256)) in SEL by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    lstep. lstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
      (* [comment removed for export] *)
      brun_to 0x8fab8%Z.
      lstep; if_cases K50; zify_cond_z K50.
      + assert (FB : fastb nG nMTF gs = true) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        (* [comment removed for export] *)
        brun_to 0x8fadc%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KF mm _ _ _ FB) end;
          [st_eq| exact FAVE| exact SEL| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
      + lstep.
        assert (FB : fastb nG nMTF gs = false) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ _ _ FB) end;
          [st_eq| exact FAVE| exact SEL| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
      lstep.
      assert (FB : fastb nG nMTF gs = false) by (unfold fastb; replace (nG =? 6)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ _ _ FB) end;
        [st_eq| exact FAVE| exact SEL| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wt := [(P + 1384, P + 1568)]%Z.
  Lemma B0_sm_tail : forall (gs nSel : Z) (v32 v48 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    (0 <= gs < nMTF)%Z -> (0 <= nSel < 18002)%Z ->
    rw_cells b0segs m (P + 1384) (HIT v32 v48 (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 nSel) v28) ->
    mem_inv b0segs m -> munch Wt mf m -> wmono b0segs mf m ->
    (forall m' (a0 a1 : word), (gs + 50 < nMTF)%Z ->
      rw_cells b0segs m' (P + 1384) (HIT v32 v48 (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (nSel + 1)) v28) ->
      mem_inv b0segs m' -> munch Wt mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4)
                       F (Z_to_bv 64 0x8c7a4) fc None m' (seg_rom b0segs))) ->
    (forall m' (a0 a1 : word), (nMTF <= gs + 50)%Z ->
      rw_cells b0segs m' (P + 1384) (HIT v32 v48 (Z_to_bv 64 nMTF) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (nSel + 1)) v28) ->
      mem_inv b0segs m' -> munch Wt mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4)
                       F (Z_to_bv 64 0x9394c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (GRB t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4)
                     F (Z_to_bv 64 0x91d9c) fc None m (seg_rom b0segs)).
  Proof.
    intros gs nSel v32 v48 v28 m mf t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 Hgs HnS HI MI MU WM KN KX.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    openHI HI.
    (* [comment removed for export] *)
    lstep. lstep. lstep; lit_store. lstep. lstep. lstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KX mm _ _ ltac:(lia)) end;
        [st_eq| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
    - (* [comment removed for export] *)
      lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KN mm _ _ ltac:(lia)) end;
        [st_eq| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; eassumption| assumption| assumption| assumption].
  Qed.
End GBB.
End ACeilS1.
