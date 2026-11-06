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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCSortF BzArrD CmpMem CmpCut BzCLemmasFs BzCFactsFs CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs2 A0_cmp_fsV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

Lemma rw_cells_cutZ : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.

(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Lemma land_m32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (32 * (x / 32))%Z.
Proof.
  intros x Hx. change 18446744073709551584%Z with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5)%Z with 32%Z. lia.
Qed.

(* [comment removed for export] *)
Definition FSAVED (X : fsenv) : list cell :=
  [C8 (fe_s11 X); C8 (fe_s10 X); C8 (fe_s9 X); C8 (fe_s8 X); C8 (fe_s7 X); C8 (fe_s6 X); C8 (fe_s5 X); C8 (fe_s4 X); C8 (fe_s3 X);
   C8 (fe_s2 X); C8 (fe_s1 X); C8 (fe_s0 X); C8 (fe_ra X)].

Section A0FSP1.
  Variable X : fsenv. Variable P : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : fsenv_ok X.
  (* [comment removed for export] *)
  Hypothesis YPl : (fe_lo X <= P)%Z. Hypothesis YPh : (P + 1376 <= bv_unsigned (fe_sp X))%Z. Hypothesis YPa : (bv_unsigned (fe_sp X) <= P + 1392)%Z.
  Notation usp := (bv_unsigned (fe_sp X)).
  Notation A1 := (fe_A1 X). Notation A2 := (fe_A2 X). Notation FT := (fe_FT X). Notation nb := (fe_nb X).
  Notation gp := (fe_gp X). Notation tp := (fe_tp X). Notation F := (fe_F X). Notation fc := (fe_fc X). Notation lo := (fe_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_fs_P1 : forall (qP : Z) (m : word -> option byte) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    (P = 32 * qP)%Z ->
    stk a0segs m lo usp -> mem_inv a0segs m -> aconsts A0C m -> aconsts_uar A0C m ->
    (forall m' (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 : word) (v80 v88 v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 v184 v192 v200 v208 v216 : word)
            (v224 v232 : word) (j4 jft : list byte) (a1 a2 : word),
      rw_cells a0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72] ->
      rw_cells a0segs m' (P + 80) [C8 v80; C8 v88; C8 (Z_to_bv 64 nb); C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144; C8 v152; C8 v160; C8 v168; C8 v176;
                                   C8 v184; C8 v192; C8 v200; C8 v208; C8 v216] ->
      rw_cells a0segs m' (P + 224) [C8 v224; C8 v232; CB 4 j4] -> rw_cells a0segs m' (P + 244) [CB 1028 jft] ->
      stk a0segs m' (P + 1272) (usp + -104) -> rw_cells a0segs m' (usp + -104) (FSAVED X) ->
      stk a0segs m' lo P -> mem_inv a0segs m' -> munch [(P, usp)]%Z m m' -> wmono a0segs m m' ->
      evt a0segs Q (MS (mkR (Z_to_bv 64 0x9aab4) (Z_to_bv 64 P) gp tp t0 t1 t2 (fe_sp X) (Z_to_bv 64 P) (Z_to_bv 64 2112) a1 a2 (Z_to_bv 64 nb) (Z_to_bv 64 0) a5 a6 a7
                            (fe_s2 X) (fe_s3 X) (Z_to_bv 64 A2) (Z_to_bv 64 A1) cSB (Z_to_bv 64 0) (Z_to_bv 64 FT) (fe_s9 X) (fe_s10 X) (fe_s11 X) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3e268) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (fe_ra X) (fe_sp X) gp tp t0 t1 t2 (fe_s0 X) (fe_s1 X) (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 FT) (Z_to_bv 64 nb) (Z_to_bv 64 0)
                          a5 a6 a7 (fe_s2 X) (fe_s3 X) (fe_s4 X) (fe_s5 X) (fe_s6 X) (fe_s7 X) (fe_s8 X) (fe_s9 X) (fe_s10 X) (fe_s11 X) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x9aa30) fc None m (seg_rom a0segs)).
  Proof.
    intros qP m t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 EqP ST MI AC AU K.
    fsenv_open XOK.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar A0C ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl a0segs m) as WM.
    assert (CASE : (P = usp - 1376 \/ P = usp - 1392)%Z) by lia.
    assert (ELAND : Z.land (usp + -1376) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - CASE EqP ALS. Z.div_mod_to_equations. lia. }
    destruct CASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 1376%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 1376 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8; 8;8;4; 1028; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -1376)%Z with P in FR, ST by lia.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      (* [comment removed for export] *)
      arun_to 0x3e268%Z.
      cb8_all FR.
      destruct (rw_cells_cutZ a0segs _ P _ 10%nat FR) as [SLa R1]. cbn [firstn skipn cells_size csize Nat.add] in SLa, R1. change (Z.of_nat 80) with 80%Z in R1.
      destruct (rw_cells_cutZ a0segs _ _ _ 18%nat R1) as [SLb R2]. cbn [firstn skipn cells_size csize Nat.add] in SLb, R2. change (Z.of_nat 144) with 144%Z in R2.
      replace (P + 80 + 144)%Z with (P + 224)%Z in R2 by lia.
      destruct (rw_cells_cutZ a0segs _ _ _ 3%nat R2) as [SLc R3]. cbn [firstn skipn cells_size csize Nat.add] in SLc, R3. change (Z.of_nat 20) with 20%Z in R3.
      replace (P + 224 + 20)%Z with (P + 244)%Z in R3 by lia.
      destruct (rw_cells_cutZ a0segs _ _ _ 1%nat R3) as [FTJ SVc]. cbn [firstn skipn cells_size csize Nat.add] in FTJ, SVc. change (Z.of_nat 1028) with 1028%Z in SVc.
      replace (P + 244 + 1028)%Z with (usp + -104)%Z in SVc by lia.
      eapply K; [exact SLa| exact SLb| exact SLc| exact FTJ| | exact SVc| exact ST| assumption| exact MU| exact WM].
      split; [lia|]. split; [lia|]. intros a Ha. lia.
    - (* [comment removed for export] *)
      carve_frame 1392%nat ST.
      apply (rw_cells_split_CB a0segs _ _ [] 1392 _ [] [8;8;8;8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8; 8;8;4; 1028; 8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -1392)%Z with P in FR, ST by lia.
      wstep. wstep. wstep.
      arun_to 0x3e268%Z.
      cb8_all FR.
      destruct (rw_cells_cutZ a0segs _ P _ 10%nat FR) as [SLa R1]. cbn [firstn skipn cells_size csize Nat.add] in SLa, R1. change (Z.of_nat 80) with 80%Z in R1.
      destruct (rw_cells_cutZ a0segs _ _ _ 18%nat R1) as [SLb R2]. cbn [firstn skipn cells_size csize Nat.add] in SLb, R2. change (Z.of_nat 144) with 144%Z in R2.
      replace (P + 80 + 144)%Z with (P + 224)%Z in R2 by lia.
      destruct (rw_cells_cutZ a0segs _ _ _ 3%nat R2) as [SLc R3]. cbn [firstn skipn cells_size csize Nat.add] in SLc, R3. change (Z.of_nat 20) with 20%Z in R3.
      replace (P + 224 + 20)%Z with (P + 244)%Z in R3 by lia.
      destruct (rw_cells_cutZ a0segs _ _ _ 1%nat R3) as [FTJ R4]. cbn [firstn skipn cells_size csize Nat.add] in FTJ, R4. change (Z.of_nat 1028) with 1028%Z in R4.
      replace (P + 244 + 1028)%Z with (P + 1272)%Z in R4 by lia.
      destruct (rw_cells_cutZ a0segs _ _ _ 2%nat R4) as [GAPc SVc]. cbn [firstn skipn cells_size csize Nat.add] in GAPc, SVc. change (Z.of_nat 16) with 16%Z in SVc.
      replace (P + 1272 + 16)%Z with (usp + -104)%Z in SVc by lia.
      pose proof (stk_of_rw_cells a0segs _ _ _ GAPc) as GAPs. cbn [cells_size csize Nat.add] in GAPs. change (Z.of_nat 16) with 16%Z in GAPs.
      replace (P + 1272 + 16)%Z with (usp + -104)%Z in GAPs by lia.
      eapply K; [exact SLa| exact SLb| exact SLc| exact FTJ| exact GAPs| exact SVc| exact ST| assumption| exact MU| exact WM].
  Qed.
End A0FSP1.

End ACeilS1.
