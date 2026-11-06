(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_cbV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section B0CBE.
  Variable X : cbenv. Variable Y : acenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y).
  Notation E := (c_E cx).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).

  Lemma B0_cb_E1 : forall (m : word -> option byte) (FL : Z)
      (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    ro_cells b0segs m (FB + 504) [C8 (Z_to_bv 64 FL)] ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 FB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ac54) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 FB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ac50) fc None m (seg_rom b0segs)).
  Proof.
    intros m FL ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLP K.
    acenv_open YOK.
    wstep. exact K.
  Qed.

  Lemma B0_cb_E2 : forall (m : word -> option byte) (FL : Z) (b1 : byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m FL [C1 b1] -> mem_inv b0segs m ->
    (forall m', rw_cells b0segs m' FL [C1 z8] -> mem_inv b0segs m' -> munch [(FL, FL + 1)]%Z m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x8ac58) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ac54) fc None m (seg_rom b0segs)).
  Proof.
    intros m FL b1 ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLC MI K.
    pose proof (munch_refl [(FL, FL + 1)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    wstep. change (le1 (Z_to_bv 64 0)) with [z8]. mem_after_store.
    eapply K; [exact FLC| exact MI| exact MU| exact WM].
  Qed.

  Lemma stk_join8 : forall segs m a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> (a <= b <= c)%Z -> stk segs m a c.
  Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.
  Ltac stk_add8 ST K :=
    lazymatch type of K with stk _ _ ?b' ?c =>
    lazymatch type of ST with stk ?segs ?m ?lo ?b =>
      let H := fresh in pose proof (stk_join8 segs m lo b b' c ST K ltac:(lia) ltac:(lia)) as H; clear ST K; rename H into ST end end.

  Lemma B0_cb_E3 : forall (m : word -> option byte) (sl : cbslB)
      (ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m P (cbslB_cells sl) -> stk b0segs m (P + 184) (usp + -104) -> rw_cells b0segs m (usp + -104) (CSAVED X) -> stk b0segs m lo P ->
    (stk b0segs m lo usp ->
      evt b0segs Q (MS (mkR (ce_ra X) (ce_sp X) gp tp t0 t1 t2 (ce_s0 X) (ce_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                            (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3 t4 t5 t6)
                       F (ret_pc (ce_ra X)) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (ce_sp X) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8ac58) fc None m (seg_rom b0segs)).
  Proof.
    intros m sl ra sp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SL GAP SAV ST K.
    cbenv_open XOK. clear CX SEP. acenv_open YOK. unfold CSAVED in SAV.
    (* [comment removed for export] *)
    wstep. wstep. do 13 wstep. wstep.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells b0segs _ _ _ SL) as K0. cbn [cbslB_cells cells_size csize Nat.add] in K0. change (Z.of_nat 184) with 184%Z in K0.
    pose proof (stk_of_rw_cells b0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add] in K5. change (Z.of_nat 104) with 104%Z in K5.
    stk_add8 ST K0. stk_add8 ST GAP. stk_add8 ST K5.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with usp in ST by lia end.
    replace (Z_to_bv 64 (usp + -288 + 288)) with (ce_sp X) by (rewrite <- (Z_to_bv_bv_unsigned (ce_sp X)) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep.
    exact (K ST).
  Qed.
End B0CBE.

End ACeilS1.
