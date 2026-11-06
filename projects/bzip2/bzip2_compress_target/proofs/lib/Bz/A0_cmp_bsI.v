(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW A0_cmp_bsE A0_cmp_bsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma rw_cells_cutI : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [f8b]; mem_after_store.
  Ltac sbf2 := wstep; change (le1 (Z_to_bv 64 (-14))) with [f2b]; mem_after_store.
  Ltac sbx := first [sbf8 | sbf2].

  Lemma A0_bs_P3 : forall (me m : word -> option byte) (bs : list byte) (v200 v208 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m (SHF + 306) [CB 56 bs] -> rw_cells a0segs m (P + 200) [C8 v200; C8 v208] -> mem_inv a0segs m ->
    munch [(SHF + 306, SHF + 362); (P + 200, P + 216)]%Z me m -> wmono a0segs me m ->
    (forall m', rw_cells a0segs m' (SHF + 322) (shcB f8b) -> rw_cells a0segs m' (P + 200) [C8 v200; C8 (Z_to_bv 64 (SHF + 362))] -> mem_inv a0segs m' ->
       munch [(SHF + 306, SHF + 362); (P + 200, P + 216)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x97a38) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             (Z_to_bv 64 (-8)) x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (-8)) x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97948) fc None m (seg_rom a0segs)).
  Proof.
    intros me m bs v200 v208 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 RZ SL MI MU WMo K.
    msenv_open1 XOK. amenv_open YOK. amenv_shx_open X Y SHF YSHX.
    apply (rw_cells_split_CB a0segs _ _ [] 56%nat _ [] (repeat 1%nat 56)) in RZ; [| reflexivity]. cbn [repeat mk_CB_cells app] in RZ.
    do 56 sbx.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    destruct (rw_cells_cutI a0segs _ _ _ 16 RZ) as [_ RZ1]. cbn [firstn skipn cells_size csize Nat.add] in RZ1. change (Z.of_nat 16) with 16%Z in RZ1.
    replace (SHF + 306 + 16)%Z with (SHF + 322)%Z in RZ1 by lia.
    destruct (rw_cells_cutI a0segs _ _ _ 32 RZ1) as [RZ2 _]. cbn [firstn] in RZ2.
    apply K; [exact RZ2| exact SL| exact MI| exact MU| exact WMo].
  Qed.

  Lemma A0_bs_P4 : forall (me m : word -> option byte) (bs : list byte) (v200 v208 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m (SHF + 490) [CB 16 bs] -> rw_cells a0segs m (P + 200) [C8 v200; C8 v208] -> mem_inv a0segs m ->
    munch [(SHF + 490, SHF + 506); (P + 200, P + 216)]%Z me m -> wmono a0segs me m ->
    (forall m', rw_cells a0segs m' (P + 200) [C8 (Z_to_bv 64 (SHF + 506)); C8 v208] -> mem_inv a0segs m' ->
       munch [(SHF + 490, SHF + 506); (P + 200, P + 216)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x97a88) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 506)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             x18 x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 (Z_to_bv 64 (-14)) x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97a38) fc None m (seg_rom a0segs)).
  Proof.
    intros me m bs v200 v208 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 RZ SL MI MU WMo K.
    msenv_open1 XOK. amenv_open YOK. amenv_shx_open X Y SHF YSHX.
    apply (rw_cells_split_CB a0segs _ _ [] 16%nat _ [] (repeat 1%nat 16)) in RZ; [| reflexivity]. cbn [repeat mk_CB_cells app] in RZ.
    do 16 sbf2.
    wstep. wstep. wstep. wstep.
    apply K; [exact SL| exact MI| exact MU| exact WMo].
  Qed.
End A0MS.

End ACeilS1.
