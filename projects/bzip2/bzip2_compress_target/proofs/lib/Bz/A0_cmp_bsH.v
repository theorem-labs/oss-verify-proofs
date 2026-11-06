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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW A0_cmp_bsE.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis YOK : amenv_ok X Y.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y). Notation E := (me_E X).
  Notation FT := (me_FT X). Notation n := (me_n X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).

  Ltac sb0 := wstep; change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store.

  Lemma A0_bs_P6 : forall (me m : word -> option byte) (b : byte) (v200 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m (SHF + 322) (shcB b) -> mem_inv a0segs m -> munch [(SHF + 322, SHF + 354)]%Z me m -> wmono a0segs me m ->
    frdW a0segs [(SHF + 322, SHF + 354)]%Z me (P + 200) [C8 v200; C8 (Z_to_bv 64 (SHF + 362))] ->
    (forall m', rw_cells a0segs m' (SHF + 322) (shcB z8) -> mem_inv a0segs m' -> munch [(SHF + 322, SHF + 354)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x97c70) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 362)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                             x18 x19 x20 x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x558c4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 (Z_to_bv 64 SHF) x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97be4) fc None m (seg_rom a0segs)).
  Proof.
    intros me m b v200 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 SH MI MU WMo V K.
    unfold shcB in SH.
    (* [comment removed for export] *)
    do 32 sb0. wstep.
    pose proof (V _ MU) as RO_. wstep. clear RO_. wstep.
    apply K; [unfold shcB; exact SH| exact MI| exact MU| exact WMo].
  Qed.

  Lemma A0_bs_P7 : forall (m : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m (P + 200) [C8 (Z_to_bv 64 (SHF + 506))] -> mem_inv a0segs m ->
    (evt a0segs Q (MS (mkR (Z_to_bv 64 0x97c7c) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 (SHF + 506)) (Z_to_bv 64 128) x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x558c4) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97c70) fc None m (seg_rom a0segs)).
  Proof.
    intros m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 SL MI K.
    wstep. wstep. wstep. exact K.
  Qed.

  Notation WP8 := [(P + 104, P + 152); (P + 152, P + 200)]%Z.
  Lemma A0_bs_P8 : forall (me m : word -> option byte) (SHn : Z) (s5v v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 w184 v192 : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells a0segs m (P + 104) [C8 v104; C8 v112; C8 v120; C8 v128; C8 v136; C8 v144] ->
    rw_cells a0segs m (P + 152) [C8 v152; C8 v160; C8 v168; C8 v176; C8 w184; C8 v192] ->
    rw_cells a0segs m (P + 248) [C8 (Z_to_bv 64 0)] -> mem_inv a0segs m -> munch WP8 me m -> wmono a0segs me m ->
    (forall m',
       rw_cells a0segs m' (P + 104) [C8 (Z_to_bv 64 SHn); C8 (Z_to_bv 64 (E + 108)); C8 (Z_to_bv 64 (SHF + 178)); C8 (Z_to_bv 64 E); C8 v136; C8 s5v] ->
       rw_cells a0segs m' (P + 152) [C8 v152; C8 v160; C8 v168; C8 (Z_to_bv 64 SHF); C8 w184; C8 v192] ->
       rw_cells a0segs m' (P + 248) [C8 (Z_to_bv 64 0)] -> mem_inv a0segs m' -> munch WP8 me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x97cb8) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 FT) (Z_to_bv 64 0) (Z_to_bv 64 262148) x13 x14 x15 x16 x17
                             (Z_to_bv 64 (E + 108)) cSB (Z_to_bv 64 n) s5v (Z_to_bv 64 SHF) (Z_to_bv 64 FT) (Z_to_bv 64 FB) (Z_to_bv 64 E) (Z_to_bv 64 (SHF + 178))
                             (Z_to_bv 64 SHn) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (E + 108)) cSB (Z_to_bv 64 n) s5v (Z_to_bv 64 SHF) (Z_to_bv 64 FT) (Z_to_bv 64 FB) (Z_to_bv 64 E) (Z_to_bv 64 (SHF + 178))
                          (Z_to_bv 64 SHn) x28 x29 x30 x31)
                     F (Z_to_bv 64 0x97c7c) fc None m (seg_rom a0segs)).
  Proof.
    intros me m SHn s5v v104 v112 v120 v128 v136 v144 v152 v160 v168 v176 w184 v192 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 SL SK VB MI MU WMo K.
    msenv_open XOK. amenv_open YOK.
    (* [comment removed for export] *)
    astep. astep. astep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    apply K; [exact SL| exact SK| exact VB| exact MI| exact MU| exact WMo].
  Qed.
End A0MS.

End ACeilS1.
