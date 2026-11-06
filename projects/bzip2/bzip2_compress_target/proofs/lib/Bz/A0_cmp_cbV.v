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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Record cbenv := CBE {
  ce_ra : word; ce_sp : word; ce_gp : word; ce_tp : word;
  ce_s0 : word; ce_s1 : word; ce_s2 : word; ce_s3 : word; ce_s4 : word; ce_s5 : word;
  ce_s6 : word; ce_s7 : word; ce_s8 : word; ce_s9 : word; ce_s10 : word; ce_s11 : word;
  ce_F : bvmap 5 word; ce_fc : bv 32;
  ce_cx : cctx; ce_lo : Z; ce_il : bool
}.
(* [comment removed for export] *)
Definition xFc (X : cbenv) (F : bvmap 5 word) (fc : bv 32) : cbenv :=
  CBE (ce_ra X) (ce_sp X) (ce_gp X) (ce_tp X) (ce_s0 X) (ce_s1 X) (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X)
      (ce_s10 X) (ce_s11 X) F fc (ce_cx X) (ce_lo X) (ce_il X).

(* [comment removed for export] *)
Record acenv := ACE {
  ac_P : Z;      (* [comment removed for export] *)
  ac_FB : Z;     (* [comment removed for export] *)
  ac_SHF : Z;    (* [comment removed for export] *)
  ac_SHE : Z     (* [comment removed for export] *)
}.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition il_w (b : bool) : word := Z_to_bv 64 (if b then 1 else 0).

(* [comment removed for export] *)
Definition cbenv_ok (X : cbenv) : Prop :=
  let usp := bv_unsigned (ce_sp X) in let cx := ce_cx X in
  cctx_ok cx /\ cctx_sep cx /\
  0x61e000 <= c_E cx /\ 0x61e000 <= c_A1 cx /\ 0x61e000 <= c_A2 cx /\ 0x61e000 <= c_FT cx /\
  CEILv <= ce_lo X /\ ce_lo X + 512 <= usp /\ usp < 18446744073709551616 /\ usp mod 16 = 0.

Definition acenv_ok (X : cbenv) (Y : acenv) : Prop :=
  let usp := bv_unsigned (ce_sp X) in
  ce_lo X + 32 <= ac_P Y /\ ac_P Y + 224 <= usp /\ usp <= ac_P Y + 240 /\
  0x61e000 <= ac_FB Y /\ ac_FB Y + 512 <= CEILv /\
  SH_LO <= ac_SHF Y /\ ac_SHF Y + 64 <= SH_HI.

(* [comment removed for export] *)
Definition acenv_sep (X : cbenv) (Y : acenv) : Prop :=
  let cx := ce_cx X in
  apartv (c_E cx) ESTATE_SIZE (ac_FB Y) 512 /\ apartv (c_A1 cx) ARR1_SIZE (ac_FB Y) 512 /\ apartv (c_A2 cx) ARR2_SIZE (ac_FB Y) 512.

(* [comment removed for export] *)
Definition acenv_offsh (X : cbenv) (Y : acenv) : Prop :=
  let cx := ce_cx X in
  (c_E cx + ESTATE_SIZE <= SH_LO \/ SH_HI <= c_E cx) /\ (c_A1 cx + ARR1_SIZE <= SH_LO \/ SH_HI <= c_A1 cx) /\
  (c_A2 cx + ARR2_SIZE <= SH_LO \/ SH_HI <= c_A2 cx) /\ (ac_FB Y + 512 <= SH_LO \/ SH_HI <= ac_FB Y).

(* [comment removed for export] *)
Definition CSAVED (X : cbenv) : list cell :=
  [C8 (ce_s11 X); C8 (ce_s10 X); C8 (ce_s9 X); C8 (ce_s8 X); C8 (ce_s7 X); C8 (ce_s6 X); C8 (ce_s5 X); C8 (ce_s4 X); C8 (ce_s3 X);
   C8 (ce_s2 X); C8 (ce_s1 X); C8 (ce_s0 X); C8 (ce_ra X)].

(* [comment removed for export] *)
Record cbsl := CBSL { k0 : word; k8 : word; k16 : word; k24 : word; k32 : word; k40 : word; k48 : word; k56 : word; k64 : word; k72 : word;
                      k80 : word; k88 : word; k96 : word; k104 : word; k112 : word }.
Definition cbsl_cells (s : cbsl) : list cell :=
  [C8 (k0 s); C8 (k8 s); C8 (k16 s); C8 (k24 s); C8 (k32 s); C8 (k40 s); C8 (k48 s); C8 (k56 s); C8 (k64 s); C8 (k72 s);
   C8 (k80 s); C8 (k88 s); C8 (k96 s); C8 (k104 s); C8 (k112 s)].

(* [comment removed for export] *)
Definition set8 (s : cbsl) (v : word) := CBSL (k0 s) v (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set16 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) v (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set24 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) v (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set32 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) v (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set40 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) v (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set48 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) v (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set56 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) v (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set64 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) v (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set72 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) v (k80 s) (k88 s) (k96 s) (k104 s) (k112 s).
Definition set80 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) v (k88 s) (k96 s) (k104 s) (k112 s).
Definition set88 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) v (k96 s) (k104 s) (k112 s).
Definition set112 (s : cbsl) (v : word) := CBSL (k0 s) (k8 s) (k16 s) (k24 s) (k32 s) (k40 s) (k48 s) (k56 s) (k64 s) (k72 s) (k80 s) (k88 s) (k96 s) (k104 s) v.

(* [comment removed for export] *)
Definition cf1b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))).
Definition cf3b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))).
Definition cf8b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8))).
(* [comment removed for export] *)
Definition yysh (b : byte) : list cell := Eval cbv [repeat] in repeat (C1 b) 32.
(* [comment removed for export] *)
Lemma yysh_bytes : forall b, cells_bytes (yysh b) = repeat b 32. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_cells_cutZ : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.
Lemma rw_cells_glue : forall segs m A l1 l2 B, rw_cells segs m A l1 -> rw_cells segs m B l2 -> B = (A + Z.of_nat (cells_size l1))%Z -> rw_cells segs m A (l1 ++ l2).
Proof. intros segs m A l1 l2 B H1 H2 ->. exact (proj2 (rw_cells_app_iff_c segs m A _ _) (conj H1 H2)). Qed.

End ACeilS1.

(* [comment removed for export] *)
Ltac cbenv_open XOK :=
  let H := fresh "XL" in
  pose proof XOK as H; unfold cbenv_ok, CEILv in H; cbv zeta in H;
  cps_destruct H as (?CX & ?SEP & ?XEi & ?XA1i & ?XA2i & ?XFTi & ?XLO & ?XST & ?XSP & ?ALS).
(* [comment removed for export] *)
Ltac sl_cbn := unfold cbsl_cells; cbn [set8 set16 set24 set32 set40 set48 set56 set64 set72 set80 set88 set112 k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112].
(* [comment removed for export] *)
Ltac cb_ranges CX :=
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ?LJ & _).
Ltac acenv_open YOK :=
  let H := fresh "YL" in
  pose proof YOK as H; unfold acenv_ok, CEILv, SH_LO, SH_HI in H; cbv zeta in H;
  cps_destruct H as (?YPl & ?YPh & ?YPa & ?YFl & ?YFh & ?YSl & ?YSh).
