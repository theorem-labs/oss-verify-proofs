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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0CBS.
  Variable X : cbenv. Variable Y : acenv. Variable Q : machine_state -> Prop.
  Notation cx := (ce_cx X).
  Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y).
  Notation E := (c_E cx).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WS := [(SHF + 4, SHF + 36)]%Z.

  Ltac sbz := wstep; change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store.
  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [cf8b]; mem_after_store.

  Lemma A0_cb_scope_begin : forall (m : word -> option byte)
      (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m (SHF + 4) (yysh cf8b) -> mem_inv a0segs m ->
    (forall m', rw_cells a0segs m' (SHF + 4) (yysh z8) -> mem_inv a0segs m' -> munch WS m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x8908c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8900c) fc None m (seg_rom a0segs)).
  Proof.
    intros m ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 SH MI K.
    pose proof (munch_refl WS m) as MU. pose proof (wmono_refl a0segs m) as WM.
    unfold yysh in SH.
    do 32 sbz.
    eapply K; [exact SH| exact MI| exact MU| exact WM].
  Qed.

  Lemma A0_cb_scope_end : forall (m : word -> option byte)
      (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m (SHF + 4) (yysh z8) -> mem_inv a0segs m ->
    (forall m', rw_cells a0segs m' (SHF + 4) (yysh cf8b) -> mem_inv a0segs m' -> munch WS m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x8968c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 E) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x8a3ac) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 E) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x89600) fc None m (seg_rom a0segs)).
  Proof.
    intros m ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 SH MI K.
    pose proof (munch_refl WS m) as MU. pose proof (wmono_refl a0segs m) as WM.
    unfold yysh in SH.
    wstep. do 32 sbf8. wstep. wstep.
    eapply K; [exact SH| exact MI| exact MU| exact WM].
  Qed.
End A0CBS.

End ACeilS1.
