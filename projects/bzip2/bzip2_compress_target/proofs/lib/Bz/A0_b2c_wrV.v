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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpCarve CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0_cmp_smV.
Local Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition DBZA : Z := 0x82450.   (* [comment removed for export] *)
Definition DBZF : Z := 0x82458.   (* [comment removed for export] *)
Definition A0_MALLOC : Z := 0x53d58.
Definition A0_FREE : Z := 0x53d54.

(* [comment removed for export] *)
Definition STRMS (ob on dbza dbzfr : Z) (z : zstrm) (nin : Z) (p1 p2 : word) (st : Z) : list cell :=
  [C8 (Z_to_bv 64 nin); C4 (Z_to_bv 64 (z_avail_in z)); C4 (Z_to_bv 64 (z_tin_lo z)); C4 (Z_to_bv 64 (z_tin_hi z)); C4 p1;
   C8 (Z_to_bv 64 (ob + (on - z_avail_out z))); C4 (Z_to_bv 64 (z_avail_out z));
   C4 (Z_to_bv 64 (z_tout_lo z)); C4 (Z_to_bv 64 (z_tout_hi z)); C4 p2;
   C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 dbza); C8 (Z_to_bv 64 dbzfr); C8 (Z_to_bv 64 0)].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ESAVED (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition STRMC (w0 w8 w12 w16 w20 w24 w32 w36 w40 w44 w48 w56 w64 w72 : word) : list cell :=
  [C8 w0; C4 w8; C4 w12; C4 w16; C4 w20; C8 w24; C4 w32; C4 w36; C4 w40; C4 w44; C8 w48; C8 w56; C8 w64; C8 w72].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ISLOTS (v0 v8 v16 v24 v32 : word) : list cell := [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32].

(* [comment removed for export] *)
Definition EJ1wA (J : list byte) (c0 c24 c32 c40 : word) : list cell :=
  [C8 c0; C4 (jw4 J 8); C4 (jw4 J 12); C4 (jw4 J 16); C4 (jw4 J 20); C8 c24; C8 c32; C8 c40; C4 (jw4 J 48); C4 (jw4 J 52);
   C8 (jw8 J 56); C8 (jw8 J 64); C8 (jw8 J 72); C8 (jw8 J 80); C4 (jw4 J 88); C4 (jw4 J 92); C4 (jw4 J 96); C4 (jw4 J 100);
   C4 (jw4 J 104); C4 (jw4 J 108); C4 (jw4 J 112); C4 (jw4 J 116); C4 (jw4 J 120); C4 (jw4 J 124)].
(* [comment removed for export] *)
Definition EJ2A (J : list byte) : list cell :=
  [C4 (jw4 J 640); C4 (jw4 J 644); C4 (jw4 J 648); C4 (jw4 J 652); C4 (jw4 J 656); C4 (jw4 J 660); C4 (jw4 J 664); C4 (jw4 J 668)].
(* [comment removed for export] *)
Definition EFINA (J : list byte) (STRM r1 r2 r3 : Z) : list cell :=
  [C8 (Z_to_bv 64 STRM); C4 (Z_to_bv 64 2); C4 (Z_to_bv 64 2); C4 (jw4 J 16); C4 (jw4 J 20);
   C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3); C4 (jw4 J 48); C4 (jw4 J 52);
   C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 WORKFACTOR); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 0); C4 (jw4 J 100); C4 (jw4 J 104);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 NBLOCKMAX); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (jw4 J 124)].
Definition EFIN2A (J : list byte) (bno : word) : list cell :=
  [C4 (jw4 J 640); C4 (jw4 J 644); C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 bno;
   C4 (Z_to_bv 64 BLOCKSIZE100K); C4 (jw4 J 668)].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition WSLOTS (v0 v8 v16 v24 v32 v40 v48 : word) : list cell := [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48].
(* [comment removed for export] *)
Definition b2c_shadow : list cell :=
  [C1 A0_cmp_smV.sf1b; C1 A0_cmp_smV.sf1b; C1 A0_cmp_smV.sf1b; C1 A0_cmp_smV.sf1b; C1 z8; C1 z8; C1 z8; C1 z8; C1 z8; C1 z8; C1 z8; C1 z8; C1 z8; C1 z8;
   C1 A0_cmp_smV.sf3b; C1 A0_cmp_smV.sf3b; C1 A0_cmp_smV.sf3b; C1 A0_cmp_smV.sf3b; C1 A0_cmp_smV.sf3b; C1 A0_cmp_smV.sf3b].
(* [comment removed for export] *)
Definition sf5b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-11))).
Definition b2c_sh_f5 : list cell := Eval cbv [repeat] in repeat (C1 sf5b) 32.

End ACeilS1.
