(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 ReadKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_read_a_xsrc_u5 Cut_read_b_xsrc_u5 Cut_read_c_xsrc_u5 Cut_read_d_xsrc_u5.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module RT.
Definition RD_R_NEXT : Z := 240524.    (* [comment removed for export] *)
Definition RN_R_PUSH : Z := 292120.    Definition LOOPA : Z := 291404.       Definition RN_R_CHUNKA : Z := 291436.  Definition RN_R_PSOME : Z := 291504.
Definition LOOPB : Z := 291620.        Definition RN_R_WS2 : Z := 291640.    Definition RN_R_CHUNKB : Z := 291664.  Definition RN_EPI : Z := 291700.
Definition LOOPC : Z := 291868.        Definition CD_R_CHUNK : Z := 291892.  Definition CD_R_PCD : Z := 291940.     Definition CD_C00 : Z := 291956.
Definition CD_EPI : Z := 292024.
Definition RD_RET : Z := 240548.       Definition RN_RET : Z := 291736.      Definition CD_RET : Z := 292044.
End RT.

Module RS.
Module GA := Cut_read_a_xsrc_u5.  Module GB := Cut_read_b_xsrc_u5.  Module GC := Cut_read_c_xsrc_u5.  Module GD := Cut_read_d_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
(* [comment removed for export] *)
Definition KSA : list nat := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
(* [comment removed for export] *)
Definition KSW : list nat := [3; 4; 8; 9; 18; 20; 21; 23; 24; 25; 26; 27]%nat.
Definition spok (sp0 : Z) : Prop := ((@Corelib.Init.Logic.and (@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.pow (@Corelib.Numbers.BinNums.Zpos 2%positive) (@Corelib.Numbers.BinNums.Zpos 40%positive)) sp0) (@Stdlib.ZArith.BinInt.Z.le sp0 (@Stdlib.ZArith.BinInt.Z.pow (@Corelib.Numbers.BinNums.Zpos 2%positive) (@Corelib.Numbers.BinNums.Zpos 47%positive)))) (@Corelib.Init.Logic.eq Corelib.Numbers.BinNums.Z (@Stdlib.ZArith.BinInt.Z.modulo sp0 (@Corelib.Numbers.BinNums.Zpos 16%positive)) Corelib.Numbers.BinNums.Z0))).
Definition pok (p : Z) : Prop := ((@Corelib.Init.Logic.and (@Stdlib.ZArith.BinInt.Z.le (@Stdlib.ZArith.BinInt.Z.pow (@Corelib.Numbers.BinNums.Zpos 2%positive) (@Corelib.Numbers.BinNums.Zpos 12%positive)) p) (@Stdlib.ZArith.BinInt.Z.le p (@Stdlib.ZArith.BinInt.Z.pow (@Corelib.Numbers.BinNums.Zpos 2%positive) (@Corelib.Numbers.BinNums.Zpos 47%positive))))).

(* [comment removed for export] *)
Definition r_ra : reg := 1%bv.   Definition r_sp : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 2%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 2%positive))))).   Definition r_s0 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive))))).   Definition r_s1 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive))))).
Definition r_a0 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 10%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 10%positive))))).  Definition r_a1 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 11%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 11%positive))))).  Definition r_a2 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 12%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 12%positive))))).  Definition r_s2 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive))))).
Definition r_s3 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 19%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 19%positive))))).  Definition r_s4 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 20%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 20%positive))))).  Definition r_s5 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 21%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 21%positive))))).  Definition r_s6 : reg := ((@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 22%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 22%positive))))).
Ltac rr x := eval cbv delta [r_ra r_sp r_s0 r_s1 r_a0 r_a1 r_a2 r_s2 r_s3 r_s4 r_s5 r_s6] in x.

(* [comment removed for export] *)
Definition rn_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop :=
  L5.u64_at RSEGS M (sp1 - 8) rav /\ L5.u64_at RSEGS M (sp1 - 16) (bv_unsigned (getr R0 8%bv)) /\ L5.u64_at RSEGS M (sp1 - 24) (bv_unsigned (getr R0 9%bv)) /\
  L5.u64_at RSEGS M (sp1 - 32) (bv_unsigned (getr R0 18%bv)) /\ L5.u64_at RSEGS M (sp1 - 40) (bv_unsigned (getr R0 19%bv)) /\ L5.u64_at RSEGS M (sp1 - 48) (bv_unsigned (getr R0 20%bv)) /\
  L5.u64_at RSEGS M (sp1 - 56) (bv_unsigned (getr R0 21%bv)) /\ L5.u64_at RSEGS M (sp1 - 64) (bv_unsigned (getr R0 22%bv)).
Definition cd_frame (M : mem) (sp1 rav : Z) (R0 : bvmap 5 word) : Prop := ((@Corelib.Init.Logic.and (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.L5Defs.L5.u64_at OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.loaded_segments M (@Stdlib.ZArith.BinInt.Z.sub sp1 (@Corelib.Numbers.BinNums.Zpos 8%positive)) rav) (@Corelib.Init.Logic.and (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.L5Defs.L5.u64_at OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.loaded_segments M (@Stdlib.ZArith.BinInt.Z.sub sp1 (@Corelib.Numbers.BinNums.Zpos 16%positive)) (@stdpp.bitvector.definitions.bv_unsigned (@Corelib.Numbers.BinNums.Npos 64%positive) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive))))))) (@Corelib.Init.Logic.and (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.L5Defs.L5.u64_at OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.loaded_segments M (@Stdlib.ZArith.BinInt.Z.sub sp1 (@Corelib.Numbers.BinNums.Zpos 24%positive)) (@stdpp.bitvector.definitions.bv_unsigned (@Corelib.Numbers.BinNums.Npos 64%positive) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive))))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.L5Defs.L5.u64_at OssFuzzTheorems.jsoncons.fuzz_json_encoder.images.Ubsan.M.loaded_segments M (@Stdlib.ZArith.BinInt.Z.sub sp1 (@Corelib.Numbers.BinNums.Zpos 32%positive)) (@stdpp.bitvector.definitions.bv_unsigned (@Corelib.Numbers.BinNums.Npos 64%positive) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive))))))))))).

Definition same_s06 (R0 R' : bvmap 5 word) : Prop := ((@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive)))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive)))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive)))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 19%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 19%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 19%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 19%positive)))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 20%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 20%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 20%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 20%positive)))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 21%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 21%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 21%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 21%positive)))))) (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 22%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 22%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 22%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 22%positive))))))))))))).
Definition same_s02 (R0 R' : bvmap 5 word) : Prop := ((@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 8%positive)))))) (@Corelib.Init.Logic.and (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 9%positive)))))) (@Corelib.Init.Logic.eq (@stdpp.bitvector.definitions.bv (@Corelib.Numbers.BinNums.Npos 64%positive)) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R' (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive))))) (@OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PropExec.getr R0 (@stdpp.bitvector.definitions.BV (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive) (@Corelib.Init.Logic.I <: (@stdpp.bitvector.definitions.BvWf (@Corelib.Numbers.BinNums.Npos 5%positive) (@Corelib.Numbers.BinNums.Zpos 18%positive))))))))).

Section S.
Context {SCFG_P : ScfgP}.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Ltac hv_open cp plans off gl pn sp0 R M fx model K Hh Hl Hfp H2 Hpins :=
  let E := fresh "E" in set (E := TK.hvE sp0 R (RK.ghl gl));
  assert (U2 : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (RK.regs_ok_hv _ off pn); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins] | | ].
Ltac no_pins := let q := fresh in let z := fresh in intros q z [].
(* [comment removed for export] *)
Ltac reg_atom E sp0 R v r Hr := let U := fresh "Ur" in
  lazymatch type of Hr with getr _ _ = Z_to_bv 64 ?z =>
    assert (U : bv_unsigned (ev E v) = z) by (change v with (32 + ridx (r : reg))%nat; subst E; apply (RK.hv_reg_u sp0 R _ r z Hr); lia) end.
Ltac gh_atom E sp0 R v k z := let U := fresh "Ug" in
  assert (U : bv_unsigned (ev E v) = z) by (change v with (64 + k)%nat; subst E; eapply RK.ghl_u; [reflexivity | lia]).
(* [comment removed for export] *)
Ltac leaf_open Hag HLF E' nxv :=
  assert (Hag64 : env_agree 64 _ E') by (eapply CC.env_agree_le; [exact Hag | vm_compute; lia]);
  repeat match goal with U : bv_unsigned (ev ?E ?v) = ?z |- _ =>
           lazymatch E with E' => fail | _ => let U' := fresh "V" in assert (U' : bv_unsigned (ev E' v) = z) by (rewrite <- (proj1 Hag v) by (vm_compute; lia); exact U); clear U end end.


Ltac leaf_k k Hnth := destruct k as [|k]; [injection Hnth as <- | ].
Ltac leaf_end k Hnth := destruct k; discriminate Hnth.
Ltac leaves n k Hnth tac := lazymatch n with O => leaf_end k Hnth | S ?m => destruct k as [|k]; [injection Hnth as <-; tac | leaves m k Hnth tac] end.
Ltac probes_in HLF PF := pose proof (RK.leaf_probes _ _ _ _ _ _ HLF) as PF; vm_compute RK.probes in PF; cbn [RK.pfacts edenot] in PF.
Ltac w2z H := repeat match type of H with context [ev ?E ?v] => match goal with U : bv_unsigned (ev E v) = ?z |- _ => rewrite (RK.w_of_u _ _ U) in H end end.
Ltac hv_keeps HLF Hag64 sp0 R E' R' M M' qs := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; exact (TK.keeps_hv_sound _ _ sp0 R _ E' R' M M' qs r HLF eq_refl Hag64 Hr).

(* [comment removed for export] *)
Definition s_loopA_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr vis p e fl,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> pok Rr -> L5.u64_at RSEGS M (Rr + 312) vis -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p ->
  0 <= vis < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> pok vis -> vis mod 8 = 0 -> getr R 10%bv = Z_to_bv 64 fl -> 0 <= fl < 2 ^ 64 ->
  (Z.land fl 1 = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.LOOPB ->
      getr R' 10%bv = getr R 18%bv -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_WS M model) K) ->
  (Z.land fl 1 <> 0 -> p = e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_CHUNKA ->
      getr R' 10%bv = Z_to_bv 64 Rr -> getr R' 11%bv = getr R 8%bv -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READ_CHUNK M model) K) ->
  (Z.land fl 1 <> 0 -> p <> e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_PSOME ->
      getr R' 10%bv = getr R 18%bv -> getr R' 11%bv = Z_to_bv 64 vis -> getr R' 12%bv = getr R 8%bv -> getr R' 21%bv = Z_to_bv 64 e -> getr R' 22%bv = Z_to_bv 64 p ->
      TK.keepsR [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSE_SOME M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPA M model) K.


(* [comment removed for export] *)
Ltac llin HLF x := let x' := rr x in tk_lin HLF x'.
Ltac lreg HLF x := let x' := rr x in tk_reg HLF x'.
Ltac lkeep HLF Hag64 sp0 R x v r := let x' := rr x in let r' := rr r in tk_reg HLF x'; rewrite <- (proj1 Hag64 v) by lia; exact (TK.hvE_reg sp0 R _ r').
Ltac lcell64 HLF b off v := eapply (CL5.kword64_elim RSEGS); [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA b off) 8 v)); cbn; tauto | ev_start | ].
Ltac lcell32 HLF b off v := eapply TK.kword32_elim; [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA b off) 4 v)); cbn; tauto | ev_start | ].
Ltac lcell8 HLF b off v := eapply RK.kword8_elim; [apply (CC.lf_cells _ _ _ _ _ _ _ HLF (KWord (SA b off) 1 v)); cbn; tauto | ev_start | ].
Ltac vlit := cbn [edenot]; apply u64_of_Z; lia.
Ltac vreg Hag64 sp0 R v r := let r' := rr r in cbn [edenot]; rewrite <- (proj1 Hag64 v) by lia; f_equal; exact (TK.hvE_reg sp0 R _ r').
Ltac vlin := apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?u64_of_Z by lia; lia | lia].
Ltac kw64 A0 z0 H := eapply CL5.kword64_intro with (A := A0) (z := z0); [ev_start | lia | lia | reflexivity | exact H].
Ltac kw32 A0 z0 H := eapply RK.kword32_intro with (A := A0) (z := z0); [ev_start | lia | lia | reflexivity | exact H].
Ltac kw8 A0 z0 H := eapply TK.kword8_intro with (A := A0) (z := z0); [ev_start | lia | lia | reflexivity | lia | exact H].
Ltac lframe HLF := apply (TK.frame_samem _ _ _ _ _ _ _ HLF); let a := fresh "a" in let Ha := fresh "Ha" in let Hk := fresh "Hk" in intros a Ha Hk; cbn [CC.cp_F]; tk_outside.
(* [comment removed for export] *)
Ltac lsame HLF M M' A0 e p D Ce Cp b ve vp :=
  assert (SAME : M' = M);
  [ eapply (RK.same_mem16 M M' A0 e p); [lia | lia | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact D | exact Ce | | replace (A0 + 8) with (A0 - 512 + 520) by lia; ring_simplify (A0 - 512 + 520); exact Cp | ];
    [ lcell64 HLF b 512 ve; cbn [edenot]; assumption | replace (A0 + 8) with (A0 - 512 + 520) by lia; ring_simplify (A0 - 512 + 520); lcell64 HLF b 520 vp; cbn [edenot]; assumption ] | ].

Definition ret_rd_stmt : Prop := CL.is_ret_at RSEGS RT.RD_RET.
Definition ret_rn_stmt : Prop := CL.is_ret_at RSEGS RT.RN_RET.
Definition ret_cd_stmt : Prop := CL.is_ret_at RSEGS RT.CD_RET.

(* [comment removed for export] *)
Definition KS01 : list nat := [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition KS012 : list nat := ((@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 3%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 4%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 19%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 20%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 21%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 22%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 23%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 24%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 25%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 26%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 27%nat (@Corelib.Init.Datatypes.nil Corelib.Init.Datatypes.nat))))))))))))).
Definition KS06 : list nat := ((@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 3%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 4%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 23%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 24%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 25%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 26%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 27%nat (@Corelib.Init.Datatypes.nil Corelib.Init.Datatypes.nat))))))))).
Definition KS45 : list nat := ((@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 3%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 4%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 8%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 9%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 18%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 19%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 22%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 23%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 24%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 25%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 26%nat (@Corelib.Init.Datatypes.cons Corelib.Init.Datatypes.nat 27%nat (@Corelib.Init.Datatypes.nil Corelib.Init.Datatypes.nat)))))))))))))).

(* [comment removed for export] *)
Definition s_rd_entry_stmt : Prop := forall (fx : FPState) R M model K sp1 rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 sp1 -> spok sp1 ->
  getr R 1%bv = Z_to_bv 64 rav -> 0 <= rav < 2 ^ 64 -> L5.defined M (sp1 - 32) 32 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 RT.RD_R_NEXT ->
      getr R' 10%bv = getr R 10%bv -> getr R' 11%bv = getr R 11%bv -> getr R' 8%bv = getr R 11%bv -> getr R' 9%bv = getr R 10%bv -> TK.keepsR KS01 R R' ->
      L5.u64_at RSEGS M' (sp1 - 8) rav -> L5.u64_at RSEGS M' (sp1 - 16) (bv_unsigned (getr R 8%bv)) -> L5.u64_at RSEGS M' (sp1 - 24) (bv_unsigned (getr R 9%bv)) ->
      TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READ_NEXT M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_READ M model) K.


(* [comment removed for export] *)
Definition s_rd_r_next_stmt : Prop := forall (fx : FPState) R M model K sp1 Ev rav s0v s1v code,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> spok sp1 ->
  getr R 8%bv = Z_to_bv 64 Ev -> pok Ev -> L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 ->
  L5.u64_at RSEGS M (sp1 - 8) rav -> L5.u64_at RSEGS M (sp1 - 16) s0v -> L5.u64_at RSEGS M (sp1 - 24) s1v -> L5.ra_ok rav -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 ->
  (code = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = Z_to_bv 64 rav ->
      getr R' 10%bv = getr R 9%bv -> getr R' 11%bv = Z_to_bv 64 Ev -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v -> TK.keepsR KS01 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_RCHECK_DONE M model) K) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 8%bv = Z_to_bv 64 s0v -> getr R' 9%bv = Z_to_bv 64 s1v -> TK.keepsR KS01 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RD_R_NEXT M model) K.

(* [comment removed for export] *)
Definition s_loopB_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr IS rdb,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> pok Rr -> pok IS -> IS mod 8 = 0 -> PML.img_ro M ->
  L5.u64_at RSEGS M (Rr + 288) 0 -> L5.u64_at RSEGS M (Rr + 240) IS -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u8_at RSEGS M (IS + 152) rdb -> 0 <= rdb <= 255 ->
  (Z.land rdb 2 = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_WS2 ->
      getr R' 10%bv = getr R 18%bv -> TK.keepsR KSA R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_WS M model) K) ->
  (Z.land rdb 2 <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPB M model) K.

(* [comment removed for export] *)
Definition s_loopC_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr e p,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> pok Rr -> Rr mod 8 = 0 -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= e < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
  (p = e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 RT.CD_R_CHUNK ->
      getr R' 10%bv = getr R 9%bv -> getr R' 11%bv = getr R 8%bv -> TK.keepsR KSA R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READ_CHUNK M model) K) ->
  (p <> e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 RT.CD_R_PCD ->
      getr R' 10%bv = getr R 18%bv -> getr R' 11%bv = getr R 8%bv -> TK.keepsR KSA R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PCHECK_DONE M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.LOOPC M model) K.


(* [comment removed for export] *)
Definition s_rn_entry_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr IS rdb sb eb rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 sp1 -> spok sp1 ->
  getr R 10%bv = Z_to_bv 64 Rr -> getr R 1%bv = Z_to_bv 64 rav -> 0 <= rav < 2 ^ 64 -> pok Rr -> pok IS -> IS mod 8 = 0 -> PML.img_ro M ->
  L5.u64_at RSEGS M (Rr + 240) IS -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u8_at RSEGS M (IS + 152) rdb -> 0 <= rdb <= 255 -> Z.land rdb 1 = 0 ->
  L5.u64_at RSEGS M (Rr + 568) sb -> 0 <= sb < 2 ^ 64 -> L5.u64_at RSEGS M (Rr + 576) eb -> (eb = sb \/ (pok sb /\ sb < eb /\ eb <= sb + 2 ^ 47)) ->
  L5.defined M (sp1 - 96) 96 -> L5.defined M (Rr + 576) 8 ->
  sp1 <= Rr -> sp1 <= IS -> (Rr + 584 <= IS \/ IS + 272 <= Rr + 576) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 96) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_PUSH ->
      getr R' 10%bv = Z_to_bv 64 (Rr + 568) -> getr R' 11%bv = Z_to_bv 64 (sp1 - 81) ->
      getr R' 8%bv = Z_to_bv 64 (Rr + 320) -> getr R' 9%bv = Z_to_bv 64 Rr -> getr R' 18%bv = Z_to_bv 64 (Rr + 320) -> TK.keepsR KS012 R R' ->
      rn_frame M' sp1 rav R -> L5.u64_at RSEGS M' (sp1 - 72) 0x4723c -> L5.u64_at RSEGS M' (sp1 - 80) (bv_unsigned (getr R 11%bv)) ->
      L5.u8_at RSEGS M' (sp1 - 81) 0 -> L5.u64_at RSEGS M' (Rr + 576) sb ->
      TK.samem (fun a => ~ (sp1 - 96 <= a < sp1) /\ ~ (Rr + 576 <= a < Rr + 584)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_VEC_PUSH M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_READ_NEXT M model) K.


(* [comment removed for export] *)
Definition s_rn_r_push_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr Ev fl,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 96) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 (Rr + 320) -> pok Rr -> sp1 <= Rr -> L5.defined M (Rr + 464) 69 ->
  L5.u8_at RSEGS M (Rr + 531) fl -> 0 <= fl <= 1 -> L5.u64_at RSEGS M (sp1 - 72) 0x4723c -> L5.u64_at RSEGS M (sp1 - 80) Ev -> 0 <= Ev < 2 ^ 64 ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 8%bv = Z_to_bv 64 Ev -> getr R' 10%bv = Z_to_bv 64 1 ->
      getr R' 19%bv = Z_to_bv 64 1 -> getr R' 20%bv = Z_to_bv 64 2 -> TK.keepsR [3; 4; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat R R' ->
      L5.u8_at RSEGS M' (Rr + 528) 1 -> L5.u8_at RSEGS M' (Rr + 531) 1 -> L5.u8_at RSEGS M' (Rr + 532) 0 -> L5.u32_at RSEGS M' (Rr + 464) 0 ->
      L5.u64_at RSEGS M' (Rr + 480) 1 -> L5.u64_at RSEGS M' (Rr + 488) 0 -> L5.u64_at RSEGS M' (Rr + 496) 0 ->
      TK.samem (fun a => ~ (Rr + 464 <= a < Rr + 468) /\ ~ (Rr + 480 <= a < Rr + 504) /\ ~ (Rr + 528 <= a < Rr + 529) /\ ~ (Rr + 531 <= a < Rr + 533)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPA M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_PUSH M model) K.

(* [comment removed for export] *)
Definition s_rn_r_chunkA_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr Ev code vis p e p' k,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 k -> 0 <= p' -> 0 <= k -> p' + k < 2 ^ 64 -> (0 < k -> pok p' /\ p' + k <= 2 ^ 47) ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u64_at RSEGS M (Rr + 312) vis -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p ->
  0 <= vis < 2 ^ 64 -> pok vis -> vis mod 8 = 0 -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> L5.defined M (Rr + 512) 16 -> (Rr + 592 <= Ev \/ Ev + 16 <= Rr) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR KSW R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) ->
  (code = 0 -> forall (fx' : FPState) R' M' pn en, PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_PSOME ->
      getr R' 10%bv = getr R 18%bv -> getr R' 11%bv = Z_to_bv 64 vis -> getr R' 12%bv = Z_to_bv 64 Ev -> getr R' 22%bv = Z_to_bv 64 pn -> getr R' 21%bv = Z_to_bv 64 en ->
      TK.keepsR [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat R R' ->
      ((k = 0 /\ pn = p /\ en = e /\ M' = M) \/
       (k <> 0 /\ pn = p' /\ en = p' + k /\ L5.u64_at RSEGS M' (Rr + 512) en /\ L5.u64_at RSEGS M' (Rr + 520) pn /\ TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M M' /\ mem_grows M M')) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSE_SOME M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_CHUNKA M model) K.


(* [comment removed for export] *)
Ltac pf_z H := w2z H; rewrite ?RK.ext_s32, ?RK.ext_u8 in H by lia; rewrite ?RK.and_lit in H by lia;
  first [apply RK.w_inj in H; [| first [lia | apply RK.land_range; lia] | first [lia | apply RK.land_range; lia]] | apply RK.w_neq in H].
Ltac pf_all PF := repeat (let X := fresh "PFx" in destruct PF as [X PF]; pf_z X); clear PF.
Ltac pins45 H20 H21 := let q := fresh in let z := fresh in let X := fresh in intros q z [X|[X|[]]]; injection X as <- <-; [exact H20 | exact H21].

(* [comment removed for export] *)
Definition s_rn_r_psome_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr Ev code st dn mo p e rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 19%bv = Z_to_bv 64 1 -> getr R 20%bv = Z_to_bv 64 2 ->
  getr R 22%bv = Z_to_bv 64 p -> getr R 21%bv = Z_to_bv 64 e -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u8_at RSEGS M (Rr + 528) st -> L5.u8_at RSEGS M (Rr + 532) dn -> L5.u8_at RSEGS M (Rr + 531) mo ->
  0 <= st <= 255 -> 0 <= dn <= 1 -> 0 <= mo <= 1 -> rn_frame M sp1 rav R0 -> 0 <= rav < 2 ^ 64 ->
  (code = 0 -> p = e -> st = 1 ->
      forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.LOOPB -> getr R' 10%bv = getr R 18%bv ->
      getr R' 19%bv = Z_to_bv 64 1 -> getr R' 20%bv = Z_to_bv 64 2 -> TK.keepsR [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SKIP_WS M model) K) ->
  (code = 0 -> (p = e -> st <> 1 /\ (st = 2 \/ dn <> 0)) -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 10%bv = Z_to_bv 64 mo ->
      getr R' 19%bv = Z_to_bv 64 1 -> getr R' 20%bv = Z_to_bv 64 2 -> TK.keepsR [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPA M model) K) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) ->
  (code = 0 -> p = e -> st <> 1 -> st <> 2 -> dn = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = Z_to_bv 64 rav ->
      getr R' 10%bv = Z_to_bv 64 Ev -> getr R' 11%bv = Z_to_bv 64 1 -> TK.keepsR [8; 9; 18; 19; 20; 21; 22]%nat R0 R' -> TK.keepsR [3; 4; 23; 24; 25; 26; 27]%nat R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_SET_EC M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_PSOME M model) K.


(* [comment removed for export] *)
Definition s_rn_r_ws2_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr p e,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> pok Rr -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  (p = e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_CHUNKB ->
      getr R' 10%bv = Z_to_bv 64 Rr -> getr R' 11%bv = getr R 8%bv -> TK.keepsR KSA R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_READ_CHUNK M model) K) ->
  (p <> e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_WS2 M model) K.

(* [comment removed for export] *)
Definition s_rn_r_chunkB_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr Ev code p e p' k,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 k -> 0 <= p' -> 0 <= k -> p' + k < 2 ^ 64 -> (0 < k -> pok p' /\ p' + k <= 2 ^ 47) ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.defined M (Rr + 512) 16 -> (Rr + 592 <= Ev \/ Ev + 16 <= Rr) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.RN_EPI M model) K) ->
  (code = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR KSA R R' ->
      ((k = 0 /\ M' = M) \/
       (k <> 0 /\ L5.u64_at RSEGS M' (Rr + 512) (p' + k) /\ L5.u64_at RSEGS M' (Rr + 520) p' /\ TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M M' /\ mem_grows M M')) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPB M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_R_CHUNKB M model) K.


(* [comment removed for export] *)
Definition s_cd_entry_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr IS rd p e rav,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 sp1 -> spok sp1 ->
  getr R 10%bv = Z_to_bv 64 Rr -> getr R 1%bv = Z_to_bv 64 rav -> 0 <= rav < 2 ^ 64 -> pok Rr -> pok IS -> PML.img_ro M ->
  L5.u64_at RSEGS M (Rr + 240) IS -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u32_at RSEGS M (IS + 152) rd -> 0 <= rd <= 255 -> Z.land rd 1 = 0 ->
  L5.u64_at RSEGS M (Rr + 288) 0 -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.defined M (sp1 - 32) 32 -> sp1 <= Rr -> sp1 <= IS -> IS mod 8 = 0 ->
  (Z.land rd 2 <> 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> getr R' 1%bv = Z_to_bv 64 rav ->
      getr R' 10%bv = Z_to_bv 64 (Rr + 320) -> getr R' 11%bv = getr R 11%bv -> TK.keepsR KSA R R' ->
      TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PCHECK_DONE M' model) K) ->
  (Z.land rd 2 = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) ->
      getr R' 9%bv = Z_to_bv 64 Rr -> getr R' 8%bv = getr R 11%bv -> getr R' 18%bv = Z_to_bv 64 (Rr + 320) -> TK.keepsR KS012 R R' ->
      cd_frame M' sp1 rav R -> TK.samem (fun a => ~ (sp1 - 32 <= a < sp1)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPC M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R PML.PC_RCHECK_DONE M model) K.

(* [comment removed for export] *)
Definition s_cd_r_chunk_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr Ev code p e p' k,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 k -> 0 <= p' -> 0 <= k -> p' + k < 2 ^ 64 -> (k <> 0 -> pok p' /\ k <= 2 ^ 47) ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.defined M (Rr + 512) 16 -> (Rr + 592 <= Ev \/ Ev + 16 <= Rr) ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.CD_EPI M model) K) ->
  (code = 0 -> k = 0 -> p = e -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 10%bv = Z_to_bv 64 e -> getr R' 11%bv = Z_to_bv 64 e -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.CD_C00 M model) K) ->
  (code = 0 -> forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 1%bv = Z_to_bv 64 RT.CD_R_PCD ->
      getr R' 10%bv = getr R 18%bv -> getr R' 11%bv = Z_to_bv 64 Ev -> TK.keepsR KSA R R' ->
      ((k = 0 /\ p <> e /\ M' = M) \/
       (k <> 0 /\ L5.u64_at RSEGS M' (Rr + 512) (p' + k) /\ L5.u64_at RSEGS M' (Rr + 520) p' /\ TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M M' /\ mem_grows M M')) ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PCHECK_DONE M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.CD_R_CHUNK M model) K.


(* [comment removed for export] *)
Definition s_cd_r_pcd_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr Ev code p e,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev ->
  L5.u32_at RSEGS M Ev code -> 0 <= code < 2 ^ 31 -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  (code <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.CD_EPI M model) K) ->
  (code = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> getr R' 10%bv = Z_to_bv 64 e -> getr R' 11%bv = Z_to_bv 64 p -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.CD_C00 M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.CD_R_PCD M model) K.

(* [comment removed for export] *)
Definition s_cd_c00_stmt : Prop := forall (fx : FPState) R M model K sp1 Rr IS rdb a0v a1v,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> pok Rr -> pok IS -> PML.img_ro M -> getr R 10%bv = Z_to_bv 64 a0v -> getr R 11%bv = Z_to_bv 64 a1v -> 0 <= a0v < 2 ^ 64 -> 0 <= a1v < 2 ^ 64 ->
  L5.u64_at RSEGS M (Rr + 288) 0 -> L5.u64_at RSEGS M (Rr + 240) IS -> L5.u64_at RSEGS M IS PML.VT_ISS -> L5.u8_at RSEGS M (IS + 152) rdb -> 0 <= rdb <= 255 -> IS mod 8 = 0 ->
  (a0v <> a1v \/ Z.land rdb 2 = 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPC M model) K) ->
  (a0v = a1v -> Z.land rdb 2 <> 0 -> forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 32) -> TK.keepsR KSA R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.CD_EPI M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.CD_C00 M model) K.

(* [comment removed for export] *)
Definition s_rn_epi_stmt : Prop := forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 -> rn_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 ->
      same_s06 R0 R' -> TK.keepsR KS06 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.RN_EPI M model) K.


(* [comment removed for export] *)
Definition s_cd_epi_stmt : Prop := forall (fx : FPState) R M model K sp1 rav R0,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 32) -> spok sp1 -> cd_frame M sp1 rav R0 -> L5.ra_ok rav ->
  (forall (fx' : FPState) R', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 sp1 -> same_s02 R0 R' -> TK.keepsR KS012 R R' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' rav M model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R RT.CD_EPI M model) K.

Lemma ret_rd : ret_rd_stmt.
Proof.
  unfold ret_rd_stmt. CL.solve_is_ret. Qed.

Lemma ret_rn : ret_rn_stmt.
Proof.
  unfold ret_rn_stmt. CL.solve_is_ret. Qed.

Lemma ret_cd : ret_cd_stmt.
Proof.
  unfold ret_cd_stmt. CL.solve_is_ret. Qed.

Lemma s_rd_entry : s_rd_entry_stmt.
Proof.
  unfold s_rd_entry_stmt.
  intros fx R M model K sp1 rav Hh Hl Hfp H2 [Hsp Hal] H1 Rra D Kc.
  change PML.PC_READ with (CC.cp_pc GB.cp0).
  hv_open GB.cp0 (GB.plans 0%nat _ eq_refl) 0 (@nil Z) (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 33%nat r_ra H1.
    leaf_open Hag HLF E' 64%nat.
    leaves 1%nat k Hnth idtac.
    apply (Kc fx' R' M' Hfp');
      [llin HLF r_sp | unfold RT.RD_R_NEXT; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 42%nat r_a0 | lkeep HLF Hag64 sp1 R r_a1 43%nat r_a1
      | lkeep HLF Hag64 sp1 R r_s0 43%nat r_a1 | lkeep HLF Hag64 sp1 R r_s1 42%nat r_a0 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS01
      | lcell64 HLF (EVar 2) (-8) (EVar 33); cbn [edenot]; assumption
      | lcell64 HLF (EVar 2) (-16) (EVar 40); cbn [edenot]; rewrite <- (proj1 Hag64 40%nat) by lia; exact (f_equal (@bv_unsigned 64) (TK.hvE_reg sp1 R _ r_s0))
      | lcell64 HLF (EVar 2) (-24) (EVar 41); cbn [edenot]; rewrite <- (proj1 Hag64 41%nat) by lia; exact (f_equal (@bv_unsigned 64) (TK.hvE_reg sp1 R _ r_s1))
      | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_rd_r_next : s_rd_r_next_stmt.
Proof.
  unfold s_rd_r_next_stmt.
  intros fx R M model K sp1 Ev rav s0v s1v code Hh Hl Hfp H2 [Hsp Hal] H8 [He1 He2] Cc Rc Cra Cs0 Cs1 [Hra1 Hra2] Rs0 Rs1 K0 K1.
  change RT.RD_R_NEXT with (CC.cp_pc GB.cp1).
  hv_open GB.cp1 (GB.plans 1%nat _ eq_refl) (-32) [rav; s0v; s1v; code] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 40%nat r_s0 H8. gh_atom E sp1 R 64%nat 0%nat rav. gh_atom E sp1 R 65%nat 1%nat s0v. gh_atom E sp1 R 66%nat 2%nat s1v. gh_atom E sp1 R 67%nat 3%nat code.
    unfold know_ok, GB.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + kw64 (sp1 - 8) rav Cra. + kw64 (sp1 - 16) s0v Cs0. + kw64 (sp1 - 24) s1v Cs1. + e_range. + kw32 Ev code Cc.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 40%nat r_s0 H8. gh_atom E sp1 R 64%nat 0%nat rav. gh_atom E sp1 R 65%nat 1%nat s0v. gh_atom E sp1 R 66%nat 2%nat s1v. gh_atom E sp1 R 67%nat 3%nat code.
    leaf_open Hag HLF E' 68%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 2%nat k Hnth ltac:(probes_in HLF PF; pf_all PF).
    + apply (K0 ltac:(lia) fx' R' Hfp');
        [llin HLF r_sp | llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 41%nat r_s1 | llin HLF r_a1 | llin HLF r_s0 | llin HLF r_s1 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS01].
    + assert (Ra : getr R' 1%bv = Z_to_bv 64 rav) by llin HLF r_ra.
      unfold PML.cfg. eapply (CL.ret_cps RSEGS); [exact ret_rd | exact Hh | exact Hl | rewrite Ra; apply Hoare.ret_ok_even; rewrite u64_of_Z by lia; exact Hra2 | ].
      rewrite Ra. apply (K1 ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | llin HLF r_s0 | llin HLF r_s1 | hv_keeps HLF Hag64 sp1 R E' R' M M' KS01].
Qed.

Lemma s_loopA : s_loopA_stmt.
Proof.
  unfold s_loopA_stmt.
  intros fx R M model K sp1 Rr vis p e fl Hh Hl Hfp H2 [Hsp Hal] H9 [Hr1 Hr2] Cvis Ce Cp Rvis Rp Re [Hv1 Hv2] Hval H10 Rfl Kws Kchunk Kps.
  change RT.LOOPA with (CC.cp_pc GB.cp2).
  hv_open GB.cp2 (GB.plans 2%nat _ eq_refl) (-64) [vis; e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat vis. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p.
    unfold know_ok, GB.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + kw64 (Rr + 312) vis Cvis. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp. + e_range. + e_align Hval.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 42%nat r_a0 H10. gh_atom E sp1 R 64%nat 0%nat vis. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p.
    leaf_open Hag HLF E' 67%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 3%nat k Hnth ltac:(probes_in HLF PF; pf_all PF).
    + apply (Kws ltac:(lia) fx' R' Hfp');
        [llin HLF r_sp | unfold RT.LOOPB; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
    + apply (Kchunk ltac:(lia) ltac:(lia) fx' R' Hfp');
        [llin HLF r_sp | unfold RT.RN_R_CHUNKA; llin HLF r_ra | llin HLF r_a0 | lkeep HLF Hag64 sp1 R r_a1 40%nat r_s0 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
    + apply (Kps ltac:(lia) ltac:(lia) fx' R' Hfp');
        [llin HLF r_sp | unfold RT.RN_R_PSOME; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | llin HLF r_a1 | lkeep HLF Hag64 sp1 R r_a2 40%nat r_s0
        | llin HLF r_s5 | llin HLF r_s6 | hv_keeps HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat].
Qed.

Lemma bit1_eq : forall rdb, 0 <= rdb <= 255 ->
  (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 (2 ^ 62)) (Z_to_bv 64 rdb)) (Z_to_bv 64 63) = Z_to_bv 64 0 <-> Z.land rdb 2 = 0).
Proof.
  assert (C : forallb (fun n => Bool.eqb (Z.eqb (bv_unsigned (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 (2 ^ 62)) (Z_to_bv 64 (Z.of_nat n))) (Z_to_bv 64 63))) 0)
                                      (Z.eqb (Z.land (Z.of_nat n) 2) 0)) (seq 0 256) = true) by (vm_compute; reflexivity).
  intros rdb Hr. rewrite forallb_forall in C. specialize (C (Z.to_nat rdb) ltac:(apply in_seq; lia)). cbv beta in C.
  rewrite Z2Nat.id in C by lia. apply Bool.eqb_prop in C. split; intros H.
  - rewrite H in C. apply Z.eqb_eq. rewrite <- C. reflexivity.
  - assert (B : (Z.land rdb 2 =? 0) = true) by (apply Z.eqb_eq; exact H). rewrite <- C in B. apply Z.eqb_eq in B.
    apply bv_eq. rewrite B. reflexivity.
Qed.

Lemma s_loopB : s_loopB_stmt.
Proof.
  unfold s_loopB_stmt.
  intros fx R M model K sp1 Rr IS rdb Hh Hl Hfp H2 [Hsp Hal] H9 [Hr1 Hr2] [Hi1 Hi2] Hial RO C288 Cis Cvt Crdb Rrdb Kws Kepi.
  change RT.LOOPB with (CC.cp_pc GB.cp3).
  hv_open GB.cp3 (GB.plans 3%nat _ eq_refl) (-64) [IS; rdb] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rdb.
    unfold know_ok, GB.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + kw64 (Rr + 288) 0 C288. + kw64 (Rr + 240) IS Cis. + kw64 IS PML.VT_ISS Cvt. + kw8 (IS + 152) rdb Crdb.
    + tk_kimg RO. + e_range. + e_range. + e_align Hial.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rdb.
    leaf_open Hag HLF E' 66%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 2%nat k Hnth ltac:(probes_in HLF PF; destruct PF as [X _]; w2z X).
    + apply (Kws (proj1 (bit1_eq rdb Rrdb) X) fx' R' Hfp');
        [llin HLF r_sp | unfold RT.RN_R_WS2; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
    + apply (Kepi (fun Y => X (proj2 (bit1_eq rdb Rrdb) Y)) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
Qed.

Lemma s_loopC : s_loopC_stmt.
Proof.
  unfold s_loopC_stmt.
  intros fx R M model K sp1 Rr e p Hh Hl Hfp H2 [Hsp Hal] H9 [Hr1 Hr2] Hra Ce Cp Re Rp Kchunk Kpcd.
  change RT.LOOPC with (CC.cp_pc GB.cp4).
  hv_open GB.cp4 (GB.plans 4%nat _ eq_refl) (-32) [e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat e. gh_atom E sp1 R 65%nat 1%nat p.
    unfold know_ok, GB.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_align Hra. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat e. gh_atom E sp1 R 65%nat 1%nat p.
    leaf_open Hag HLF E' 66%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 2%nat k Hnth ltac:(probes_in HLF PF; pf_all PF).
    + apply (Kchunk ltac:(lia) fx' R' Hfp');
        [llin HLF r_sp | unfold RT.CD_R_CHUNK; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 41%nat r_s1 | lkeep HLF Hag64 sp1 R r_a1 40%nat r_s0 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
    + apply (Kpcd ltac:(lia) fx' R' Hfp');
        [llin HLF r_sp | unfold RT.CD_R_PCD; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | lkeep HLF Hag64 sp1 R r_a1 40%nat r_s0 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
Qed.


Lemma u_lin_mod : forall E e v, lden E (lin_of e) = v -> bv_unsigned (edenot E e) = v mod 2 ^ 64.
Proof.
  intros E e v H. pose proof (lin_of_sound E e) as [q Hq]. unfold uE in Hq. rewrite H in Hq.
  pose proof (bv_unsigned_in_range _ (edenot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
  rewrite Hq, Z_mod_plus_full. symmetry. apply Z.mod_small. exact Hu.
Qed.

Lemma krange_sltu1 : forall E (M : mem) a b va vb, lden E (lin_of a) = va -> lden E (lin_of b) = vb -> va mod 2 ^ 64 < vb mod 2 ^ 64 ->
  kentry_ok RSEGS E M (KRange (EAlu ALU_SLTU a b) 1 1).
Proof.
  intros E M a b va vb Ha Hb Hlt. cbn [kentry_ok edenot].
  change (alu64 ALU_SLTU (edenot E a) (edenot E b)) with (if bv_ltu (edenot E a) (edenot E b) then Z_to_bv 64 1 else Z_to_bv 64 0 : word).
  unfold bv_ltu. rewrite (u_lin_mod E a va Ha), (u_lin_mod E b vb Hb).
  destruct (Z.ltb_spec (va mod 2 ^ 64) (vb mod 2 ^ 64)); [|lia]. rewrite u64_of_Z by lia. lia.
Qed.

Definition hvO (sp0 : Z) (R : bvmap 5 word) (gh : nat -> word) (ov : list (nat * word)) : env :=
  Env (fun n => match List.find (fun p => Nat.eqb (fst p) n) ov with Some p => snd p | None => TK.hvV sp0 R gh n end) (fun _ => []).
Definition ovk (ov : list (nat * word)) (n : nat) : bool := existsb (fun p => Nat.eqb (fst p) n) ov.

Lemma hvO_out : forall sp0 R gh ov n, ovk ov n = false -> ev (hvO sp0 R gh ov) n = ev (TK.hvE sp0 R gh) n.
Proof.
  intros sp0 R gh ov n H. cbn [ev hvO TK.hvE].
  destruct (find (fun p => Nat.eqb (fst p) n) ov) as [p|] eqn:F; [|reflexivity].
  exfalso. apply find_some in F as [Hin Hq].
  assert (X : ovk ov n = true) by (unfold ovk; apply existsb_exists; exists p; split; assumption).
  congruence.
Qed.

Lemma hvO_reg : forall sp0 R gh ov (r : reg), ovk ov (32 + ridx r) = false -> ev (hvO sp0 R gh ov) (32 + ridx r) = getr R r.
Proof. intros sp0 R gh ov r H. rewrite hvO_out by exact H. apply TK.hvE_reg. Qed.

Definition hv_shapeO (sr : list expr) (off : Z) (pins : list (nat * Z)) (ex : list (nat * expr)) (ov : list (nat * word)) : bool :=
  negb (ovk ov 2) && forallb (fun q => match List.find (fun p => Nat.eqb (fst p) q) ex with
    | Some p => expr_eqb (nth q sr (ELit 0)) (snd p)
    | None => expr_eqb (nth q sr (ELit 0)) (RK.hv_slot off pins q) && negb (ovk ov (32 + q)) end) (seq 1 31).

Lemma regs_ok_hvO : forall sr off pins ex ov sp0 R gh,
  hv_shapeO sr off pins ex ov = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  (forall q e, In (q, e) ex -> getr R (Z_to_bv 5 (Z.of_nat q)) = edenot (hvO sp0 R gh ov) e) ->
  regs_ok (hvO sp0 R gh ov) sr R.
Proof.
  intros sr off pins ex ov sp0 R gh Hsh Hsp Hspo H2 Hpins Hex. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold hv_shapeO in Hsh. apply andb_true_iff in Hsh as [H2o Hsh]. apply negb_true_iff in H2o.
  rewrite forallb_forall in Hsh. specialize (Hsh _ Hq).
  destruct (find (fun p => Nat.eqb (fst p) (ridx r)) ex) as [[q e]|] eqn:Hf.
  - apply expr_eqb_eq in Hsh. rewrite Hsh. apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q.
    cbn [snd]. rewrite <- (Hex _ _ Hin), ridx_roundtrip. reflexivity.
  - apply andb_true_iff in Hsh as [Hsh Hno]. apply negb_true_iff in Hno. apply expr_eqb_eq in Hsh. rewrite Hsh.
    unfold RK.hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
    + apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
      destruct (Z.eqb_spec off 0) as [->|Hne].
      * cbn [edenot]. rewrite hvO_out by exact H2o. cbn [ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
      * cbn [edenot]. rewrite hvO_out by exact H2o. cbn [ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
    + destruct (find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf2.
      * apply find_some in Hf2 as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
        rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
      * cbn [edenot]. rewrite hvO_out by exact Hno. symmetry. apply TK.hvE_reg.
Qed.

Lemma keeps_hvO_sound : forall c ps sp0 R gh ov E' R' M M' qs (r : reg),
  CC.leaf_facts RSEGS c ps E' R' M M' -> env_agree 64 (hvO sp0 R gh ov) E' -> TK.keeps_hv ps qs = true ->
  forallb (fun q => negb (ovk ov (32 + q))) qs = true -> In (ridx r) qs -> getr R' r = getr R r.
Proof.
  intros c ps sp0 R gh ov E' R' M M' qs r HLF Hag H Hov Hin. unfold TK.keeps_hv in H. rewrite forallb_forall in H, Hov.
  rewrite <- (ridx_roundtrip r) at 1. rewrite (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF (H _ Hin)). cbn [edenot].
  rewrite <- (proj1 Hag) by (pose proof (ridx_range r); lia). apply hvO_reg. apply negb_true_iff. exact (Hov _ Hin).
Qed.

Lemma keepsR_of : forall qs (R0 R' : bvmap 5 word), Forall (fun q => getr R' (Z_to_bv 5 (Z.of_nat q)) = getr R0 (Z_to_bv 5 (Z.of_nat q))) qs -> TK.keepsR qs R0 R'.
Proof. intros qs R0 R' H r Hr. rewrite Forall_forall in H. specialize (H _ Hr). rewrite ridx_roundtrip in H. exact H. Qed.

Ltac reg_atomO E sp0 R v r Hr := let U := fresh "Ur" in
  lazymatch type of Hr with getr _ _ = Z_to_bv 64 ?z =>
    assert (U : bv_unsigned (ev E v) = z) by (change v with (32 + ridx (r : reg))%nat; subst E; rewrite hvO_out by reflexivity; apply (RK.hv_reg_u sp0 R _ r z Hr); lia) end.
Ltac gh_atomO E sp0 R v k z := let U := fresh "Ug" in
  assert (U : bv_unsigned (ev E v) = z) by (change v with (64 + k)%nat; subst E; rewrite hvO_out by reflexivity; eapply RK.ghl_u; [reflexivity | lia]).
Ltac hv_keepsO HLF Hag64 sp0 R E' R' M M' qs := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; exact (keeps_hvO_sound _ _ sp0 R _ _ E' R' M M' qs r HLF Hag64 eq_refl eq_refl Hr).
Ltac lkeepO HLF Hag64 sp0 R x v r := let x' := rr x in let r' := rr r in tk_reg HLF x'; rewrite <- (proj1 Hag64 v) by lia; apply (hvO_reg sp0 R _ _ r'); reflexivity.
Ltac lghost HLF := lazymatch goal with |- getr _ ?r = _ => tk_reg HLF r end;
  lazymatch goal with |- ev ?E' ?v = _ => lazymatch goal with U : bv_unsigned (ev E' v) = _ |- _ => rewrite (RK.w_of_u _ _ U); apply Z_to_bv_bv_unsigned end end.

Ltac ext0 := eapply CL5.krange_intro with (v := 0);
  [lin_eval; match goal with U : bv_unsigned (ev ?E 64) = 0 |- _ => rewrite (RK.w_of_u _ _ U) end; rewrite RK.ext_s32 by lia; rewrite u64_of_Z by lia; lia | lia | lia].

Lemma s_rn_k11 : forall (fx : FPState) R M model K sp1 Rr Ev vis p e p' k,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 k ->
  pok p' -> 1 <= k <= 2 ^ 47 ->
  L5.u32_at RSEGS M Ev 0 -> L5.u64_at RSEGS M (Rr + 312) vis -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p ->
  pok vis -> vis mod 8 = 0 -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> L5.defined M (Rr + 512) 16 -> (Rr + 592 <= Ev \/ Ev + 16 <= Rr) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> getr R' 1%bv = Z_to_bv 64 RT.RN_R_PSOME ->
      getr R' 10%bv = getr R 18%bv -> getr R' 11%bv = Z_to_bv 64 vis -> getr R' 12%bv = Z_to_bv 64 Ev -> getr R' 22%bv = Z_to_bv 64 p' -> getr R' 21%bv = Z_to_bv 64 (p' + k) ->
      TK.keepsR [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat R R' ->
      L5.u64_at RSEGS M' (Rr + 512) (p' + k) -> L5.u64_at RSEGS M' (Rr + 520) p' -> TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' PML.PC_PARSE_SOME M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x47278 M model) K.
Proof.
  intros fx R M model K sp1 Rr Ev vis p e p' k Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H10 H11 [Hq1 Hq2] Hk Cc Cv Ce Cp [Hv1 Hv2] Hva Rp Re D Dj Kok.
  change 0x47278 with (CC.cp_pc GA.cp11).
  set (E := hvO sp1 R (RK.ghl [0; vis; e; p]) [(12%nat, getr R 12%bv)]).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (subst E; rewrite hvO_out by reflexivity; apply TK.hvE_sp; lia).
  reg_atomO E sp1 R 41%nat r_s1 H9. reg_atomO E sp1 R 40%nat r_s0 H8. reg_atomO E sp1 R 42%nat r_a0 H10. reg_atomO E sp1 R 43%nat r_a1 H11.
  gh_atomO E sp1 R 64%nat 0%nat 0. gh_atomO E sp1 R 65%nat 1%nat vis. gh_atomO E sp1 R 66%nat 2%nat e. gh_atomO E sp1 R 67%nat 3%nat p.
  apply (TK.stretch_cps FPM GA.cp11 fx E R M model K (GA.plans 11%nat _ eq_refl) Hh Hl Hfp).
  - apply (regs_ok_hvO _ (-64) (@nil (nat * Z)) [(12%nat, EVar 12)]); [vm_compute; reflexivity | lia | lia | exact H2 | no_pins |].
    intros q x [X|[]]. injection X as <- <-. subst E. cbn [edenot ev hvO find fst snd Nat.eqb]. reflexivity.
  - unfold know_ok, GA.cp11. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev 0 Cc. + kw64 (Rr + 312) vis Cv. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
    + e_wr. + e_disj. + e_range. + e_align Hva. + e_range. + e_range. + ext0.
  - intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
    leaf_open Hag HLF E' 68%nat.
    leaves 1%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
    apply (Kok fx' R' M' Hfp'); [llin HLF r_sp | unfold RT.RN_R_PSOME; llin HLF r_ra | lkeepO HLF Hag64 sp1 R r_a0 50%nat r_s2 | llin HLF r_a1 | llin HLF r_a2 | llin HLF r_s6 | llin HLF r_s5
      | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat
      | lcell64 HLF (EVar 41) 512 (EAlu ALU_ADD (EVar 42) (EVar 43)); vlin | lcell64 HLF (EVar 41) 520 (EVar 42); vlin | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_rn_k12 : forall (fx : FPState) R M model K sp1 Rr Ev p e p' k,
  m_halted model = None -> m_vm_lazy model = [] -> PML.fp_ok fx -> getr R 2%bv = Z_to_bv 64 (sp1 - 64) -> spok sp1 ->
  getr R 9%bv = Z_to_bv 64 Rr -> getr R 8%bv = Z_to_bv 64 Ev -> pok Rr -> pok Ev -> getr R 10%bv = Z_to_bv 64 p' -> getr R 11%bv = Z_to_bv 64 k ->
  pok p' -> 1 <= k <= 2 ^ 47 ->
  L5.u32_at RSEGS M Ev 0 -> L5.u64_at RSEGS M (Rr + 512) e -> L5.u64_at RSEGS M (Rr + 520) p -> 0 <= p < 2 ^ 64 -> 0 <= e < 2 ^ 64 ->
  L5.defined M (Rr + 512) 16 -> (Rr + 592 <= Ev \/ Ev + 16 <= Rr) ->
  (forall (fx' : FPState) R' M', PML.fp_ok fx' -> getr R' 2%bv = Z_to_bv 64 (sp1 - 64) -> TK.keepsR KSA R R' ->
      L5.u64_at RSEGS M' (Rr + 512) (p' + k) -> L5.u64_at RSEGS M' (Rr + 520) p' -> TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M M' -> mem_grows M M' ->
      srealizes RSEGS SCFG (@PML.cfg fx' R' RT.LOOPB M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx R 0x4735c M model) K.
Proof.
  intros fx R M model K sp1 Rr Ev p e p' k Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H10 H11 [Hq1 Hq2] Hk Cc Ce Cp Rp Re D Dj Kok.
  change 0x4735c with (CC.cp_pc GA.cp12).
  set (E := hvO sp1 R (RK.ghl [0; e; p]) [(12%nat, getr R 12%bv)]).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (subst E; rewrite hvO_out by reflexivity; apply TK.hvE_sp; lia).
  reg_atomO E sp1 R 41%nat r_s1 H9. reg_atomO E sp1 R 40%nat r_s0 H8. reg_atomO E sp1 R 42%nat r_a0 H10. reg_atomO E sp1 R 43%nat r_a1 H11.
  gh_atomO E sp1 R 64%nat 0%nat 0. gh_atomO E sp1 R 65%nat 1%nat e. gh_atomO E sp1 R 66%nat 2%nat p.
  apply (TK.stretch_cps FPM GA.cp12 fx E R M model K (GA.plans 12%nat _ eq_refl) Hh Hl Hfp).
  - apply (regs_ok_hvO _ (-64) (@nil (nat * Z)) [(12%nat, EVar 12)]); [vm_compute; reflexivity | lia | lia | exact H2 | no_pins |].
    intros q x [X|[]]. injection X as <- <-. subst E. cbn [edenot ev hvO find fst snd Nat.eqb]. reflexivity.
  - unfold know_ok, GA.cp12. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev 0 Cc. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
    + e_wr. + e_disj. + e_range. + e_range. + ext0.
  - intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
    leaf_open Hag HLF E' 67%nat.
    leaves 1%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
    apply (Kok fx' R' M' Hfp'); [llin HLF r_sp | hv_keepsO HLF Hag64 sp1 R E' R' M M' KSA
      | lcell64 HLF (EVar 41) 512 (EAlu ALU_ADD (EVar 42) (EVar 43)); vlin | lcell64 HLF (EVar 41) 520 (EVar 42); vlin | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_rn_entry : s_rn_entry_stmt.
Proof.
  unfold s_rn_entry_stmt.
  intros fx R M model K sp1 Rr IS rdb sb eb rav Hh Hl Hfp H2 [Hsp Hal] H10 H1 Hrav [Hr1 Hr2] [Hi1 Hi2] His RO Cis Cvt Crdb Rrdb Hrdb1 Csb Rsb Ceb Hvec Dsp D576 Hsr Hsi Hdj Kc.
  change PML.PC_READ_NEXT with (CC.cp_pc GA.cp0).
  destruct Hvec as [-> | ([Hs1 Hs2] & Hlt & Hle)].
  - hv_open GA.cp0 (GA.plans 0%nat _ eq_refl) 0 [IS; rdb; sb] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
    + reg_atom E sp1 R 42%nat r_a0 H10. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rdb. gh_atom E sp1 R 66%nat 2%nat sb.
      unfold know_ok, GA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align Hal. * e_unk. * e_wr. * e_range. * kw64 (Rr + 240) IS Cis. * kw64 IS PML.VT_ISS Cvt. * kw8 (IS + 152) rdb Crdb. * tk_kimg RO.
      * e_range. * e_range. * kw64 (Rr + 568) sb Csb. * kw64 (Rr + 576) sb Ceb. * e_wr. * e_disj. * e_disj. * e_disj. * e_align His.
    + intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
      reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 33%nat r_ra H1. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rdb. gh_atom E sp1 R 66%nat 2%nat sb.
      leaf_open Hag HLF E' 67%nat.
      leaves 2%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
      * apply (Kc fx' R' M' Hfp'); [llin HLF r_sp | unfold RT.RN_R_PUSH; llin HLF r_ra | llin HLF r_a0 | llin HLF r_a1 | llin HLF r_s0 | llin HLF r_s1 | llin HLF r_s2
          | hv_keeps HLF Hag64 sp1 R E' R' M M' KS012 | | lcell64 HLF (EVar 2) (-72) (ELit 0x4723c); vlit | lcell64 HLF (EVar 2) (-80) (EVar 43); vreg Hag64 sp1 R 43%nat r_a1
          | lcell8 HLF (EVar 2) (-81) (ELit 0); vlit | lcell64 HLF (EVar 42) 576 (EVar 66); cbn [edenot]; assumption | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
        unfold rn_frame. split; [lcell64 HLF (EVar 2) (-8) (EVar 33); cbn [edenot]; assumption|].
        split; [lcell64 HLF (EVar 2) (-16) (EVar 40); vreg Hag64 sp1 R 40%nat r_s0|]. split; [lcell64 HLF (EVar 2) (-24) (EVar 41); vreg Hag64 sp1 R 41%nat r_s1|].
        split; [lcell64 HLF (EVar 2) (-32) (EVar 50); vreg Hag64 sp1 R 50%nat r_s2|]. split; [lcell64 HLF (EVar 2) (-40) (EVar 51); vreg Hag64 sp1 R 51%nat r_s3|].
        split; [lcell64 HLF (EVar 2) (-48) (EVar 52); vreg Hag64 sp1 R 52%nat r_s4|]. split; [lcell64 HLF (EVar 2) (-56) (EVar 53); vreg Hag64 sp1 R 53%nat r_s5|].
        lcell64 HLF (EVar 2) (-64) (EVar 54); vreg Hag64 sp1 R 54%nat r_s6.
      * exfalso; lia.
  - change (CC.cp_pc GA.cp0) with (CC.cp_pc GA.cp9).
    hv_open GA.cp9 (GA.plans 9%nat _ eq_refl) 0 [IS; rdb; sb; eb] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
    + reg_atom E sp1 R 42%nat r_a0 H10. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rdb. gh_atom E sp1 R 66%nat 2%nat sb. gh_atom E sp1 R 67%nat 3%nat eb.
      unfold know_ok, GA.cp9. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align Hal. * e_unk. * e_wr. * e_range. * kw64 (Rr + 240) IS Cis. * kw64 IS PML.VT_ISS Cvt. * kw8 (IS + 152) rdb Crdb. * tk_kimg RO.
      * e_range. * e_range. * kw64 (Rr + 568) sb Csb. * kw64 (Rr + 576) eb Ceb. * e_wr. * e_disj. * e_disj. * e_disj. * e_align His.
      * e_range. * e_range.
      * apply (krange_sltu1 _ _ _ _ (- eb) (sb - eb)); [lin_eval; rw_atoms; lia | lin_eval; rw_atoms; lia |].
        rewrite <- (Z.mod_unique (- eb) (2 ^ 64) (-1) (2 ^ 64 - eb)) by lia.
        rewrite <- (Z.mod_unique (sb - eb) (2 ^ 64) (-1) (2 ^ 64 + sb - eb)) by lia. lia.
    + intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
      reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 33%nat r_ra H1. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rdb. gh_atom E sp1 R 66%nat 2%nat sb.
      gh_atom E sp1 R 67%nat 3%nat eb.
      leaf_open Hag HLF E' 68%nat.
      leaves 2%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
      * apply (Kc fx' R' M' Hfp'); [llin HLF r_sp | unfold RT.RN_R_PUSH; llin HLF r_ra | llin HLF r_a0 | llin HLF r_a1 | llin HLF r_s0 | llin HLF r_s1 | llin HLF r_s2
          | hv_keeps HLF Hag64 sp1 R E' R' M M' KS012 | | lcell64 HLF (EVar 2) (-72) (ELit 0x4723c); vlit | lcell64 HLF (EVar 2) (-80) (EVar 43); vreg Hag64 sp1 R 43%nat r_a1
          | lcell8 HLF (EVar 2) (-81) (ELit 0); vlit | lcell64 HLF (EVar 42) 576 (EVar 66); cbn [edenot]; assumption | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
        unfold rn_frame. split; [lcell64 HLF (EVar 2) (-8) (EVar 33); cbn [edenot]; assumption|].
        split; [lcell64 HLF (EVar 2) (-16) (EVar 40); vreg Hag64 sp1 R 40%nat r_s0|]. split; [lcell64 HLF (EVar 2) (-24) (EVar 41); vreg Hag64 sp1 R 41%nat r_s1|].
        split; [lcell64 HLF (EVar 2) (-32) (EVar 50); vreg Hag64 sp1 R 50%nat r_s2|]. split; [lcell64 HLF (EVar 2) (-40) (EVar 51); vreg Hag64 sp1 R 51%nat r_s3|].
        split; [lcell64 HLF (EVar 2) (-48) (EVar 52); vreg Hag64 sp1 R 52%nat r_s4|]. split; [lcell64 HLF (EVar 2) (-56) (EVar 53); vreg Hag64 sp1 R 53%nat r_s5|].
        lcell64 HLF (EVar 2) (-64) (EVar 54); vreg Hag64 sp1 R 54%nat r_s6.
      * exfalso; lia.
Qed.

Lemma s_rn_r_push : s_rn_r_push_stmt.
Proof.
  unfold s_rn_r_push_stmt.
  intros fx R M model K sp1 Rr Ev fl Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] Hsr D Cfl Rfl Cra Cev REv Kc.
  change RT.RN_R_PUSH with (CC.cp_pc GA.cp1).
  set (E := hvO sp1 R (RK.ghl [fl]) [(40%nat, Z_to_bv 64 Ev)]).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (subst E; rewrite hvO_out by reflexivity; apply TK.hvE_sp; lia).
  reg_atomO E sp1 R 41%nat r_s1 H9. gh_atomO E sp1 R 64%nat 0%nat fl.
  assert (Uo : bv_unsigned (ev E 40) = Ev) by (subst E; cbn [ev hvO find fst snd Nat.eqb]; apply u64_of_Z; lia).
  apply (TK.stretch_cps FPM GA.cp1 fx E R M model K (GA.plans 1%nat _ eq_refl) Hh Hl Hfp).
  - apply (regs_ok_hvO _ (-96) (@nil (nat * Z)) [(8%nat, nth 8 (CC.cp_regs GA.cp1) (ELit 0))]); [vm_compute; reflexivity | lia | lia | exact H2 | no_pins |].
    intros q x [X|[]]. injection X as <- <-. change (hvO sp1 R (RK.ghl [fl]) [(40%nat, Z_to_bv 64 Ev)]) with E. rewrite (TK.edenot_lin _ _ (Rr + 320)); [exact H8 | lin_eval; rw_atoms; lia | lia].
  - unfold know_ok, GA.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr. + e_unk. + e_wr.
    + kw8 (Rr + 531) fl Cfl. + e_range. + kw64 (sp1 - 72) 0x4723c Cra. + kw64 (sp1 - 80) Ev Cev. + e_disj.
  - intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
    leaf_open Hag HLF E' 65%nat.
    leaves 1%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
    apply (Kc fx' R' M' Hfp'); [llin HLF r_sp | llin HLF r_s0 | llin HLF r_a0 | llin HLF r_s3 | llin HLF r_s4
      | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 9; 18; 21; 22; 23; 24; 25; 26; 27]%nat
      | lcell8 HLF (EVar 41) 528 (ELit 1); vlit | lcell8 HLF (EVar 41) 531 (ELit 1); vlit | lcell8 HLF (EVar 41) 532 (ELit 0); vlit
      | lcell32 HLF (EVar 41) 464 (ELit 0); vlit | lcell64 HLF (EVar 41) 480 (ELit 1); vlit | lcell64 HLF (EVar 41) 488 (ELit 0); vlit
      | lcell64 HLF (EVar 41) 496 (ELit 0); vlit | lframe HLF | exact (CC.lf_grows _ _ _ _ _ _ _ HLF)].
Qed.

Lemma s_rn_r_chunkA : s_rn_r_chunkA_stmt.
Proof.
  unfold s_rn_r_chunkA_stmt.
  intros fx R M model K sp1 Rr Ev code vis p e p' k Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H10 H11 Hp0 Hk0 Hpk Hq Cc Rc Cv Ce Cp Rv [Hv1 Hv2] Hva Rp Re D Dj Kerr Kok.
  change RT.RN_R_CHUNKA with (CC.cp_pc GA.cp2).
  hv_open GA.cp2 (GA.plans 2%nat _ eq_refl) (-64) [code; vis; e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat vis. gh_atom E sp1 R 66%nat 2%nat e. gh_atom E sp1 R 67%nat 3%nat p.
    unfold know_ok, GA.cp2. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw64 (Rr + 312) vis Cv. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
    + e_wr. + e_disj. + e_range. + e_align Hva.
  - intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat vis. gh_atom E sp1 R 66%nat 2%nat e. gh_atom E sp1 R 67%nat 3%nat p.
    leaf_open Hag HLF E' 68%nat.
    leaves 3%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 41) (EVar 66) (EVar 67). subst M'.
      apply (Kok ltac:(lia) fx' R' M p e Hfp'); [llin HLF r_sp | unfold RT.RN_R_PSOME; llin HLF r_ra | lkeep HLF Hag64 sp1 R r_a0 50%nat r_s2 | llin HLF r_a1 | llin HLF r_a2 | llin HLF r_s6 | llin HLF r_s5 | hv_keeps HLF Hag64 sp1 R E' R' M M [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat | left; split; [lia | split; [reflexivity | split; reflexivity]]].
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 41) (EVar 66) (EVar 67). subst M'.
      destruct (Hq ltac:(lia)) as [[Hq1 Hq2] Hq3]. assert (C0 : code = 0) by lia. rewrite C0 in Cc.
      assert (KR : TK.keepsR [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat R R') by (hv_keeps HLF Hag64 sp1 R E' R' M M [3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%nat).
      assert (K18 : getr R' 18%bv = getr R 18%bv) by (lkeep HLF Hag64 sp1 R r_s2 50%nat r_s2).
      apply (s_rn_k11 fx' R' M model K sp1 Rr Ev vis p e p' k Hh Hl Hfp'); [llin HLF r_sp | exact (conj Hsp Hal) | llin HLF r_s1 | llin HLF r_s0 | split; lia | split; lia
        | llin HLF r_a0 | llin HLF r_a1 | split; lia | lia | exact Cc | exact Cv | exact Ce | exact Cp | split; lia | exact Hva | lia | lia | exact D | exact Dj |].
      intros fx2 R2 M2 Hfp2 X2 X1 X10 X11 X12 X22 X21 XK C512 C520 SM MG.
      apply (Kok C0 fx2 R2 M2 p' (p' + k) Hfp2 X2 X1); [rewrite X10; exact K18 | exact X11 | exact X12 | exact X22 | exact X21 | exact (TK.keepsR_trans _ _ _ _ KR XK) | right].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact C512|]. split; [exact C520|]. split; [exact SM | exact MG].
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 41) (EVar 66) (EVar 67). subst M'.
      apply (Kerr ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M KSW].
Qed.

Lemma s_rn_r_psome : s_rn_r_psome_stmt.
Proof.
  unfold s_rn_r_psome_stmt.
  intros fx R M model K sp1 Rr Ev code st dn mo p e rav R0 Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H19 H20 H22 H21 Rp Re Cc Rc Cst Cdn Cmo Rst Rdn Rmo
    [F8 [F16 [F24 [F32 [F40 [F48 [F56 F64]]]]]]] Hrav Kws Kloop Kepi Kset.
  change RT.RN_R_PSOME with (CC.cp_pc GA.cp3).
  pose proof (bv_unsigned_in_range _ (getr R0 8%bv)) as B8. pose proof (bv_unsigned_in_range _ (getr R0 9%bv)) as B9.
  pose proof (bv_unsigned_in_range _ (getr R0 18%bv)) as B18. pose proof (bv_unsigned_in_range _ (getr R0 19%bv)) as B19.
  pose proof (bv_unsigned_in_range _ (getr R0 20%bv)) as B20. pose proof (bv_unsigned_in_range _ (getr R0 21%bv)) as B21.
  pose proof (bv_unsigned_in_range _ (getr R0 22%bv)) as B22.
  change (bv_modulus 64) with (2 ^ 64) in B8, B9, B18, B19, B20, B21, B22.
  set (E := hvO sp1 R (RK.ghl [code; st; dn; mo; bv_unsigned (getr R0 22%bv); bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 19%bv);
    bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 8%bv); rav]) [(21%nat, getr R 21%bv)]).
  assert (U2 : bv_unsigned (ev E 2) = sp1) by (subst E; rewrite hvO_out by reflexivity; apply TK.hvE_sp; lia).
  reg_atomO E sp1 R 41%nat r_s1 H9. reg_atomO E sp1 R 40%nat r_s0 H8. reg_atomO E sp1 R 54%nat r_s6 H22.
  assert (Uo : bv_unsigned (ev E 21) = e) by (subst E; cbn [ev hvO find fst snd Nat.eqb]; rewrite H21; apply u64_of_Z; lia).
  gh_atomO E sp1 R 64%nat 0%nat code. gh_atomO E sp1 R 65%nat 1%nat st. gh_atomO E sp1 R 66%nat 2%nat dn. gh_atomO E sp1 R 67%nat 3%nat mo.
  gh_atomO E sp1 R 68%nat 4%nat (bv_unsigned (getr R0 22%bv)). gh_atomO E sp1 R 69%nat 5%nat (bv_unsigned (getr R0 21%bv)).
  gh_atomO E sp1 R 70%nat 6%nat (bv_unsigned (getr R0 20%bv)). gh_atomO E sp1 R 71%nat 7%nat (bv_unsigned (getr R0 19%bv)).
  gh_atomO E sp1 R 72%nat 8%nat (bv_unsigned (getr R0 18%bv)). gh_atomO E sp1 R 73%nat 9%nat (bv_unsigned (getr R0 9%bv)).
  gh_atomO E sp1 R 74%nat 10%nat (bv_unsigned (getr R0 8%bv)). gh_atomO E sp1 R 75%nat 11%nat rav.
  apply (TK.stretch_cps FPM GA.cp3 fx E R M model K (GA.plans 3%nat _ eq_refl) Hh Hl Hfp).
  - apply (regs_ok_hvO _ (-64) [(19%nat, 1); (20%nat, 2)] [(21%nat, nth 21 (CC.cp_regs GA.cp3) (ELit 0))]); [vm_compute; reflexivity | lia | lia | exact H2 | pins45 H19 H20 |].
    intros q x [X|[]]. injection X as <- <-. change (nth 21 (CC.cp_regs GA.cp3) (ELit 0)) with (EVar 21). cbn [edenot ev hvO find fst snd Nat.eqb]. reflexivity.
  - unfold know_ok, GA.cp3. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw8 (Rr + 528) st Cst. + kw8 (Rr + 532) dn Cdn. + kw8 (Rr + 531) mo Cmo.
    + e_range. + e_range.
    + kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F64. + kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F56.
    + kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F48. + kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F40.
    + kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F32. + kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F24.
    + kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F16. + kw64 (sp1 - 8) rav F8.
  - intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
    leaf_open Hag HLF E' 76%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 7%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
    + apply (Kloop ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | llin HLF r_a0 | llin HLF r_s3 | llin HLF r_s4 | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat].
    + apply (Kws ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | unfold RT.LOOPB; llin HLF r_ra | lkeepO HLF Hag64 sp1 R r_a0 50%nat r_s2
        | llin HLF r_s3 | llin HLF r_s4 | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat].
    + apply (Kset ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | llin HLF r_ra | llin HLF r_a0 | llin HLF r_a1
        | apply keepsR_of; repeat (apply Forall_cons; [lghost HLF|]); apply Forall_nil | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 23; 24; 25; 26; 27]%nat].
    + apply (Kloop ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | llin HLF r_a0 | llin HLF r_s3 | llin HLF r_s4 | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat].
    + apply (Kepi ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat].
    + apply (Kloop ltac:(lia) ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | llin HLF r_a0 | llin HLF r_s3 | llin HLF r_s4 | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat].
    + apply (Kepi ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keepsO HLF Hag64 sp1 R E' R' M M' [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%nat].
Qed.

Lemma s_rn_r_ws2 : s_rn_r_ws2_stmt.
Proof.
  unfold s_rn_r_ws2_stmt.
  intros fx R M model K sp1 Rr p e Hh Hl Hfp H2 [Hsp Hal] H9 [Hr1 Hr2] Ce Cp Rp Re Kck Kepi.
  change RT.RN_R_WS2 with (CC.cp_pc GA.cp4).
  hv_open GA.cp4 (GA.plans 4%nat _ eq_refl) (-64) [e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat e. gh_atom E sp1 R 65%nat 1%nat p.
    unfold know_ok, GA.cp4. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. gh_atom E sp1 R 64%nat 0%nat e. gh_atom E sp1 R 65%nat 1%nat p.
    leaf_open Hag HLF E' 66%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 2%nat k Hnth ltac:(probes_in HLF PF; pf_all PF).
    + apply (Kck ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | unfold RT.RN_R_CHUNKB; llin HLF r_ra | llin HLF r_a0 | lkeep HLF Hag64 sp1 R r_a1 40%nat r_s0 | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
    + apply (Kepi ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M' KSA].
Qed.

Lemma s_rn_r_chunkB : s_rn_r_chunkB_stmt.
Proof.
  unfold s_rn_r_chunkB_stmt.
  intros fx R M model K sp1 Rr Ev code p e p' k Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H10 H11 Hp0 Hk0 Hpk Hq Cc Rc Ce Cp Rp Re D Dj Kerr Kok.
  change RT.RN_R_CHUNKB with (CC.cp_pc GA.cp5).
  hv_open GA.cp5 (GA.plans 5%nat _ eq_refl) (-64) [code; e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p.
    unfold know_ok, GA.cp5. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp. + e_wr. + e_disj.
  - intros fx' E' R' M' n ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 41%nat r_s1 H9. reg_atom E sp1 R 40%nat r_s0 H8. reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 43%nat r_a1 H11.
    gh_atom E sp1 R 64%nat 0%nat code. gh_atom E sp1 R 65%nat 1%nat e. gh_atom E sp1 R 66%nat 2%nat p.
    leaf_open Hag HLF E' 67%nat.
    leaves 3%nat n Hnth ltac:(probes_in HLF PF; pf_all PF).
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 41) (EVar 65) (EVar 66). subst M'.
      apply (Kok ltac:(lia) fx' R' M Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M KSA | left; split; [lia | reflexivity]].
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 41) (EVar 65) (EVar 66). subst M'.
      destruct (Hq ltac:(lia)) as [[Hq1 Hq2] Hq3]. assert (C0 : code = 0) by lia. rewrite C0 in Cc.
      assert (KR : TK.keepsR KSA R R') by (hv_keeps HLF Hag64 sp1 R E' R' M M KSA).
      apply (s_rn_k12 fx' R' M model K sp1 Rr Ev p e p' k Hh Hl Hfp'); [llin HLF r_sp | exact (conj Hsp Hal) | llin HLF r_s1 | llin HLF r_s0 | split; lia | split; lia
        | llin HLF r_a0 | llin HLF r_a1 | split; lia | lia | exact Cc | exact Ce | exact Cp | lia | lia | exact D | exact Dj |].
      intros fx2 R2 M2 Hfp2 X2 XK C512 C520 SM MG.
      apply (Kok C0 fx2 R2 M2 Hfp2 X2 (TK.keepsR_trans _ _ _ _ KR XK)). right.
      split; [lia|]. split; [exact C512|]. split; [exact C520|]. split; [exact SM | exact MG].
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 41) (EVar 65) (EVar 66). subst M'.
      apply (Kerr ltac:(lia) fx' R' Hfp'); [llin HLF r_sp | hv_keeps HLF Hag64 sp1 R E' R' M M KSA].
Qed.


Definition swr (a b : reg) (R : bvmap 5 word) : bvmap 5 word := regupd (regupd R a (getr R b)) b (getr R a).
Lemma bv_ne : forall a b : reg, bv_unsigned a <> bv_unsigned b -> a <> b.
Proof. intros a b H X. apply H. rewrite X. reflexivity. Qed.
Ltac bvne := apply bv_ne; vm_compute; let X := fresh in intro X; discriminate X.
Lemma sw_a : forall (a b : reg) R, a <> 0%bv -> a <> b -> getr (swr a b R) a = getr R b.
Proof. intros a b R Ha Hab. unfold swr. rewrite getr_other by exact Hab. apply getr_same. exact Ha. Qed.
Lemma sw_b : forall (a b : reg) R, b <> 0%bv -> getr (swr a b R) b = getr R a.
Proof. intros a b R Hb. unfold swr. apply getr_same. exact Hb. Qed.
Lemma sw_o : forall (a b r : reg) R, r <> a -> r <> b -> getr (swr a b R) r = getr R r.
Proof. intros a b r R Ha Hb. unfold swr. rewrite getr_other by exact Hb. rewrite getr_other by exact Ha. reflexivity. Qed.
Lemma hvE_hi : forall sp0 R gh (r : reg) n, n = (32 + ridx r)%nat -> ev (TK.hvE sp0 R gh) n = getr R r.
Proof. intros sp0 R gh r n ->. apply TK.hvE_reg. Qed.
Lemma reg_is : forall (r s : reg) (q : nat), q = ridx r -> bv_unsigned s = Z.of_nat q -> r = s.
Proof. intros r s q Hq Hs. rewrite <- (ridx_roundtrip r), <- Hq. apply bv_eq. rewrite Hs. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. pose proof (bv_unsigned_in_range _ s) as B. change (bv_modulus 5) with 32 in B. lia. Qed.
Lemma reg_not : forall (r s : reg) (l : list nat), ~ In (ridx r) l -> In (ridx s) l -> r <> s.
Proof. intros r s l H1 H2 X. subst. exact (H1 H2). Qed.

Definition PR89 : list (nat * nat) := [(8%nat, 41%nat); (9%nat, 40%nat)].
Definition PR89Z : list (nat * nat) := [(8%nat, 41%nat); (9%nat, 40%nat); (12%nat, 12%nat)].
Definition PR4 : list (nat * nat) := [(8%nat, 41%nat); (9%nat, 40%nat); (10%nat, 43%nat); (11%nat, 42%nat)].
Abbreviation sw89 R := (swr 8%bv 9%bv R).
Abbreviation sw4 R := (swr 10%bv 11%bv (swr 8%bv 9%bv R)).

Lemma pr89 : forall sp0 R gh (r : reg) n, In (ridx r, n) PR89 -> ev (TK.hvE sp0 (sw89 R) gh) n = getr R r.
Proof.
  intros sp0 R gh r n H. destruct H as [X|[X|[]]]; injection X as Hr Hn; subst n.
  - rewrite (reg_is r 8%bv 8%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 9%bv 41%nat eq_refl). apply sw_b. bvne.
  - rewrite (reg_is r 9%bv 9%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 8%bv 40%nat eq_refl). apply sw_a; bvne.
Qed.
Lemma pr89z : forall sp0 R gh, getr R 12%bv = Z_to_bv 64 0 -> forall (r : reg) n, In (ridx r, n) PR89Z -> ev (TK.hvE sp0 (sw89 R) gh) n = getr R r.
Proof.
  intros sp0 R gh H12 r n H. destruct H as [X|[X|[X|[]]]]; injection X as Hr Hn; subst n.
  - rewrite (reg_is r 8%bv 8%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 9%bv 41%nat eq_refl). apply sw_b. bvne.
  - rewrite (reg_is r 9%bv 9%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 8%bv 40%nat eq_refl). apply sw_a; bvne.
  - rewrite (reg_is r 12%bv 12%nat Hr eq_refl). rewrite H12. reflexivity.
Qed.
Lemma pr4 : forall sp0 R gh (r : reg) n, In (ridx r, n) PR4 -> ev (TK.hvE sp0 (sw4 R) gh) n = getr R r.
Proof.
  intros sp0 R gh r n H. destruct H as [X|[X|[X|[X|[]]]]]; injection X as Hr Hn; subst n.
  - rewrite (reg_is r 8%bv 8%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 9%bv 41%nat eq_refl). rewrite sw_o by bvne. apply sw_b. bvne.
  - rewrite (reg_is r 9%bv 9%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 8%bv 40%nat eq_refl). rewrite sw_o by bvne. apply sw_a; bvne.
  - rewrite (reg_is r 10%bv 10%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 11%bv 43%nat eq_refl). rewrite sw_b by bvne. apply sw_o; bvne.
  - rewrite (reg_is r 11%bv 11%nat Hr eq_refl). rewrite (hvE_hi sp0 _ gh 10%bv 42%nat eq_refl). rewrite sw_a by bvne. apply sw_o; bvne.
Qed.
Lemma not89 : forall R (r : reg), ~ In (ridx r) (map fst PR89) -> getr (sw89 R) r = getr R r.
Proof. intros R r H. apply sw_o; apply (reg_not r _ _ H); vm_compute; tauto. Qed.
Lemma not89z : forall R (r : reg), ~ In (ridx r) (map fst PR89Z) -> getr (sw89 R) r = getr R r.
Proof. intros R r H. apply sw_o; apply (reg_not r _ _ H); vm_compute; tauto. Qed.
Lemma not4 : forall R (r : reg), ~ In (ridx r) (map fst PR4) -> getr (sw4 R) r = getr R r.
Proof. intros R r H. rewrite sw_o by (apply (reg_not r _ _ H); vm_compute; tauto). apply sw_o; apply (reg_not r _ _ H); vm_compute; tauto. Qed.

Definition sslot (off : Z) (pins : list (nat * Z)) (pr : list (nat * nat)) (q : nat) : expr :=
  match List.find (fun p => Nat.eqb (fst p) q) pr with Some p => EVar (snd p) | None => RK.hv_slot off pins q end.
Definition sshape (sr : list expr) (off : Z) (pins : list (nat * Z)) (pr : list (nat * nat)) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (sslot off pins pr q)) (seq 1 31).
Lemma find_fst_none : forall (pr : list (nat * nat)) q, List.find (fun p => Nat.eqb (fst p) q) pr = None -> ~ In q (map fst pr).
Proof.
  intros pr q Hf Hin. apply in_map_iff in Hin as [[q' n] [Hq Hin]]. cbn [fst] in Hq. subst q'.
  pose proof (find_none _ _ Hf _ Hin) as X. cbn [fst] in X. rewrite Nat.eqb_refl in X. discriminate X.
Qed.
Lemma regs_ok_sw : forall sr off pins pr sp0 R Rs gh,
  sshape sr off pins pr = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  (forall (r : reg) n, In (ridx r, n) pr -> ev (TK.hvE sp0 Rs gh) n = getr R r) ->
  (forall r : reg, ~ In (ridx r) (map fst pr) -> getr Rs r = getr R r) ->
  regs_ok (TK.hvE sp0 Rs gh) sr R.
Proof.
  intros sr off pins pr sp0 R Rs gh Hsh Hsp Hspo H2 Hpins Hpr Hnot. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold sshape in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold sslot. destruct (List.find (fun p => Nat.eqb (fst p) (ridx r)) pr) as [[q n]|] eqn:Hf.
  - apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot]. symmetry. apply Hpr. exact Hin.
  - pose proof (find_fst_none _ _ Hf) as Hn.
    unfold RK.hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
    + apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
      destruct (Z.eqb_spec off 0) as [->|Hne].
      * cbn [edenot ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
      * cbn [edenot ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
    + destruct (List.find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf2.
      * apply find_some in Hf2 as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
        rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
      * cbn [edenot]. rewrite TK.hvE_reg. symmetry. apply Hnot. exact Hn.
Qed.

Definition kslot (pr : list (nat * nat)) (q : nat) : expr :=
  match List.find (fun p => Nat.eqb (fst p) q) pr with Some p => EVar (snd p) | None => EVar (32 + q) end.
Definition keeps_sw (ps : SR.post_spec) (qs : list nat) (pr : list (nat * nat)) : bool :=
  forallb (fun q => CL.ps_reg_is ps q (kslot pr q)) qs.
Lemma keeps_sw_sound : forall c ps sp0 Rs gh E' R' M M' qs pr R,
  CC.leaf_facts RSEGS c ps E' R' M M' -> keeps_sw ps qs pr = true -> env_agree 64 (TK.hvE sp0 Rs gh) E' ->
  forallb (fun p => Nat.ltb (snd p) 64) pr = true ->
  (forall (r : reg) n, In (ridx r, n) pr -> ev (TK.hvE sp0 Rs gh) n = getr R r) ->
  (forall r : reg, ~ In (ridx r) (map fst pr) -> getr Rs r = getr R r) ->
  TK.keepsR qs R R'.
Proof.
  intros c ps sp0 Rs gh E' R' M M' qs pr R HLF H Hag Hlt Hpr Hnot r Hr.
  unfold keeps_sw in H. rewrite forallb_forall in H. specialize (H _ Hr).
  rewrite <- (ridx_roundtrip r) at 1. rewrite (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF H).
  unfold kslot. destruct (List.find (fun p => Nat.eqb (fst p) (ridx r)) pr) as [[q n]|] eqn:Hf.
  - apply find_some in Hf as [Hin Hq]. cbn [fst] in Hq. apply Nat.eqb_eq in Hq. subst q. cbn [snd edenot].
    rewrite forallb_forall in Hlt. specialize (Hlt _ Hin). cbn [snd] in Hlt. apply Nat.ltb_lt in Hlt.
    rewrite <- (proj1 Hag) by exact Hlt. apply Hpr. exact Hin.
  - cbn [edenot]. rewrite <- (proj1 Hag) by (pose proof (ridx_range r); lia). rewrite TK.hvE_reg. apply Hnot.
    exact (find_fst_none _ _ Hf).
Qed.

Lemma bit1_srl : forall r, 0 <= r <= 255 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 r)) (Z_to_bv 64 63) = Z_to_bv 64 (r / 2 mod 2).
Proof.
  intros r Hr. apply RK.w_of_u.
  assert (A : forallb (fun z => Z.eqb (bv_unsigned (alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 z)) (Z_to_bv 64 63))) (z / 2 mod 2)) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. apply Z.eqb_eq. apply A. apply in_map_iff. exists (Z.to_nat r). split; [lia | apply in_seq; lia].
Qed.
Lemma bit_land2 : forall r, 0 <= r <= 255 -> Z.land r 2 = 2 * (r / 2 mod 2).
Proof.
  intros r Hr.
  assert (A : forallb (fun z => Z.eqb (Z.land z 2) (2 * (z / 2 mod 2))) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. apply Z.eqb_eq. apply A. apply in_map_iff. exists (Z.to_nat r). split; [lia | apply in_seq; lia].
Qed.
Lemma g3_bit1_eq : forall r, 0 <= r <= 255 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 r)) (Z_to_bv 64 63) = Z_to_bv 64 0 -> Z.land r 2 = 0.
Proof.
  intros r Hr H. rewrite bit1_srl in H by exact Hr. pose proof (Z.mod_pos_bound (r / 2) 2 ltac:(lia)) as B.
  apply RK.w_inj in H; [| lia | lia]. rewrite bit_land2 by exact Hr. rewrite H. reflexivity.
Qed.
Lemma bit1_ne : forall r, 0 <= r <= 255 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4611686018427387904) (Z_to_bv 64 r)) (Z_to_bv 64 63) <> Z_to_bv 64 0 -> Z.land r 2 <> 0.
Proof.
  intros r Hr H X. apply H. rewrite bit1_srl by exact Hr. rewrite bit_land2 in X by exact Hr. f_equal. lia.
Qed.
Lemma u64r : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.


Ltac hvs_open cp plans off gl pn pr sp0 R Rs M fx model K Hh Hl Hfp H2 Hpins Hpr Hnot :=
  let E := fresh "E" in set (E := TK.hvE sp0 Rs (RK.ghl gl));
  let U := fresh "U2" in assert (U : bv_unsigned (ev E 2) = sp0) by (apply TK.hvE_sp; lia);
  apply (TK.stretch_cps FPM cp fx E R M model K plans Hh Hl Hfp);
  [ apply (regs_ok_sw _ off pn pr); [vm_compute; reflexivity | lia | lia | first [exact H2 | rewrite Z.add_0_r; exact H2] | Hpins | exact Hpr | exact Hnot] | | ].
Ltac hs_keeps HLF Hag64 sp0 Rs E' R' qs pr PR NOT := exact (keeps_sw_sound _ _ sp0 Rs _ E' R' _ _ qs pr _ HLF eq_refl Hag64 eq_refl PR NOT).
Ltac lkeeps HLF Hag64 sp0 Rs x v r S := let x' := rr x in let r' := rr r in tk_reg HLF x'; rewrite <- (proj1 Hag64 v) by lia; rewrite <- S; exact (TK.hvE_reg sp0 Rs _ r').
Ltac w2zg := repeat match goal with |- context [ev ?E ?v] => match goal with U : bv_unsigned (ev E v) = ?z |- _ => rewrite (RK.w_of_u _ _ U) end end.
Ltac pfb HLF PF := probes_in HLF PF; w2z PF; pf_all PF.
Ltac pfc HLF PF := probes_in HLF PF; w2z PF;
  first [let X := fresh "PB" in destruct PF as [X PF]; first [apply g3_bit1_eq in X; [|lia] | apply bit1_ne in X; [|lia]] | idtac];
  pf_all PF.

Lemma s_cd_entry : s_cd_entry_stmt.
Proof.
  unfold s_cd_entry_stmt.
  intros fx R M model K sp1 Rr IS rd p e rav Hh Hl Hfp H2 [Hsp Hal] H10 H1 Rrav [Hr1 Hr2] [Hi1 Hi2] RO C240 Cvt Crd Rrd Hrd1 C288 Ce Cp Rp Re Dfr Hle1 Hle2 HIS Kp Kloop.
  change PML.PC_RCHECK_DONE with (CC.cp_pc GA.cp6).
  hv_open GA.cp6 (GA.plans 6%nat _ eq_refl) 0 [IS; rd; e; p] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - reg_atom E sp1 R 42%nat r_a0 H10. gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rd. gh_atom E sp1 R 66%nat 2%nat e. gh_atom E sp1 R 67%nat 3%nat p.
    unfold know_ok, GA.cp6. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_unk. + e_wr. + e_range.
    + kw64 (Rr + 240) IS C240. + kw64 IS PML.VT_ISS Cvt. + kw32 (IS + 152) rd Crd. + tk_kimg RO.
    + e_range. + e_range. + kw64 (Rr + 288) 0 C288. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
    + e_disj. + e_disj. + e_align HIS.
  - intros fx' E' R' M' kk ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 R 42%nat r_a0 H10. reg_atom E sp1 R 33%nat r_ra H1.
    gh_atom E sp1 R 64%nat 0%nat IS. gh_atom E sp1 R 65%nat 1%nat rd. gh_atom E sp1 R 66%nat 2%nat e. gh_atom E sp1 R 67%nat 3%nat p.
    leaf_open Hag HLF E' 68%nat.
    leaves 3%nat kk Hnth ltac:(pfc HLF PF).
    + apply (Kloop ltac:(lia) fx' R' M' Hfp').
      * llin HLF r_sp.
      * llin HLF r_s1.
      * lkeep HLF Hag64 sp1 R r_s0 43%nat r_a1.
      * llin HLF r_s2.
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KS012.
      * unfold cd_frame. refine (conj _ (conj _ (conj _ _))).
        -- lcell64 HLF (EVar 2) (-8) (EVar 33). cbn [edenot]. assumption.
        -- lcell64 HLF (EVar 2) (-16) (EVar 40). vreg Hag64 sp1 R 40%nat r_s0.
        -- lcell64 HLF (EVar 2) (-24) (EVar 41). vreg Hag64 sp1 R 41%nat r_s1.
        -- lcell64 HLF (EVar 2) (-32) (EVar 50). vreg Hag64 sp1 R 50%nat r_s2.
      * lframe HLF.
      * exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
    + apply (Kp ltac:(lia) fx' R' M' Hfp').
      * llin HLF r_sp.
      * llin HLF r_ra.
      * llin HLF r_a0.
      * lkeep HLF Hag64 sp1 R r_a1 43%nat r_a1.
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KSA.
      * lframe HLF.
      * exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
    + exfalso. lia.
Qed.

Lemma s_cd_r_chunk : s_cd_r_chunk_stmt.
Proof.
  unfold s_cd_r_chunk_stmt.
  intros fx R M model K sp1 Rr Ev code p e p' k Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] H10 H11 Hp0 Hk0 Hpk Hkr Cc Rc Ce Cp Rp Re D Dj Kepi Kc00 Kpcd.
  assert (H8s : getr (sw89 R) 8%bv = Z_to_bv 64 Rr) by (rewrite sw_a by bvne; exact H9).
  assert (H9s : getr (sw89 R) 9%bv = Z_to_bv 64 Ev) by (rewrite sw_b by bvne; exact H8).
  assert (H10s : getr (sw89 R) 10%bv = Z_to_bv 64 p') by (rewrite sw_o by bvne; exact H10).
  assert (H11s : getr (sw89 R) 11%bv = Z_to_bv 64 k) by (rewrite sw_o by bvne; exact H11).
  assert (S18 : getr (sw89 R) 18%bv = getr R 18%bv) by (apply sw_o; bvne).
  change RT.CD_R_CHUNK with (CC.cp_pc GA.cp7).
  hvs_open GA.cp7 (GA.plans 7%nat _ eq_refl) (-32) [code; e; p] (@nil (nat * Z)) PR89 sp1 R (sw89 R) M fx model K Hh Hl Hfp H2 no_pins (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
  - reg_atom E sp1 (sw89 R) 40%nat r_s0 H8s. reg_atom E sp1 (sw89 R) 41%nat r_s1 H9s.
    gh_atom E sp1 (sw89 R) 64%nat 0%nat code. gh_atom E sp1 (sw89 R) 65%nat 1%nat e. gh_atom E sp1 (sw89 R) 66%nat 2%nat p.
    unfold know_ok, GA.cp7. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
    + e_wr. + e_disj.
  - intros fx' E' R' M' kk ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 (sw89 R) 40%nat r_s0 H8s. reg_atom E sp1 (sw89 R) 41%nat r_s1 H9s.
    reg_atom E sp1 (sw89 R) 42%nat r_a0 H10s. reg_atom E sp1 (sw89 R) 43%nat r_a1 H11s.
    gh_atom E sp1 (sw89 R) 64%nat 0%nat code. gh_atom E sp1 (sw89 R) 65%nat 1%nat e. gh_atom E sp1 (sw89 R) 66%nat 2%nat p.
    leaf_open Hag HLF E' 67%nat.
    leaves 4%nat kk Hnth ltac:(pfb HLF PF).
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 40) (EVar 65) (EVar 66). rewrite SAME.
      apply (Kc00 ltac:(lia) ltac:(lia) ltac:(lia) fx' R' Hfp').
      * llin HLF r_sp.
      * llin HLF r_a0.
      * llin HLF r_a1.
      * hs_keeps HLF Hag64 sp1 (sw89 R) E' R' KSA PR89 (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 40) (EVar 65) (EVar 66).
      apply (Kpcd ltac:(lia) fx' R' M' Hfp').
      * llin HLF r_sp.
      * unfold RT.CD_R_PCD. llin HLF r_ra.
      * lkeeps HLF Hag64 sp1 (sw89 R) r_a0 50%nat r_s2 S18.
      * llin HLF r_a1.
      * hs_keeps HLF Hag64 sp1 (sw89 R) E' R' KSA PR89 (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
      * left. split; [lia | split; [lia | exact SAME]].
    + assert (Kn : k <> 0) by lia. assert (C0 : code = 0) by lia. destruct (Hkr Kn) as [[Hq1 Hq2] Hk2].
      assert (L2 : getr R' 2%bv = Z_to_bv 64 (sp1 + -32)) by llin HLF r_sp.
      assert (L8 : getr R' 8%bv = Z_to_bv 64 Ev) by llin HLF r_s0.
      assert (L9 : getr R' 9%bv = Z_to_bv 64 Rr) by llin HLF r_s1.
      assert (L10 : getr R' 10%bv = Z_to_bv 64 p') by llin HLF r_a0.
      assert (L11 : getr R' 11%bv = Z_to_bv 64 k) by llin HLF r_a1.
      assert (L12 : getr R' 12%bv = Z_to_bv 64 0) by (lreg HLF r_a2; w2zg; rewrite RK.ext_s32 by lia; rewrite C0; reflexivity).
      assert (L18 : getr R' 18%bv = getr R 18%bv) by (lreg HLF r_s2; rewrite <- (proj1 Hag64 50%nat) by lia; rewrite <- S18; exact (TK.hvE_reg sp1 (sw89 R) _ 18%bv)).
      assert (KP1 : TK.keepsR KSA R R') by (hs_keeps HLF Hag64 sp1 (sw89 R) E' R' KSA PR89 (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R)).
      assert (C1 : L5.u32_at RSEGS M' Ev code) by (lcell32 HLF (EVar 41) 0 (EVar 64); cbn [edenot]; assumption).
      assert (C2 : L5.u64_at RSEGS M' (Rr + 512) e) by (lcell64 HLF (EVar 40) 512 (EVar 65); cbn [edenot]; assumption).
      assert (C3 : L5.u64_at RSEGS M' (Rr + 520) p) by (lcell64 HLF (EVar 40) 520 (EVar 66); cbn [edenot]; assumption).
      assert (G1 : mem_grows M M') by exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
      assert (D1 : L5.defined M' (Rr + 512) 16) by exact (L5.defined_grows _ _ _ _ G1 D).
      assert (SM1 : TK.samem (fun a => ~ (Rr + 512 <= a < Rr + 528)) M M') by lframe HLF.
      clear Hag64 Hag HLF. rename E into E7.
      assert (H8t : getr (sw89 R') 8%bv = Z_to_bv 64 Rr) by (rewrite sw_a by bvne; exact L9).
      assert (H9t : getr (sw89 R') 9%bv = Z_to_bv 64 Ev) by (rewrite sw_b by bvne; exact L8).
      assert (H10t : getr (sw89 R') 10%bv = Z_to_bv 64 p') by (rewrite sw_o by bvne; exact L10).
      assert (H11t : getr (sw89 R') 11%bv = Z_to_bv 64 k) by (rewrite sw_o by bvne; exact L11).
      assert (S18t : getr (sw89 R') 18%bv = getr R' 18%bv) by (apply sw_o; bvne).
      match goal with |- context [@PML.cfg _ _ ?pc _ _] => change pc with (CC.cp_pc GA.cp10) end.
      hvs_open GA.cp10 (GA.plans 10%nat _ eq_refl) (-32) [code; e; p] (@nil (nat * Z)) PR89Z sp1 R' (sw89 R') M' fx' model K Hh Hl Hfp' L2 no_pins (pr89z sp1 R' (RK.ghl [code; e; p]) L12) (not89z R').
      * reg_atom E sp1 (sw89 R') 40%nat r_s0 H8t. reg_atom E sp1 (sw89 R') 41%nat r_s1 H9t.
        reg_atom E sp1 (sw89 R') 42%nat r_a0 H10t. reg_atom E sp1 (sw89 R') 43%nat r_a1 H11t.
        gh_atom E sp1 (sw89 R') 64%nat 0%nat code. gh_atom E sp1 (sw89 R') 65%nat 1%nat e. gh_atom E sp1 (sw89 R') 66%nat 2%nat p.
        unfold know_ok, GA.cp10. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
        -- e_range. -- e_align Hal. -- e_range. -- e_range. -- kw32 Ev code C1. -- kw64 (Rr + 512) e C2. -- kw64 (Rr + 520) p C3.
        -- e_wr. -- e_disj. -- e_range. -- e_range.
        -- cbn [kentry_ok edenot]. w2zg. rewrite RK.ext_s32 by lia. rewrite u64_of_Z by lia. lia.
      * intros fx2 E2 R2 M2 kk2 ps2 Hnth2 Hag2 HLF2 Hfp2.
        reg_atom E sp1 (sw89 R') 40%nat r_s0 H8t. reg_atom E sp1 (sw89 R') 41%nat r_s1 H9t.
        reg_atom E sp1 (sw89 R') 42%nat r_a0 H10t. reg_atom E sp1 (sw89 R') 43%nat r_a1 H11t.
        gh_atom E sp1 (sw89 R') 64%nat 0%nat code. gh_atom E sp1 (sw89 R') 65%nat 1%nat e. gh_atom E sp1 (sw89 R') 66%nat 2%nat p.
        leaf_open Hag2 HLF2 E2 67%nat.
        leaves 1%nat kk2 Hnth2 ltac:(idtac).
        apply (Kpcd C0 fx2 R2 M2 Hfp2).
        -- llin HLF2 r_sp.
        -- unfold RT.CD_R_PCD. llin HLF2 r_ra.
        -- lreg HLF2 r_a0. rewrite <- (proj1 Hag64 50%nat) by lia. rewrite <- L18. rewrite <- S18t. exact (TK.hvE_reg sp1 (sw89 R') _ 18%bv).
        -- llin HLF2 r_a1.
        -- apply (TK.keepsR_trans _ _ R' _ KP1). hs_keeps HLF2 Hag64 sp1 (sw89 R') E2 R2 KSA PR89 (pr89 sp1 R' (RK.ghl [code; e; p])) (not89 R').
        -- right. refine (conj Kn (conj _ (conj _ (conj _ _)))).
           ++ lcell64 HLF2 (EVar 40) 512 (EAlu ALU_ADD (EVar 42) (EVar 43)). vlin.
           ++ lcell64 HLF2 (EVar 40) 520 (EVar 42). cbn [edenot]. assumption.
           ++ apply (TK.samem_trans _ _ M'); [exact SM1 | lframe HLF2].
           ++ exact (mem_grows_trans _ _ _ G1 (CC.lf_grows _ _ _ _ _ _ _ HLF2)).
    + lsame HLF M M' (Rr + 512) e p D Ce Cp (EVar 40) (EVar 65) (EVar 66). rewrite SAME.
      apply (Kepi ltac:(lia) fx' R' Hfp').
      * llin HLF r_sp.
      * hs_keeps HLF Hag64 sp1 (sw89 R) E' R' KSA PR89 (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
Qed.

Lemma s_cd_r_pcd : s_cd_r_pcd_stmt.
Proof.
  unfold s_cd_r_pcd_stmt.
  intros fx R M model K sp1 Rr Ev code p e Hh Hl Hfp H2 [Hsp Hal] H9 H8 [Hr1 Hr2] [He1 He2] Cc Rc Ce Cp Rp Re Kepi Kc00.
  assert (H8s : getr (sw89 R) 8%bv = Z_to_bv 64 Rr) by (rewrite sw_a by bvne; exact H9).
  assert (H9s : getr (sw89 R) 9%bv = Z_to_bv 64 Ev) by (rewrite sw_b by bvne; exact H8).
  change RT.CD_R_PCD with (CC.cp_pc GA.cp8).
  hvs_open GA.cp8 (GA.plans 8%nat _ eq_refl) (-32) [code; e; p] (@nil (nat * Z)) PR89 sp1 R (sw89 R) M fx model K Hh Hl Hfp H2 no_pins (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
  - reg_atom E sp1 (sw89 R) 40%nat r_s0 H8s. reg_atom E sp1 (sw89 R) 41%nat r_s1 H9s.
    gh_atom E sp1 (sw89 R) 64%nat 0%nat code. gh_atom E sp1 (sw89 R) 65%nat 1%nat e. gh_atom E sp1 (sw89 R) 66%nat 2%nat p.
    unfold know_ok, GA.cp8. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + e_range. + kw32 Ev code Cc. + kw64 (Rr + 512) e Ce. + kw64 (Rr + 520) p Cp.
  - intros fx' E' R' M' kk ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 (sw89 R) 40%nat r_s0 H8s. reg_atom E sp1 (sw89 R) 41%nat r_s1 H9s.
    gh_atom E sp1 (sw89 R) 64%nat 0%nat code. gh_atom E sp1 (sw89 R) 65%nat 1%nat e. gh_atom E sp1 (sw89 R) 66%nat 2%nat p.
    leaf_open Hag HLF E' 67%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 2%nat kk Hnth ltac:(pfb HLF PF).
    + apply (Kc00 ltac:(lia) fx' R' Hfp').
      * llin HLF r_sp.
      * llin HLF r_a0.
      * llin HLF r_a1.
      * hs_keeps HLF Hag64 sp1 (sw89 R) E' R' KSA PR89 (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
    + apply (Kepi ltac:(lia) fx' R' Hfp').
      * llin HLF r_sp.
      * hs_keeps HLF Hag64 sp1 (sw89 R) E' R' KSA PR89 (pr89 sp1 R (RK.ghl [code; e; p])) (not89 R).
Qed.

Lemma s_cd_c00 : s_cd_c00_stmt.
Proof.
  unfold s_cd_c00_stmt.
  intros fx R M model K sp1 Rr IS rdb a0v a1v Hh Hl Hfp H2 [Hsp Hal] H9 [Hr1 Hr2] [Hi1 Hi2] RO H10 H11 Ra0 Ra1 C288 C240 Cvt Crd Rrd HIS Kloop Kepi.
  assert (H8s : getr (sw4 R) 8%bv = Z_to_bv 64 Rr) by (rewrite sw_o by bvne; rewrite sw_a by bvne; exact H9).
  assert (H10s : getr (sw4 R) 10%bv = Z_to_bv 64 a1v) by (rewrite sw_a by bvne; rewrite sw_o by bvne; exact H11).
  assert (H11s : getr (sw4 R) 11%bv = Z_to_bv 64 a0v) by (rewrite sw_b by bvne; rewrite sw_o by bvne; exact H10).
  change RT.CD_C00 with (CC.cp_pc GC.cp0).
  hvs_open GC.cp0 (GC.plans 0%nat _ eq_refl) (-32) [IS; rdb] (@nil (nat * Z)) PR4 sp1 R (sw4 R) M fx model K Hh Hl Hfp H2 no_pins (pr4 sp1 R (RK.ghl [IS; rdb])) (not4 R).
  - reg_atom E sp1 (sw4 R) 40%nat r_s0 H8s. gh_atom E sp1 (sw4 R) 64%nat 0%nat IS. gh_atom E sp1 (sw4 R) 65%nat 1%nat rdb.
    unfold know_ok, GC.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal. + e_range. + kw64 (Rr + 288) 0 C288. + kw64 (Rr + 240) IS C240. + kw64 IS PML.VT_ISS Cvt.
    + kw8 (IS + 152) rdb Crd. + tk_kimg RO. + e_range. + e_range. + e_align HIS.
  - intros fx' E' R' M' kk ps Hnth Hag HLF Hfp'.
    reg_atom E sp1 (sw4 R) 40%nat r_s0 H8s. reg_atom E sp1 (sw4 R) 42%nat r_a0 H10s. reg_atom E sp1 (sw4 R) 43%nat r_a1 H11s.
    gh_atom E sp1 (sw4 R) 64%nat 0%nat IS. gh_atom E sp1 (sw4 R) 65%nat 1%nat rdb.
    leaf_open Hag HLF E' 66%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 3%nat kk Hnth ltac:(pfc HLF PF).
    + apply (Kloop ltac:(right; lia) fx' R' Hfp').
      * llin HLF r_sp.
      * hs_keeps HLF Hag64 sp1 (sw4 R) E' R' KSA PR4 (pr4 sp1 R (RK.ghl [IS; rdb])) (not4 R).
    + apply (Kepi ltac:(lia) ltac:(lia) fx' R' Hfp').
      * llin HLF r_sp.
      * hs_keeps HLF Hag64 sp1 (sw4 R) E' R' KSA PR4 (pr4 sp1 R (RK.ghl [IS; rdb])) (not4 R).
    + apply (Kloop ltac:(left; lia) fx' R' Hfp').
      * llin HLF r_sp.
      * hs_keeps HLF Hag64 sp1 (sw4 R) E' R' KSA PR4 (pr4 sp1 R (RK.ghl [IS; rdb])) (not4 R).
Qed.

Lemma s_rn_epi : s_rn_epi_stmt.
Proof.
  unfold s_rn_epi_stmt.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] [F1 [F2 [F3 [F4 [F5 [F6 [F7 F8]]]]]]] [Hra1 Hra2] Kc.
  pose proof (u64r (getr R0 8%bv)) as B8. pose proof (u64r (getr R0 9%bv)) as B9. pose proof (u64r (getr R0 18%bv)) as B18.
  pose proof (u64r (getr R0 19%bv)) as B19. pose proof (u64r (getr R0 20%bv)) as B20. pose proof (u64r (getr R0 21%bv)) as B21. pose proof (u64r (getr R0 22%bv)) as B22.
  change RT.RN_EPI with (CC.cp_pc GD.cp0).
  hv_open GD.cp0 (GD.plans 0%nat _ eq_refl) (-64) [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv); bv_unsigned (getr R0 19%bv); bv_unsigned (getr R0 20%bv); bv_unsigned (getr R0 21%bv); bv_unsigned (getr R0 22%bv)] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - unfold know_ok, GD.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + kw64 (sp1 - 8) rav F1. + kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2.
    + kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
    + kw64 (sp1 - 40) (bv_unsigned (getr R0 19%bv)) F5. + kw64 (sp1 - 48) (bv_unsigned (getr R0 20%bv)) F6.
    + kw64 (sp1 - 56) (bv_unsigned (getr R0 21%bv)) F7. + kw64 (sp1 - 64) (bv_unsigned (getr R0 22%bv)) F8.
  - intros fx' E' R' M' kk ps Hnth Hag HLF Hfp'.
    gh_atom E sp1 R 64%nat 0%nat rav. gh_atom E sp1 R 65%nat 1%nat (bv_unsigned (getr R0 8%bv)).
    gh_atom E sp1 R 66%nat 2%nat (bv_unsigned (getr R0 9%bv)). gh_atom E sp1 R 67%nat 3%nat (bv_unsigned (getr R0 18%bv)).
    gh_atom E sp1 R 68%nat 4%nat (bv_unsigned (getr R0 19%bv)). gh_atom E sp1 R 69%nat 5%nat (bv_unsigned (getr R0 20%bv)).
    gh_atom E sp1 R 70%nat 6%nat (bv_unsigned (getr R0 21%bv)). gh_atom E sp1 R 71%nat 7%nat (bv_unsigned (getr R0 22%bv)).
    leaf_open Hag HLF E' 72%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 1%nat kk Hnth ltac:(idtac).
    assert (HR1 : getr R' 1%bv = Z_to_bv 64 rav) by llin HLF r_ra.
    unfold PML.cfg. apply (CL.ret_cps RSEGS fx' R' RT.RN_RET M model K ret_rn Hh Hl).
    + rewrite HR1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hra2.
    + rewrite HR1. apply (Kc fx' R' Hfp').
      * llin HLF r_sp.
      * unfold same_s06. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
          [lreg HLF r_s0 | lreg HLF r_s1 | lreg HLF r_s2 | lreg HLF r_s3 | lreg HLF r_s4 | lreg HLF r_s5 | lreg HLF r_s6]; apply bv_eq; assumption.
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KS06.
Qed.

Lemma s_cd_epi : s_cd_epi_stmt.
Proof.
  unfold s_cd_epi_stmt.
  intros fx R M model K sp1 rav R0 Hh Hl Hfp H2 [Hsp Hal] [F1 [F2 [F3 F4]]] [Hra1 Hra2] Kc.
  pose proof (u64r (getr R0 8%bv)) as B8. pose proof (u64r (getr R0 9%bv)) as B9. pose proof (u64r (getr R0 18%bv)) as B18.
  change RT.CD_EPI with (CC.cp_pc GD.cp1).
  hv_open GD.cp1 (GD.plans 1%nat _ eq_refl) (-32) [rav; bv_unsigned (getr R0 8%bv); bv_unsigned (getr R0 9%bv); bv_unsigned (getr R0 18%bv)] (@nil (nat * Z)) sp1 R M fx model K Hh Hl Hfp H2 no_pins.
  - unfold know_ok, GD.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align Hal.
    + kw64 (sp1 - 8) rav F1. + kw64 (sp1 - 16) (bv_unsigned (getr R0 8%bv)) F2.
    + kw64 (sp1 - 24) (bv_unsigned (getr R0 9%bv)) F3. + kw64 (sp1 - 32) (bv_unsigned (getr R0 18%bv)) F4.
  - intros fx' E' R' M' kk ps Hnth Hag HLF Hfp'.
    gh_atom E sp1 R 64%nat 0%nat rav. gh_atom E sp1 R 65%nat 1%nat (bv_unsigned (getr R0 8%bv)).
    gh_atom E sp1 R 66%nat 2%nat (bv_unsigned (getr R0 9%bv)). gh_atom E sp1 R 67%nat 3%nat (bv_unsigned (getr R0 18%bv)).
    leaf_open Hag HLF E' 68%nat. rewrite (TK.frame_nil _ _ _ _ _ _ HLF eq_refl).
    leaves 1%nat kk Hnth ltac:(idtac).
    assert (HR1 : getr R' 1%bv = Z_to_bv 64 rav) by llin HLF r_ra.
    unfold PML.cfg. apply (CL.ret_cps RSEGS fx' R' RT.CD_RET M model K ret_cd Hh Hl).
    + rewrite HR1. apply Hoare.ret_ok_even. rewrite u64_of_Z by lia. exact Hra2.
    + rewrite HR1. apply (Kc fx' R' Hfp').
      * llin HLF r_sp.
      * unfold same_s02. refine (conj _ (conj _ _)); [lreg HLF r_s0 | lreg HLF r_s1 | lreg HLF r_s2]; apply bv_eq; assumption.
      * hv_keeps HLF Hag64 sp1 R E' R' M M' KS012.
Qed.


End S.
End RS.
