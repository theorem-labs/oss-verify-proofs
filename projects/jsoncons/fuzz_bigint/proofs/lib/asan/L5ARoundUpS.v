(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA
     L5Defs L5Core L5LazyA L5DefsA L5CoreA L5CoreSpecsA L5ARoundUp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5ARUS.
Import L5A. Import L5CA. Import L5CSA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Theorem roundup_ok : roundup_spec L ar HI.
Proof.
  intros fx R M model K LB FF LK cr A i sp r HH [Hh MI] HK G10 Hi G1 RA G2 A32 G4 STK ROOM RS KONT.
  apply (L5ARU.aroundup_ok L ar C HI LY HIok fx R M model LB FF LK cr A i sp r K HH Hh MI G10 Hi G1 RA G2 A32 G4).
  - exact STK.
  - exact ROOM.
  - intros f Hf. specialize (RS f Hf). unfold L5ARU.ARU_FRAME. lia.
  - exact HK.
  - intros fx' R' M' model' LK' A10 RP PRES RT MI' LKI HH'. apply (KONT fx' R' M' model' LK' A10 RP).
    + destruct PRES as [P D]. split. { intros a (Ha & Hc & _). apply P. exact Ha. exact Hc. }
      split. { intros j Hj. apply D. unfold ROUNDUP_SCR, SM_SCR, L5ARU.ARU_SCR in *. lia. }
      intros a Ha Hc HM. rewrite P. exact HM. exact Ha. exact Hc.
    + exact RT.
    + split. rewrite (L5LZ.model_rt_halted _ _ RT). exact Hh. exact MI'.
    + exact LKI.
    + exact HH'.
Qed.
End SCFG_1.
End L5ARUS.
