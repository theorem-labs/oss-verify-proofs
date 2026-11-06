(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 L5Defs L5Core L5CoreKit L5DefsAB0 L5CoreAB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmSpecsA PeSpecsAb HeapIfaceAEx PeBResize3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMBRZ.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem str_resize_ok : PMB.opnew_spec L ar HI -> PMB.opdel_spec L ar HI -> PMB.str_resize_spec L ar HI.
Proof.
  intros OPN OPD. unfold PMB.str_resize_spec, PMSPA.str_resize_spec.
  intros fx R M model K LB FF LK Aw cr o n sp r tg s HH AM K0 ENT FRM FRS A10 A11 AO O8 VS TBOK Hn1 Hn2 CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in ASTK.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  cbn [pa_str_resize PMB.AD ADDR_B].
  exact (PMBRZ3.resize_entry L ar C IL HI LY HIok ICok ILY R M model K LB FF LK Aw cr o n sp r tg s Rra RAok Rsp Rtp K0 ASTK AO O8 Hn1 Hn2 OPN OPD KONT
           fx AM HH A10 A11 VS TBOK CR).
Qed.
End WithHeap.
End PMBRZ.
