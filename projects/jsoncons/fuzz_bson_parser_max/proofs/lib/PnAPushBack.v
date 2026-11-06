(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5DefsA L5CoreA
     PmLayout PnLayout PnLayoutA PmModel PmSpecsA PnSpecsAa PnRunA PnRunAa PnAPushBack1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNAPB.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.

Theorem str_push_back_ok : PMA.opnew_spec L ar HI -> PMA.opdel_spec L ar HI -> PNRAa.str_push_back_spec L ar HI.
Proof.
  intros OPN OPD. unfold PNRAa.str_push_back_spec, PNRA.str_push_back_spec.
  intros fx R M model K LB FF LK Aw cr o c sp r tg x HH AM K0 ENT FRM FRS A10 A11 Hc AO O8 VS TBOK SZ CR KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in ASTK.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  cbn [PNL.pn_str_push_back PMA.AN NADDR_A].
  exact (PNAPB1.pb_entry L ar C IL HI LY HIok ICok ILY R M model K LB FF LK Aw cr o c sp r tg x Rra RAok Rsp Rtp K0 ASTK AO O8 Hc A11 SZ OPN OPD KONT
           fx AM HH A10 VS TBOK CR).
Qed.
End WithHeap.
End PNAPB.
