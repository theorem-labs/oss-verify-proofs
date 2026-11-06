(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU PmStep PmFrame PmUResize1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMURZ.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Theorem str_resize_ok : PMU.opnew_spec L HI -> PMU.opdel_spec L HI -> PMU.str_resize_spec L HI.
Proof.
intros OPN OPD. unfold PMU.str_resize_spec, PMSP.str_resize_spec.
intros fx R M model K LB cr o n sp r tg s HH MOK K0 ENT A10 A11 Ho1 Ho2 Ho3 VS TBOK Hn1 Hn2 CR KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
change (PMSP.pm_scr 1) with 14336 in *.
assert (BRLB : PMFR.brange L LB).
{ apply (PMFR.brange_of_heap L HI HIok _ LB cr M _ HH). intros x Hx. apply in_or_app. right. exact Hx. }
cbn [pa_str_resize PmLayoutU.ADDR_U] in *.
exact (PMURZ1.resize_entry L HI LY HIok R M model K LB cr o n sp r tg s Rra RAok Rsp Rtp K0 STK Ho1 Ho2 Ho3 Hn1 Hn2 BRLB OPN OPD KONT
fx MOK HH A10 A11 VS TBOK CR).
Qed.
End WithHeap.
End PMURZ.
