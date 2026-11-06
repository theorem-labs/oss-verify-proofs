(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA IcptIfaceA LibIface L5Defs L5DefsA L5CoreA PmLayoutA PmModel PmStaticsA HeapIfaceAJx
PmSpecsA PmSpecsAX PmSpecsAa PmSRdValD PmARvK PmARvE PmARvQ PmARvR PmARvH2 PmARvA.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmARdVal () := ([""; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAa.PMA."], [["0HI"; "0L"; "1begin_array_spec"; "1begin_object_spec"; "1get_length_spec"; "1is_base10_spec"; "1make_ec_spec"; "1read_span_spec"; "1read_value_spec"; "1src_read_spec"; "1validate_spec"; "0SCFG_P"; "0ar"]]).
Module PMARV.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithHeap.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Theorem read_value_ok : ltac2:(TCodec.tc2 tcn__PmARdVal "N&9v;v1v<v0%544321&4%146543&7%148765&:%14:987&5%14<;:9&2%14>=<;&3%14@?>=&6%14BA@?&8%14DCBAp031p061p091p0<1p0?1p0B1p0E1p0H1").
Proof.
intros SR GL RS VAL B10 BA BO MKE.
apply (PMARVE.rv_entry L ar C HI LY HIok).
intros E X fx Rc Mc modelc LKc crc Ac t ST Ht R23 R12.
destruct (PMSRVD.rv_split t Ht) as [Q|[R|[S|A]]].
- exact (PMARVQ.rv_partQ L ar C HI LY HIok IL ICok ILY MKE E X fx Rc Mc modelc LKc crc Ac t ST Q R23 R12).
- exact (PMARVR.rv_partR L ar C HI LY HIok IL ICok ILY MKE SR VAL E X fx Rc Mc modelc LKc crc Ac t ST R R23 R12).
- exact (PMARVH2.rv_partS L ar C HI LY HIok IL ICok ILY MKE GL RS VAL B10 E X fx Rc Mc modelc LKc crc Ac t ST S R23 R12).
- exact (PMARVA.rv_partA L ar C HI LY HIok IL ICok ILY BA BO E X fx Rc Mc modelc LKc crc Ac t ST A R23 R12).
Qed.
End WithHeap.
End SCFG_1.
End PMARV.
