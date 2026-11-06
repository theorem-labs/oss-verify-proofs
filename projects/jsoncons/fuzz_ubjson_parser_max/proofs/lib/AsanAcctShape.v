(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct SpinAlg.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanAcctShape () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "stdpp.bitvector.definitions."], [["0A"; "1None"; "1list"; "1option"; "1prod"; "2eq"; "3Z"; "0H"; "4MachineOk"; "4machine_result"; "4machine_state"; "4ms_mem"; "4ms_svc_pending"; "4step"; "5mkCfg"; "6Model"]; ["6m_halted"; "6m_vm_lazy"; "7A_wf"; "7MInv"; "7hclean"; "7lazy_cover"; "7restrict"; "7same_but_materialized"; "7unrestrict"; "8msteps"; "9TSet"; "9realizes"; ":srealizes"; "0T"; "0model"; "0model'"]; ["0ms"; "0msr'"; "0scfg"; "0segs"; ";bv"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.
Lemma node_ok_same : AsanAcct.node_ok segs = ShapeAlg.pnode_ok segs.
Proof. reflexivity. Qed.
Let P_of (T : TSet) : config -> Prop := fun c => realizes segs scfg c T.
Let P_of_silent1 (T : TSet) : forall c c',
ms_svc_pending (cfg_ms c) = None ->
AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
P_of T c' -> P_of T c :=
fun c c' Hsvc Hn Hr => rz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.
Theorem rz_step_restricted_T : ltac2:(TCodec.tc2 tcn__AsanAcctShape "RC'2'4'6%2211%411':'?&J&Ev7&Ar2%211r5%63521&Br6%211'Cr7r4%3221'5'3'Q4yR0%211%411&@%11@(1%115%:3531&<r8%211%>3915'9%11Q1&=vQ3&Fr9%22Q21%5241(8%12Q9<%I3931r<r1%Q0221&Gr:%221Q:'KvQ2(>&H&;r=%211%43QD1=r3%7221%:4H91<p0<1p0@1pR0QM1r;%=21K%@4N?1Q4p041p0I1p0Q51p0Q:1p0QF1p0QK1p0QO1pQLR71pQNR91pR4R;1pR2R<1p2R>1").
Proof.
intros A ms msr' model T.
exact (rz_step_restricted segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
Theorem rz_msteps_restricted_T : ltac2:(TCodec.tc2 tcn__AsanAcctShape "R<'2'4'6%2211%411':'?&J&Ev7&Ar2%211r5%63521&Br6%211'Cr7r4%3221'5'3'Q4yR0%211%411&@%11@(1%115%:3531'IvQ3&Fr8%22L1%5341Cr;r1%G221&Gr9%221Q1&D%12Q57'KvQ2(>&H&;r=%211r<%53Q>21%721Q4r:%;4H:21p0=1p0@1p0D1pR0QH1%>26K%A4N@1Q=p031p0L1p0Q31p0Q?1p0QD1p0QH1pQLR01pQNR21pR4R41pR2R51p2R71").
Proof.
intros A ms msr' model T.
exact (rz_msteps_restricted' segs H HH Hwx (P_of T) (P_of_silent1 T) A ms msr' model).
Qed.
Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs scfg c T.
Let SP_of_silent1 (T : TSet) : forall c c',
ms_svc_pending (cfg_ms c) = None ->
AsanAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
SP_of T c' -> SP_of T c :=
fun c c' Hsvc Hn Hr => srz_silent1 segs scfg c c' T (node_ok_of_pnode_instr segs scfg c _ _ _ Hsvc Hn) Hr.
Theorem srz_step_restricted_T : ltac2:(TCodec.tc2 tcn__AsanAcctShape "RC'2'4'6%2211%411':'?&J&Ev7&Ar2%211r5%63521&Br6%211'Cr7r4%3221'5'3'Q4yR0%211%411&@%11@(1%115%:3531&<r8%211%>3915'9%11Q1&=vQ3&Fr9%22Q21%5241(8%12Q9<%I3931r<r1%Q0221&Gr:%221Q:'LvQ2(>&H&;r=%211%43QD1=r3%7221%:4H91<p0<1p0@1pR0QM1r;%=21K%@4N?1Q4p041p0I1p0Q51p0Q:1p0QF1p0QK1p0QO1pQLR71pQNR91pR4R;1pR2R<1p2R>1").
Proof.
intros A ms msr' model T.
exact (rz_step_restricted segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
Theorem srz_msteps_restricted_T : ltac2:(TCodec.tc2 tcn__AsanAcctShape "R<'2'4'6%2211%411':'?&J&Ev7&Ar2%211r5%63521&Br6%211'Cr7r4%3221'5'3'Q4yR0%211%411&@%11@(1%115%:3531'IvQ3&Fr8%22L1%5341Cr;r1%G221&Gr9%221Q1&D%12Q57'LvQ2(>&H&;r=%211r<%53Q>21%721Q4r:%;4H:21p0=1p0@1p0D1pR0QH1%>26K%A4N@1Q=p031p0L1p0Q31p0Q?1p0QD1p0QH1pQLR01pQNR21pR4R41pR2R51p2R71").
Proof.
intros A ms msr' model T.
exact (rz_msteps_restricted' segs H HH Hwx (SP_of T) (SP_of_silent1 T) A ms msr' model).
Qed.
End WithSegs.
End FPX_1.
