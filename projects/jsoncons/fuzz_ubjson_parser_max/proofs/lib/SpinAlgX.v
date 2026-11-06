(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SpinAlgX () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2eq"; "3le"; "4firstn"; "5Z"; "6len_word"; "7Segment"; "8machine_state"]; ["8ms_gpr"; "8ms_read_bytes"; "8ms_svc_pending"; "8set_gpr0"; "9SpuriousCfg"; "9advance_past_svc"; "9mkCfg"; ":Model"; ":m_halted"; ":m_vm_lazy"; ";fd32"; "<buf_modeled"; "<fdchan"; "=TSet"; "=t_write_ch"; ">srealizes"]; ["0T"; "0buf"; "0ch"; "0fd"; "0model"; "0ms"; "0n"; "0scfg"; "0segs"; "?bv"; "?bv_unsigned"; "0x8"]]).
Lemma srz_write_ch : ltac2:(TCodec.tc2 tcn__SpinAlgX "SM'4'>%211'D'?'G'Q9yR0%211y8%411%;11&M'9'7%117&Hr6%211(0%11<%83631'8%12??%H11&Ir7%211(6%116%A3631&Lr8%237@1&J%113%G3L14&Br;%211(2%12Q1?%M3K31'<&Q:%12Q6=+R0%Q23421&@r=(1%3221%Q73Q<1>%Q71Q:&Ar>u1%9221u2%;241%63531r9%F2QC1%QB3:31&Kr:%211':&3%12QKO%32>1'5r1%62A1r2%72R1D%9221'OrFrE(F&E&CrD&=&;r3r?%33R>21%52R?1%8271%:11rC%=221%A4@?1Q7p0C1p0G1pR>J1rBrA%D221&Nr<%23@QF1%K4E<41p081p0Q41p0Q91p0Q=1p0QI1p0QO1p0R51p0R<1p0R@1p0RD1p0RN1pR2S81pR4S:1pRHS>1pR6S?1pR8S@1pR:SD1pR<SF1pR@SH1pRBSJ1").
Proof.
intros segs scfg ms model fd ch x8 buf T Hh Hlazy Hfdc H32 Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (srz_node segs scfg (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- eapply node_write_ch; eassumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
