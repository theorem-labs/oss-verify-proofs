(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ExitSim PropExec CatSim CatExec SeqExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__StreamExec () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2I"; "2eq"; "2or"; "3Segment"]; ["4Build_machine_state"; "4machine_state"; "4write_to_mem"; "5advance_past_svc"; "5apply_effect"; "6MemCopy"; "6mkEffectU"; "7delivered_writes"; "8bvmap"; "9c_lts"; "9fp_csr"; "9fp_regs"; "9mkst"; "9rdn"; "9regupd"; "9v_addi"]; ["9v_lui"; ":add"; ":le"; ":lt"; ":of_nat"; ":pow"; "0a"; "0buf"; "0data"; "0fx"; "0m"; "0mem"; "0n"; "0pc"; "0regs"; "0ret"]; ["0rom"; "0segs"; ";BV"; ";Z_to_bv"; ";bv"; ";bv_unsigned"; "0sv"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma v_lui_4096 : ltac2:(TCodec.tc2 tcn__StreamExec ":'='QDyR0%211&Q0+TP0%211&QC%1263%93631").
Proof. reflexivity. Qed.
Lemma c_lts_0_0 : ltac2:(TCodec.tc2 tcn__StreamExec ":'='2&I&QCyR0z%3221%5211(4%93821").
Proof. reflexivity. Qed.
Lemma write_to_mem_below : ltac2:(TCodec.tc2 tcn__StreamExec "Q;'6'QDy8%211%411yR0%511'9%115p031&Q2&Q1&QEr2%2291&Q4&5r4%22?1%411%9261&Q5+2+R0%3221%?251&Q3r3%@2G1%32?1'=&Br5r6%342A17%318%63L21p081p0=1pR>Q11pR@Q21pRHQ01pRBQ61").
Proof.
intros data mem buf a Hnw Ha.
rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.
Lemma write_to_mem_above : ltac2:(TCodec.tc2 tcn__StreamExec "Q4'6'QDy8%211%411yR0%511'9%115p031&Q2&Q1&QEr2%2291&Q4&5r4%22?1%411%9261r1%:2A1%=231'=&Br3r5%34;21?%<1@%63F21p081pR>J1pR@K1pRHI1pRBO1").
Proof.
intros data mem buf a Ha.
rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.
Lemma rdn_wtm_out : ltac2:(TCodec.tc2 tcn__StreamExec "R3'6'?%211'QDy8%211%611yR0%511'9%115p031'7&Q2&Q1&QEr2%22:1&Q4r1%211%7241&Q5+2+R0%3221%=251r4%=2E1&5r6%22J1%>11%C251%E219'>r5%F2N1r7%:2Q21%F11%K241%M21>r3%J11%O2A1%Q1219%<251'=%Q81Q;&Mr9&Br8%23@H1%5441CL%645BDM%93821p0;1p0I1p0Q21pRJQA1pR>QF1pR@QG1pRFQE1pRBQK1pS4R01").
Proof.
intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
intros x Hx. destruct Hd as [Hd | Hd].
- apply write_to_mem_above. lia.
- apply write_to_mem_below; [exact Hnb | lia].
Qed.
Lemma rdn_write_to_mem : ltac2:(TCodec.tc2 tcn__StreamExec "Q>'6'?%211'QDy8%211%611yR0%511'9%115p031&Q2&Q1&QEr1%2291&Q4&5r3%22?1%411%9261&Q5+2+R0%3221%?251'=%D1G&Mr5&Br2r4%33@21%B2O2%746241(1%12Q15%<3;31p0>1pR@Q21pRHQ01pRBQ61pS4Q;1").
Proof.
intros segs data mem buf Hnw.
rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.
Lemma adv_apply_write : ltac2:(TCodec.tc2 tcn__StreamExec "R<&Hy5'QDyR0%211%5241'9%113y8%711%411p071'6%114'='A&C&D(@r8&KvQ9%211r7r6(0%11F&J%117r5r4%=8<9875321(Fr3(3';%12Q0G(:r2r1%34Q4K21(8%116%93731%92Q8Q8%411'E%611'7%>2Q=1%911%C6B86641%Q32E1%Q511&L&N(QB+:(<%33QJ21%53Q91K&O+4%22Q81&B%13Q4KJ%<5Q=631Q4%QE3QD>1pRBQG1pR@R11pS0R21pS2QL1pRHQM1pS>R21pRLR61pRNR61").
Proof.
intros regs pc sv mem rom ret buf data.
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
apply_zeros apply_unmaps apply_writes].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma adv_apply_delivered : ltac2:(TCodec.tc2 tcn__StreamExec "R8&Hy5'QDyR0%211%5241'9%113y8%711%411p071'6%114'='A&C&D(@r8&KvQ9%211r7r6(0%11F&J%117r5r4%=8<9875321(Fr3&Gr2r1%3221(8';%12Q4Q4%311'E%511'7%62Q91%811%?6>:6641%O2A1%Q111&L&N(QB+:(<%33QF21%53Q51G&O+4%22Q41&B%13Q0JI%<5Q9631Q0%QA3Q@>1pRBQC1pR@QM1pS0QN1pS2QH1pRHQI1pS>QN1pRLR21pRNR21").
Proof.
intros regs pc sv mem rom ret buf data.
destruct data as [|b rest]; [|apply adv_apply_write].
unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
apply_zeros apply_unmaps apply_writes
delivered_writes write_to_mem].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
End WithFP1.
