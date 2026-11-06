(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__As0StepLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "2eq"; "3Z"; "4bytes_le_to_Z"; "5Segment"; "6MachineOk"; "6fetch_word"; "6is_ecall"; "6machine_result"; "6machine_state"]; ["6step"; "6word_to_le_bytes"; "7decode_any"; "8Fence"; "8FenceI"; "8instr"; "9bvmap"; ":mkst"; ":v_addi"; ";lt"; ";pow"; "0a"; "0b"; "0c"; "0d"; "0e"]; ["0fx"; "0mem"; "0pc"; "0regs"; "0rom"; "0segs"; "<bv"; "<bv_unsigned"; "0v"; "0w"]]).
Section FPX. Context {fx : PropExec.FPState}.
Lemma step_fence : ltac2:(TCodec.tc2 tcn__As0StepLib "RE'3':%211&Fy5'Q6yR0%211%5241'4y8%611%311p061yQ0%:11y4%<11%=1>'7%;15&<r;r9%3221(0r6%22<1%93841'1&=r7%211(2%?3521'6'E'8%3221%N11&Br8%211(5(Cr5r4r3%45AF321+4%74>=21%J2=1%Q13=:1'>'?%211&@r>&GvQ0r=r<r:%55432Q91%8271(;&H%126B%:5981Q>6%42?1%QC3?61p0C1p0Q61p0Q=1pR0QH1pQNQI1pQLQK1pQJQL1pQHQM1pRDR01pR:R31pR4R41pR6R;1pR8R;1pR<RB1").
Proof.
intros segs regs pc mem rom w a b c d e Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
rewrite ?b_npc4; reflexivity.
Qed.
Lemma step_fencei : ltac2:(TCodec.tc2 tcn__As0StepLib "RA'3':%211&Fy5'Q6yR0%211%5241'4y8%611%311p061yQ0%:11%;1<y<%=11'7%;15&<r9r7%3221(0r4%22<1%93841'1&=r5%211(2%?3521'6'E'8%3221%N11&Br6%211(5(Dr3%23?D1+4%54<;21%H2;1%O3;81'>'?%211&@r<&GvQ0r;r:r8%55432Q71%8271(;&H%126B%:5981Q<6%42?1%QA3?61p0C1p0Q41p0Q;1pQLQF1pQJQI1pQHQJ1pRDQL1pR:QO1pR4R01pR6R71pR8R71pR<R>1").
Proof.
intros segs regs pc mem rom w a b c Hfetch Hecall Hdecode.
step_pipeline Hfetch Hecall Hdecode.
rewrite ?b_npc4; reflexivity.
Qed.
Lemma bytes_le_to_Z_4 : ltac2:(TCodec.tc2 tcn__As0StepLib "H'Q6yR0%211&I&Q7r1%2251&J+2+Q0%3221%8251'7'8&9&Au4r2%3221%511%@2C3%93821p0;1pRBE1").
Proof.
intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
apply Z.mod_small. pose proof (u64_range v). lia.
Qed.
End FPX.
Ltac stepfence F D :=
chain_step; [reflexivity | eapply step_fence; [exact F | reflexivity | exact D] | step_simpl].
Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
Ltac addr_lit lit :=
match goal with |- rdn _ _ ?ad _ = _ =>
replace ad with lit by (gres; rwH; imm_norm; apply bv_eq; vm_compute; reflexivity) end.
Ltac mlb F D lit HYP :=
chain_step; [reflexivity | eapply step_lb; [exact F | reflexivity | exact D | addr_lit lit; exact HYP] | step_simpl; vnorm].
Ltac mlbu F D lit HYP :=
chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | addr_lit lit; exact HYP] | step_simpl; vnorm].
Ltac mlw F D lit HYP :=
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 _); [exact F | reflexivity | exact D | addr_lit lit; exact HYP | apply bytes_le_to_Z_4; first [lia | rewrite u_Z2bv by lia; lia | vm_compute; first [reflexivity | lia] ] ] | step_simpl; vnorm].
Ltac mld F D lit HYP :=
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 _); [exact F | reflexivity | exact D | addr_lit lit; exact HYP | exact (bytes_le_to_Z_8 _) ] | step_simpl; vnorm].
