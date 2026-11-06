(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Ltac1.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_StepKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Exec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.MState."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1false"; "1list"; "1option"; "1pair"; "1prod"; "2eq"; "3Z"; "0F"; "4Segment"; "5MachineOk"; "5fetch_word"; "5is_ecall"; "5machine_result"; "5machine_state"]; ["6decode_any"; "7instr"; "8bvmap"; "9Core"; "9exec"; "0P"; "0Q"; "0R"; ":evt"; ";MS"; ";interp_eff0"; ";lift_result"; "0fc"; "0i"; "0m"; "0ms1"]; ["0pc"; "0ro"; "0rv"; "0segs"; "<Z_to_bv"; "<bv"; "0sz"; "0w"]]).
Lemma evt_step_gen : ltac2:(TCodec.tc2 tcn__CJ_Lib_StepKit "S6'3':%211'?!p021&By5'Q5yR0%211%5241yQ0%511'4%115y8%911%411p091'A'8'7%91:&<r=r9%3221(0r4%22A1%93841'1&=r5%211(2%?3521'6%12CB%J11&@r6%211(5%14IH;@%B271%I3741'>%11Q>p01Q>r1(;%12QBC%311r2&Kr:&JrB&D&Q4r7%22QF1r8(Cr@r?r>r<%55432Q=1%;3871r;%?3>21%B2A1%D11p0F1pQ<K1&HrA%231>Q>&I%17@?>QI=:I%53H41p041p081p0Q71p0QB1p0QI1pR0RF1pR>R51pQLR71pR@R?1pR4R:1pQNR;1pR6R@1pQJRC1pR2RG1pDRG1pQ@RH1pQ>RO1pR8S31").
Proof.
intros segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd HL Hc.
eapply evt_step; [split; [reflexivity|] | exact Hc].
rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). apply HL. reflexivity.
Qed.
Ltac2 Type exn ::= [ StepKit_stash (constr) ].
Ltac2 probe_concl (tac : unit -> unit) : constr :=
Control.plus (fun () => tac (); let g := Control.goal () in Control.zero (StepKit_stash g))
(fun e => match e with StepKit_stash g => g | _ => Control.zero e end).
Ltac2 collapse_conv (tac : Ltac1.t) : unit :=
let g0 := Control.goal () in
let g := probe_concl (fun () => Ltac1.run tac) in
if Constr.equal g0 g then () else ltac1:(g |- change_no_check g) (Ltac1.of_constr g).
Ltac collapse_conv tac := let f := ltac2:(tac |- Control.enter (fun () => collapse_conv tac)) in f tac.
