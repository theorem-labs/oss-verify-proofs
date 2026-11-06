(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Ltac1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_StepKit () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;interp_eff0C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lift_resultC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK47Corelib4Init5Logic2eq01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState8step_genC13~~~K47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_stepC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02".
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma evt_step_gen : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w i sz ms1,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  (forall P : machine_result machine_state -> Prop,
     P (MachineOk ms1) -> P (lift_result ro (interp_eff0 segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m))) ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
ltac2:(KReplay.run1 (kr_t_StepKit ()) [] "h01mh11Fh22HLh32Hch42Hdh52Heh62Hfh71Ph81Qh91Rh:2fch;1ih<3ms1h=2pch>2roh?2rvh@4segshA2szhB1wp;1p;2p;3p;4p;5p;7p;>p;6g0000R0p4p7210g000\R1p4p710p8g001:j1NTg001Zj11Tg002?j1>Tg002dj13Tg003Bj15TP0j2ITg003ej12Tg004Gj2=Tg005Ij26Tg005kj30Tg006Ej18Tg007Ej29Tg007ej1:Tg008Vj4MTg0096j1LTg00:>j24Tg00;Fj2HTg00;lj5FTg00<Uj3ETg00=<j3?Tg00>Pj2@Tg00?dj3ATg00@nj7BTg00B9j1CTg00C?j1DTg00Caj2<Tg00D]j27Tg00E7l>GTP1j6;Tg00FHj4JTg00Fcj6KTg00H2#Ng00I1R1p-0R0[g00J8#1R2#>#3%12#1R2#1#1R3#1#3R4#5R5'IR6%33#5R3%25R7%32#5#2\5R2g00J]R8g00KIR9%23f<R:f8R;'=f3R<,6330g00Kgf4R=#8g00LG301989R>#2f5R?#:P8P9P=P<CM,6>30%L1R>P0[f0R0141=O1f1R9f9R8fAR@f6RA,H4f7R4f?RBf>RCf=RDP:f;REDF3Ef:RF3?'@RGO1[]7f@RH?AB=P@PHPBPCPDP:PEPFP8FBRHP?%CH%D5RI5071<@HRH141?R?50>177IP>PG141A90>0X0>RGP9PG17>?O2PHP@PBPCPDP:PEPFP8P;P4PAP=P<f2M>GE;CJP0EKW3W2W4W5W6X<1WAW;XB3X>2W0W?W:X=5X16W9W8W@o"). Qed.

Ltac2 Type exn ::= [ StepKit_stash (constr) ].
(* [comment removed for export] *)
Ltac2 probe_concl (tac : unit -> unit) : constr :=
  Control.plus (fun () => tac (); let g := Control.goal () in Control.zero (StepKit_stash g))
               (fun e => match e with StepKit_stash g => g | _ => Control.zero e end).
Ltac2 collapse_conv (tac : Ltac1.t) : unit :=
  let g0 := Control.goal () in
  let g := probe_concl (fun () => Ltac1.run tac) in
  if Constr.equal g0 g then () else ltac1:(g |- change_no_check g) (Ltac1.of_constr g).
(* [comment removed for export] *)
Ltac collapse_conv tac := let f := ltac2:(tac |- Control.enter (fun () => collapse_conv tac)) in f tac.
