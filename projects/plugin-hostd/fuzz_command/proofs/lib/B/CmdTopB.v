(* Modified by Theorem Labs, 2026-10: made from this harness's lib/A/CmdTop.v (the ASan closing file) for plugin-hostd/fuzz_command's ASan+UBSan build: C2 of lib/B/CmdTFIBBLib.v with the start-up certificate's instances of lib/B/CmdStartInstB.v and the program contract from lib/B/Prog/CmdLibX.v, and the two statements from it through lib/A/AsanUbsanTop.v. *)
(* The closing file of plugin-hostd/fuzz_command's ASan+UBSan build (image B): the two statements
   `Statements.asan_ubsan_agrees` and `Statements.asan_ubsan_halts` from named parts only.

   The chain, each link proved in its owner's file:
     CmdLibX.cmd_lib_x_closed (lib/B/Prog/CmdLibX.v) -- the program contract C3 (lib/B/YCfn.v tfib_lib_contract_x_all
       at CmdB, the trivial meter, every run ceiling and call index) from the contract of the program's entry
       function LLVMFuzzerTestOneInput;
     CmdTFIBBLib.cmd_TFIB_T_B_of_lib (lib/B/CmdTFIBBLib.v) -- C2: the driver and the start-up over the program contract,
       giving CmdTFIBB.TFIB_T_B, with the ASan+UBSan malloc chain's tfib_amalloc_realizes (lib/B/YF0w.v); its
       start-up classes are filled by the instances of lib/B/CmdStartInstB.v (the hand-off states of lib/B/YB01.v,
       tfib_startup_T1 of lib/B/YB1n.v, and the eight checks by computation);
     AsanUbsanTop.cmd_asan_ubsan_agrees_of_tfib / cmd_asan_ubsan_halts_of_tfib (lib/A/AsanUbsanTop.v) -- the two
       statements from TFIB_T_B.

   Every still-open part is ONE named Section hypothesis below, with exactly the statement its owner's file gives:
     DtorExit (lib/B/YE37.v) -- the ASan module destructor's contract over the ASan+UBSan image's asan_globals;
     HLTOI (lib/B/Prog/CmdLibX.v, Section closed) -- the contract of LLVMFuzzerTestOneInput
       (lib/B/Prog/LLVMFuzzerTestOneInput_c.v tLLVMFuzzerTestOneInput_spec) at every run ceiling and float state.

   THE SINK INSTANCE IS EXPLICIT. lib/A/AsanUbsanTop.v loads lib/A/AsanTop.v, which loads the plain build's
   lib/Reusable/YI5b.v (`#[global] Instance src0_sink_head`) and lib/Reusable/YI5c.v (`src0_sink`). Both hints are
   removed below, so no sink argument here can be filled with the plain build's head; `sk_probe_is_asan_ubsan` shows
   what a bare `sink_head` resolves to. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YM05 YCbp YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YE2k YCfn YE37.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import CmdShape CmdTFIBB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import CmdStartInstB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require CmdTFIBBLib YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AsanUbsanTop.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdImg LLVMFuzzerTestOneInput_c CmdLibX.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way (paths in full: lib/U/Reusable has modules of the same
   short names, YI16, YI5b and YI5c). *)
#[local] Remove Hints OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: the ASan+UBSan image's own head. *)
Definition sk_probe : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI16.sink_head := _.
Lemma sk_probe_is_asan_ubsan : sk_probe = YE2k.tfib_sink_head.
Proof. reflexivity. Qed.

Section asan_ubsan.

(* ---- the open parts, one named hypothesis each ------------------------------------- *)

(* DtorExit: the ASan module destructor's contract on the ASan+UBSan image (lib/B/YE37.v). *)
Context {DE : DtorExit}.

(* HLTOI: the contract of the program's entry function (lib/B/Prog/CmdLibX.v, Section closed), at the ASan+UBSan
   image's sink head, the program image PB_cmd (lib/B/Prog/CmdImg.v), the pinned allocator record CmdB and the trivial
   meter, at every run ceiling and float state. *)
Hypothesis HLTOI : forall (rc : YM05.RunCeil) (fx0 : YK11.FPState),
@LLVMFuzzerTestOneInput_c.tLLVMFuzzerTestOneInput_spec fx0 rc YE2k.tfib_sink_head CmdImg.PB_cmd YD2l.CmdB ameter_triv.

(* ---- the chain ---------------------------------------------------------------------- *)

(* The program contract C3 from the program side's closing bridge (lib/B/Prog/CmdLibX.v); its XL0 and
   CmdTFIBBLib's are both `fun _ => 0`. *)
Lemma cmd_lib_all : forall (rc : YM05.RunCeil) (j : nat),
@tfib_lib_contract_x_all rc cmd_shape YD2l.CmdB ameter_triv CmdTFIBBLib.XL0 CmdTFIBBLib.XL0 CMD_RLO CMD_RHI GI_cmdA j.
Proof. intros rc j. exact (@CmdLibX.cmd_lib_x_closed rc (HLTOI rc) j). Qed.

(* C2 with the start-up certificate's instances (lib/B/CmdStartInstB.v), found by instance resolution. *)
Theorem cmd_TFIB_T_B_of_parts : TFIB_T_B.
Proof. exact (CmdTFIBBLib.cmd_TFIB_T_B_of_lib cmd_lib_all). Qed.

(* The two statements of plugin-hostd/fuzz_command's ASan+UBSan build, given only the named parts above
   (lib/A/AsanUbsanTop.v). *)
Theorem cmd_asan_ubsan_agrees_of_parts : Statements.asan_ubsan_agrees.
Proof. exact (AsanUbsanTop.cmd_asan_ubsan_agrees_of_tfib cmd_TFIB_T_B_of_parts). Qed.
Theorem cmd_asan_ubsan_halts_of_parts : Statements.asan_ubsan_halts.
Proof. exact (AsanUbsanTop.cmd_asan_ubsan_halts_of_tfib cmd_TFIB_T_B_of_parts). Qed.
End asan_ubsan.
