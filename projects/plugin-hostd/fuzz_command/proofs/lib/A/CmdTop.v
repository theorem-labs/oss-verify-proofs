(* Modified by Theorem Labs, 2026-10: made from libreac/fuzz_grant's lib/A/GrantTop.v (the separate composition) for plugin-hostd/fuzz_command's ASan build: C2 of lib/A/CmdTFIBLib.v with the start-up certificate's instances of lib/A/CmdStartInst.v and the program contract from lib/A/Prog/CmdLibX.v, and the two statements from it through lib/A/AsanTop.v. *)
(* The closing file of plugin-hostd/fuzz_command's ASan build (image A): the two statements
   `Statements.asan_agrees` and `Statements.asan_halts` from named parts only.

   The chain, each link proved in its owner's file:
     CmdLibX.cmd_lib_x_closed (lib/A/Prog/CmdLibX.v) -- the program contract C3 (lib/A/ACfn.v tfib_lib_contract_x_all
       at CmdB, the trivial meter, every run ceiling and call index) from the contract of the program's entry
       function LLVMFuzzerTestOneInput;
     CmdTFIBLib.cmd_TFIB_T_of_lib (lib/A/CmdTFIBLib.v) -- C2: the driver and the start-up over the program contract,
       giving CmdTFIB.TFIB_T; its start-up classes are filled by the instances of lib/A/CmdStartInst.v (the
       hand-off states of lib/A/AB01.v, tfib_startup_T1 of lib/A/AB1n.v, and the seven checks by computation);
     AsanTop.cmd_asan_agrees_of_tfib / cmd_asan_halts_of_tfib (lib/A/AsanTop.v) -- the two statements from TFIB_T.

   Every still-open part is ONE named Section hypothesis below, with exactly the statement its owner's file gives:
     DtorExit (lib/A/AE37.v) -- the ASan module destructor's contract, cgif's x2_realizes over fuzz_command's
       asan_globals descriptors;
     HLTOI (lib/A/Prog/CmdLibX.v:155) -- the contract of LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_c.v
       tLLVMFuzzerTestOneInput_spec) at every run ceiling and float state, which the program side's composition gives
       from lib/A/Prog/LtoiClosed.v and the callees' and runtime entries' closures.

   THE SINK INSTANCE IS EXPLICIT. lib/A/AsanTop.v loads the plain build's lib/Reusable/YI5b.v (`#[global] Instance
   src0_sink_head`, the PLAIN build's output head) and lib/Reusable/YI5c.v (`src0_sink`). Both hints are removed
   below, so no sink argument here can be filled with the plain build's head; `sk_probe_is_asan` shows what a bare
   `sink_head` resolves to. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YCbp YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AE2k ACfn AE37 CmdShape CmdTFIB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import CmdStartInst.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require CmdTFIBLib AsanTop AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdImg LLVMFuzzerTestOneInput_c CmdLibX.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way (paths in full: lib/U/Reusable has modules of the same
   short names, YI16, YI5b and YI5c). *)
#[local] Remove Hints OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: the ASan image's own head. *)
Definition sk_probe : OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable.YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = AE2k.tfib_sink_head.
Proof. reflexivity. Qed.

Section asan.

(* ---- the open parts, one named hypothesis each ------------------------------------- *)

(* DtorExit: the ASan module destructor's contract (lib/A/AE37.v:14), cgif's x2_realizes statement. *)
Context {DE : DtorExit}.

(* HLTOI: the contract of the program's entry function (lib/A/Prog/CmdLibX.v:155), at the ASan image's sink head,
   the program image PB_cmd (lib/A/Prog/CmdImg.v), the pinned allocator record CmdB and the trivial meter, at every
   run ceiling and float state. *)
Hypothesis HLTOI : forall (rc : YM05.RunCeil) (fx0 : YK11.FPState),
@LLVMFuzzerTestOneInput_c.tLLVMFuzzerTestOneInput_spec fx0 rc AE2k.tfib_sink_head CmdImg.PB_cmd AD2l.CmdB ameter_triv.

(* ---- the chain ---------------------------------------------------------------------- *)

(* The program contract C3 from the program side's closing bridge (lib/A/Prog/CmdLibX.v:157); its XL0 and
   CmdTFIBLib's are both `fun _ => 0`. *)
Lemma cmd_lib_all : forall (rc : YM05.RunCeil) (j : nat),
@tfib_lib_contract_x_all rc cmd_shape AD2l.CmdB ameter_triv CmdTFIBLib.XL0 CmdTFIBLib.XL0 CMD_RLO CMD_RHI GI_cmdA j.
Proof. intros rc j. exact (@CmdLibX.cmd_lib_x_closed rc (HLTOI rc) j). Qed.

(* C2 with the start-up certificate's instances (lib/A/CmdStartInst.v), found by instance resolution. *)
Theorem cmd_TFIB_T_of_parts : TFIB_T.
Proof. exact (CmdTFIBLib.cmd_TFIB_T_of_lib cmd_lib_all). Qed.

(* The two statements of plugin-hostd/fuzz_command's ASan build, given only the named parts above
   (lib/A/AsanTop.v:75 and :91). *)
Theorem cmd_asan_agrees_of_parts : Statements.asan_agrees.
Proof. exact (AsanTop.cmd_asan_agrees_of_tfib cmd_TFIB_T_of_parts). Qed.
Theorem cmd_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (AsanTop.cmd_asan_halts_of_tfib cmd_TFIB_T_of_parts). Qed.
End asan.
