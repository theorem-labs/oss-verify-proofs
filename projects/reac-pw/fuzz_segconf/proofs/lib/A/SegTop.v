(* Modified by Theorem Labs, 2026-10: made from libreac/fuzz_grant's lib/A/GrantTop.v (the separate composition) for plugin-hostd/fuzz_command's ASan build: C2 of lib/A/CmdTFIBLib.v with the start-up certificate's instances of lib/A/CmdStartInst.v and the program contract from lib/A/Prog/CmdLibX.v, and the two statements from it through lib/A/AsanTop.v. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/CmdTop.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; Cmd*/cmd_* -> Seg*/seg_* (CmdTFIBLib -> SegTFIBLib, AsanTop -> SegAsanTop, CmdLibX -> SegLibX, CmdShape -> SegShape, CmdB -> SegB, CMD_RLO / CMD_RHI -> SEG_RLO / SEG_RHI, GI_cmdA -> GI_segA); the start-up certificate's class instances (lib/A/CmdStartInst.v) are not taken: the core's de-classed AD1q takes the generated start-up directly (SegTFIBLib.v); HLTOI is segconf's LLVMFuzzerTestOneInput_contract (contracts FINAL 6f783602b5e3) at lib/A/Prog/SegInstA.v's image-A terms, and its image premise is discharged in SegLibX.v by lib/A/Prog/SegHimgA.v; the agreement also takes SegAsanTop's plain side (plain_slot_ag, CPp, plain_segs). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05 YCbp YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v AF0m AE2k ACfn AE37 SegShape SegTFIB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegTFIBLib SegAsanTop AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA LLVMFuzzerTestOneInput_c SegLibX.
Open Scope Z_scope.

(* The guard: the plain build's sink hints are out of the way (paths in full: lib/U/Reusable has modules of the same
   short names, YI16, YI5b and YI5c). *)
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: the ASan image's own head. *)
Definition sk_probe : OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.YI16.sink_head := _.
Lemma sk_probe_is_asan : sk_probe = AE2k.tfib_sink_head.
Proof. reflexivity. Qed.

Section asan.

(* ---- the open parts, one named hypothesis each ------------------------------------- *)

(* DtorExit: the ASan module destructor's contract (lib/A/AE37.v), cgif's x2_realizes statement; the core's
   lib/A/Rt/RtDtorExit.v gives the instance. *)
Context {DE : DtorExit}.

(* HLTOI: the contract of the program's entry function (lib/A/Prog/LLVMFuzzerTestOneInput_c.v at contracts FINAL
   6f783602b5e3), at the ASan image's sink head, the segments tfibsegs, the pinned allocator record SegB and the
   trivial meter, at SegInstA's image-A terms, at every run ceiling and float state (SegProgClosed.v's seg_ltoi_all). *)
Hypothesis HLTOI : forall (rc : YM05.RunCeil) (fx0 : YK11.FPState),
  @LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc AE2k.tfib_sink_head tfibsegs AD2l.SegB ameter_triv
    SegInstA.A_LLVMFuzzerTestOneInput_A SegInstA.STK_LLVMFuzzerTestOneInput SegInstA.emptyA SegInstA.RLO_A
    SegInstA.RHI_A SegInstA.longlA SegInstA.mod40A SegInstA.catA SegInstA.wordsA SegInstA.rolesA SegInstA.gotwA
    SegInstA.guardA SegInstA.seg_litA_fz SegInstA.seg_litA_rc.

(* ---- the chain ---------------------------------------------------------------------- *)

(* The program contract C3 from the program side's closing bridge (lib/A/Prog/SegLibX.v); its XL0 and SegTFIBLib's
   are both `fun _ => 0`. *)
Lemma seg_lib_all : forall (rc : YM05.RunCeil) (j : nat),
@tfib_lib_contract_x_all rc seg_shape AD2l.SegB ameter_triv SegTFIBLib.XL0 SegTFIBLib.XL0 SEG_RLO SEG_RHI GI_segA j.
Proof. intros rc j. exact (@SegLibX.seg_lib_x_closed rc (HLTOI rc) j). Qed.

(* C2 with the core's de-classed start-up (SegTFIBLib.v). *)
Theorem seg_TFIB_T_of_parts : TFIB_T.
Proof. exact (SegTFIBLib.seg_TFIB_T_of_lib seg_lib_all). Qed.

(* The two statements of reac-pw/fuzz_segconf's ASan build, given only the named parts above and, for the agreement,
   SegAsanTop's plain side (lib/A/SegAsanTop.v). *)
Theorem seg_asan_halts_of_parts : Statements.asan_halts.
Proof. exact (SegAsanTop.seg_asan_halts_of_tfib seg_TFIB_T_of_parts). Qed.
(* the agreement: SegAsanTop's plain side (the plain tree's lib/AgreeSeg.v plain_slot_ag at
   cfdd99183965, a cut record and the plain segment lemmas at it) and C2 *)
Definition seg_asan_agrees_of_parts :=
  fun psa cpp ps => SegAsanTop.seg_asan_agrees_of_tfib psa cpp ps seg_TFIB_T_of_parts.
End asan.
