(* The closing pattern of the re-fit to statement passes 4-5 for check_words_add's ASan walk
   (lib/A/Prog/check_words_add.v, tcheck_words_add_proof), as lib/A/Prog/SupRemoveAllRefitClosed.v does for
   sup_remove_all: the per-binary record hypothesis the walk names besides HB is discharged at the pinned image
   (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head).
   IMG is cmd_img_facts_tfib. The walk takes no LAWS (it uses the core's AR_laws_ok itself), no TL, SIGP or PRW,
   and no MTL: it allocates nothing and its post has no meter conjunct. What remains is the statement's own
   hypotheses (the strcmp and strncmp wrappers' contracts at every FP state) and HB. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require check_words_add_c check_words_add.
Import ListNotations.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record *)
Hypothesis HB : CmdBSyms B.
Theorem tcheck_words_add_closed
  (ASTRCMP : forall fx0 : YK11.FPState,
     @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp))
  (ASTRNCMP : forall fx0 : YK11.FPState,
     @astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp)) :
  check_words_add_c.tcheck_words_add_spec B MT.
Proof.
exact (check_words_add.tcheck_words_add_proof B MT ASTRCMP ASTRNCMP HB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
Print Assumptions tcheck_words_add_closed.
