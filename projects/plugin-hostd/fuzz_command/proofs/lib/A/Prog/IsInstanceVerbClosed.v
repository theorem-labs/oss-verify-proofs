(* The closing pattern of the pass-4/5 re-fit for is_instance_verb's ASan walk
   (lib/A/Prog/is_instance_verb.v, is_instance_verb_ok): the record hypotheses the walk names are discharged at the
   pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head
   AE2k.tfib_sink_head), as SupRemoveAllRefitClosed.v and RecBClosed.v
   do: TL is cmd_palib and IMG is cmd_img_facts_tfib; the walk takes
   LAWS as the core's AR_laws_ok already. What remains is the statement's own runtime hypotheses (STRCSPN and STRNCMP
   at every FP state) and HB. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require is_instance_verb_c is_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Theorem tis_instance_verb_closed
  (STRCSPN : forall fx0 : YK11.FPState,
     @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8)
  (STRNCMP : forall fx0 : YK11.FPState,
     @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp)) :
  A.Prog.is_instance_verb_c.tis_instance_verb_spec B MT.
Proof.
apply (A.Prog.is_instance_verb.is_instance_verb_ok B MT);
  first [ exact STRCSPN | exact STRNCMP | exact HB
        | exact (CmdRecRest.cmd_palib B HB) | exact (CmdRecImg.cmd_img_facts_tfib B HB) ].
Qed.
End closed.
