(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_MsgpackEncImgFacts () := "K47Corelib4Init5Logic2eq01C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceEimage_brk_satisfiableI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma src_msgpack_enc_brk_satisfiable :
  image_brk_satisfiable Plain.M.loaded_segments = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncImgFacts ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Zj30Tg0024R0g002TR1'2g0034#1=001do"). Qed.

Lemma tgt_msgpack_enc_asan_brk_satisfiable :
  image_brk_satisfiable Asan.M.loaded_segments = true.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncImgFacts ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Zj30Tg0024R0g002TR1'2g004]#1=001do"). Qed.
