(* Port-from: origin/cold/c-asan-rt-stateio-n 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/Lib/ImageA.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := Asan.M.loaded_segments.
Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
