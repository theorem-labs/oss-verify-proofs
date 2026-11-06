From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.
