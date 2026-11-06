From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.
