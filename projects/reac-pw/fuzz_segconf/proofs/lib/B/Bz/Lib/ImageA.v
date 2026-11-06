From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.
