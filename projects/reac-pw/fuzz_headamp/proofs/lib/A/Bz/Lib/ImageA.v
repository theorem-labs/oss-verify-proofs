(* Modified by Theorem Labs, 2026-10: proofs/plugin-hostd/fuzz_command/lib/A/Bz/Lib/ImageA.v at 2d2ff01bb6f; module paths changed to reac-pw/fuzz_headamp; 0 numeral(s) moved from fuzz_command.asan to fuzz_headamp.asan by alreloc a5c53bb2bed4. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.reac_pw.fuzz_headamp.images Require Import Asan AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := Asan.M.loaded_segments.
Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
