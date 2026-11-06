(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Bz/Lib/ImageA.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Bz/Lib/ImageA.v, the B form of lib/A/Bz/Lib/ImageA.v at a working branch 5d8d8a15571 (asegs := AsanUbsan.M.loaded_segments; the A file's bsegs, used by no file, dropped); module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.
