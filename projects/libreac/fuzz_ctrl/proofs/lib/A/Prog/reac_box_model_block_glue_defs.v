(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44), image A: the definitions of the glue that the standalone lemma files state their
   lemmas over, without Requiring the glue (reac_box_model_block_glue.v).  bmb_WR is the glue's write set of the tail
   (Section S3 of the glue, closed: arguments sp p o FS jj).  The glue's own bmb_WR is convertible with this one:
   `reac_box_model_block_glue.BmbGlue.bmb_WR sp p o FS jj = bmb_WR sp p o FS jj` holds by reflexivity. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c.
Import ListNotations.
Open Scope Z_scope.

(* What the tail (S2 from the allocator's return, the flag release, S3) may write: the real-stack window
   [sp - 4272, sp), the class-0 frame's flag byte, the frame itself, the frame's 8 shadow bytes, and the 32 bytes
   at o when the row is read (p <> 0 and o <> 0). *)
Definition bmb_WR (sp : bv 64) (p o FS jj : Z) : list ivl :=
  [(bv_unsigned sp - 4272, bv_unsigned sp); (fs_flag FS 0 jj, fs_flag FS 0 jj + 1);
   (fs_frame FS 0%nat jj, fs_frame FS 0%nat jj + 64);
   (shadow_addr (fs_frame FS 0%nat jj), shadow_addr (fs_frame FS 0%nat jj) + 8)] ++
  (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]).
