(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: the __vdsosym postcondition at LPS 727298f3, where the lookup finds the vDSO and returns its clock_gettime entry. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/Ref/RVdsoSym.v, with its module paths, module names and numbers changed; 3 of its 23 lines of code are new or changed and 3 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/Ref/RVdsoSym.v, lines 11-39, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the postcondition of the ASan+UBSan build's __vdsosym,
   this directory's copy of Ref/RVdsoSym.v.  At LPS 727298f3 the auxv publishes AT_SYSINFO_EHDR as its first pair,
   so musl's __vdsosym("LINUX_4.15", "__vdso_clock_gettime") finds the vDSO ELF at the base [vb]
   it reads there and returns [vb + RVDSO_CGT_OFF] (Lib/VdsoImg.v ties RVDSO_CGT_OFF = 1460 to the
   model's own symbol table).  The two string compares go to ASan's strcmp interceptor
   (Both/As/AsStrcmp.v), so the stack the call uses is __vdsosym's own 0x70 bytes plus the
   interceptor's 0x7f0 + 0xa0 + 0x10 (AsStrcmp.ASTRCMP_FRAME): 112 + 2208 = 2320 bytes. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Frame VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AVdsoAddr AVdsoSegs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The deepest stack the call uses: 0x70 (__vdsosym) + 2208 (the strcmp interceptor). *)
Definition AVW_FRAME : Z := 2320.

Section WithTail.
  Variable tail : list Segment.

  Local Notation VS := (VW_BSEGS ++ tail).

  (* Every register the ABI preserves comes back; [a0] is the entry; the rest are free. *)
  Definition avdsosym_post_v (vb : Z)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0
                    a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom VS)
      /\ a0 = Z_to_bv 64 (vb + RVDSO_CGT_OFF)
      /\ munch [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m m'
      /\ wmono VS m m' /\ mem_inv VS m' /\ stk VS m' lo (bv_unsigned sp).

End WithTail.
