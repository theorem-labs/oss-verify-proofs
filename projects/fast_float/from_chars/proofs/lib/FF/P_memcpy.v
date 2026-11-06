(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim CatExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib Require RefMemcpyBase RefMemcpy.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import P_memcpy_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Lemma memcpy_spec : memcpy_stmt.
Proof.
  unfold memcpy_stmt.
  intros until old. intros SRC DST LEN N DISJ NW0 NW1 RA.
  pose proof (bytes_at_bound _ _ _ _ SRC) as Bs.
  pose proof (u8arr_bound _ _ _ _ DST) as Bd.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  (* [comment removed for export] *)
  assert (HOK : RefMemcpyBase.mcH m a0 a1 (bv_unsigned a2) bs).
  { constructor.
    - lia.
    - lia.
    - replace a1 with (wa (bv_unsigned a1 + Z.of_nat 0)) by (unfold wa; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
      rewrite (bytes_at_rdn PSEGS m _ bs 0 (length bs) SRC) by lia. cbn. rewrite firstn_all. reflexivity.
    - destruct DST as [_ W]. rewrite LEN in W.
      replace a0 with (wa (bv_unsigned a0 + 0)) by (unfold wa; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
      apply (wr_at_store_ok PSEGS m _ _ 0 (length bs) W); lia.
    - lia.
    - lia.
    - lia. }
  pose proof (RefMemcpy.ref_memcpy (fx := fp_of F fc) m a0 a1 (bv_unsigned a2) bs (seg_rom PSEGS) HOK
                (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                ra (OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare.ret_ok_even ra RA) eq_refl eq_refl eq_refl ltac:(symmetry; apply Z_to_bv_bv_unsigned))
    as (regs' & RUN & KEEP).
  resume_after_summary RUN.
  unfold RefMemcpyLib.keeps in KEEP. use_kept KEEP. simp_getr.
  (* [comment removed for export] *)
  lazymatch goal with
  | |- evt ?sg ?Q (MS ?R ?F' ra ?fc' None ?mm ?ro) =>
      apply (evt_eq sg Q _ (MS R F' (ret_pc ra) fc' None (write_to_mem m (wa (bv_unsigned a0)) bs) ro));
      [ f_equal; [ symmetry; apply (ret_pc_of_ret_ok ra (OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare.ret_ok_even ra RA))
                 | rewrite <- CatExec.write_to_mem_wbytes; unfold wa; rewrite Z_to_bv_bv_unsigned; reflexivity ]
      | ]
  end.
  apply evt_done. unfold memcpy_post.
  do 15 eexists. split; [reflexivity|].
  split. { apply munch_write; [apply munch_refl| lia | lia | cbn; lia]. }
  split. { apply wmono_write. apply wmono_refl. }
  split. { eapply u8arr_write_all; [exact DST| exact LEN]. }
  apply bytes_at_write_other; [exact SRC | lia | lia | lia].
Qed.
