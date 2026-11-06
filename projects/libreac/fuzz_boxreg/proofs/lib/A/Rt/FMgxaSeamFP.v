(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMgxaSeamFP.v (a working branch 7e395de08f5) to libreac/fuzz_boxreg.asan: module paths changed; 0 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset). *)
(* The FP clause of the shared post, in the form the GXA route delivers.

   GXA's post states the FP register file it ends in as
     (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
   (lib/CJ/RL/GX/G_vfprintf_snf.v:70, lib/CJ/RL/G/G_pop_arg.v:479), with F the entry file.  Through
   the seam the entry file is `fp_regs fx` and the new FPState is `YK11.mkFP Ft fc'`.  The shared
   post's clause in the `Sem.reg_get` form (a Theorem Labs lane, after a Theorem Labs lane found that the `getr`
   form says nothing about f0, since getr returns 0 for register 0) is then GXA's clause verbatim;
   `fp_clause_of_gxa` checks that by compiling.  `fp_clause_getr` keeps the old `getr` form derivable
   too, for any consumer still on it. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YK11.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.CJ.Lib Require FP.
Local Open Scope Z_scope.

(* GXA's two facts about the final FP state, as the seam's continuation receives them *)
Definition gxa_fp_post (F Ft : bvmap 5 word) (fc' : bv 32) : Prop :=
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) /\ FP.frm0 fc'.

(* the shared post's FP clauses, Sem.reg_get form *)
Lemma fp_clause_of_gxa : forall (fx : YK11.FPState) (Ft : bvmap 5 word) (fc' : bv 32),
  gxa_fp_post (@YK11.fp_regs fx) Ft fc' ->
  (forall k : bv 5, bv_unsigned k <> 10 ->
     Sem.reg_get (@YK11.fp_regs (YK11.mkFP Ft fc')) k = Sem.reg_get (@YK11.fp_regs fx) k) /\
  Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr (YK11.mkFP Ft fc'))) 5) 7 = 0.
Proof. intros fx Ft fc' [HF H0]. split; [exact HF | exact H0]. Qed.

(* the earlier getr form follows from the reg_get one (register 0 reads 0 on both sides) *)
Lemma fp_clause_getr : forall (fx : YK11.FPState) (Ft : bvmap 5 word) (fc' : bv 32),
  gxa_fp_post (@YK11.fp_regs fx) Ft fc' ->
  forall k : bv 5, bv_unsigned k <> 10 ->
    YK11.getr (@YK11.fp_regs (YK11.mkFP Ft fc')) k = YK11.getr (@YK11.fp_regs fx) k.
Proof.
intros fx Ft fc' [HF _] k Hk. unfold YK11.getr. cbn [YK11.fp_regs].
destruct (bv_eqb k 0); [reflexivity | exact (HF k Hk)].
Qed.
