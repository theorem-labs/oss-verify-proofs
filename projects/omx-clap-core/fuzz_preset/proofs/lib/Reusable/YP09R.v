From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK14 YK1b YP0m YP0e YP09.
Import ListNotations.
Open Scope Z_scope.

Definition in_rrange (E : env) (rs : smem) (a : Z) : Prop :=
  exists r, In r rs /\ base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r.

Definition accs_in_rrange (E : env) (rs : smem) (accs : list (word * nat)) : Prop :=
  forall a n k, In (a, n) accs -> (k < n)%nat -> in_rrange E rs (bv_unsigned a + Z.of_nat k).
