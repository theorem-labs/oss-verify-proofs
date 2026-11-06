From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c.
Open Scope Z_scope.

Definition hunt_ok (H : list byte) : Prop :=
  length H = 480%nat /\ table_ok (firstn 400 H) /\ lock_ok (firstn 12 (skipn 400 H)) /\ 0 <= s32_at H 440 <= 3.
