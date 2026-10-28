From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WoR2 LbB_WoR4.
Import ListNotations.
Open Scope Z_scope.

Lemma wo_sh_2a : LbB_WoR2.WO_SH2A = wo_sh [20]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wo_sh_2c : LbB_WoR2.WO_SH2C = wo_sh [20; 21]%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wo_sh_4t : LbB_WoR4.WO_SH4T = wo_sh [18; 20; 21]%nat.
Proof. vm_compute. reflexivity. Qed.
