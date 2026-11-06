(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP0m YP06 YI04.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Lemma env_agree_Ereg_app : forall regs l1 l2 k, (k <= 32 + length l1)%nat -> env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
