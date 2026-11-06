From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require check_round_trip_c.
Local Open Scope Z_scope.

Lemma crt_tree_plain : forall t : jv,
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.check_round_trip_c.crt_tree t =
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.check_round_trip_c.crt_tree t.
Proof. intros t. reflexivity. Qed.
