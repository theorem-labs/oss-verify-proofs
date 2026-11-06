From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

(** memcmp over n bytes of two lists with the same first n bytes returns 0. *)
Lemma chk_memcmp_eq_u : forall n (l r : list byte), (n <= length l)%nat -> (n <= length r)%nat ->
  firstn n l = firstn n r -> memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros l r Hl Hr He; [reflexivity|].
  destruct l as [|a l]; [cbn in Hl; lia|]. destruct r as [|b r]; [cbn in Hr; lia|].
  cbn in He. injection He as Eab Elr. subst b. cbn [memcmp_model]. rewrite Z.eqb_refl.
  apply IH; cbn in *; [lia | lia | exact Elr].
Qed.
