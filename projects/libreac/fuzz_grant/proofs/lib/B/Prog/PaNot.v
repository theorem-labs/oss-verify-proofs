(* The bitwise complement of any symbolic value, for the walks of image B's program code. The memory-checking build
   with the undefined-behaviour traps checks a pointer sum p + k against wrap-around as `not t, p; bltu t, k`: the
   branch to the trap is taken iff 2^64 - 1 - p < k. The symbolic engine has no interval for `x XOR -1`, and
   lib/Reusable/YI08.v's U_not / U_not_off cover an atom operand only. U_not_gen covers any operand (for example
   tx + 3 * ch), and U_not_ltb states the branch condition as the sum's overflow. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI04 YI08.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.
Lemma U_not_gen : forall E (v : sv), U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. pose proof (YP0e.U_range E v) as Hr. unfold M64 in Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* `not t, v; bltu t, k` branches iff the sum v + k passes 2^64 - 1. *)
Lemma U_not_ltb : forall E (v : sv) k, (U E (SAlu ALU_XOR v (SLit (-1))) <? k) = (2 ^ 64 - 1 <? U E v + k).
Proof.
intros E v k. rewrite U_not_gen.
destruct (Z.ltb_spec (2 ^ 64 - 1 - U E v) k); destruct (Z.ltb_spec (2 ^ 64 - 1) (U E v + k)); lia.
Qed.
(* With the sum below 2^64 the branch is not taken; the walks of image B discharge their pointer-overflow guards
   with this form. *)
Lemma U_not_ltb_false : forall E (v : sv) k, U E v + k <= 2 ^ 64 - 1 -> (U E (SAlu ALU_XOR v (SLit (-1))) <? k) = false.
Proof. intros E v k H. rewrite U_not_ltb. apply Z.ltb_ge. lia. Qed.
