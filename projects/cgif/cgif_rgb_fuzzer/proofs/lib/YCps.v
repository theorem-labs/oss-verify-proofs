(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI04 YI1i YI08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCe9 YCfx YCi1 YCib YCie YCif YCid.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0p YI0c YM01 YG0e YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCph YCjr YCpj YCpo.
Fixpoint optl (os ns : list Z) {struct os} : list (Z * Z) :=
match os, ns with
| o :: os', n :: ns' => optb o n ++ optl os' ns'
| _, _ => []
end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition rga_optblk (B : asyms) (cx : rgcx) (E : env) (a : nat) (b n : Z) : Prop :=
ew E a = Z_to_bv 64 b /\ 0 <= b < 2 ^ 64 /\
(b <> 0 ->
aftok (rgc_FPs cx) (ablocks B (c_ly cx) (c_S cx)) (b, n) /\
(forall blc lyq ownq i, In (b, n) blc -> 0 <= i < req_size n ->
awr_byte TRGBADD_STK (spZ (c_regs cx)) (rgc_FPs cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (b + i))).
Fixpoint rga_opts (B : asyms) (cx : rgcx) (E : env) (l : list (nat * Z)) (os : list Z) {struct l} : Prop :=
match l, os with
| [], [] => True
| (a, n) :: l', o :: os' => rga_optblk B cx E a o n /\ rga_opts B cx E l' os'
| _, _ => False
end.
Definition INV_NO (B : asyms) (kmax : Z) (news opts : rgcx -> list (nat * Z)) : rga_inv_t :=
fun cx E k ly3 S3 W3 ms3 md3 => exists bs os : list Z,
rga_kb cx S3 k (k <= kmax) (k) (0) 0 /\ (c_fmt cx = 3 \/ c_fmt cx = 4) /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ combine bs (map snd (news cx)) ++ optl os (map snd (opts cx)) /\
rga_news B cx E (news cx) bs /\ rga_opts B cx E (opts cx) os /\
exists av : Z, ew E 300 = Z_to_bv 64 av /\ (av = 1 \/ av = 9).
Lemma mres_optb : forall (B : asyms) ly2 S2 lyc Sc (res n : Z) (P Q : Prop),
(res = 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\ P) \/ (4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] /\ Q) ->
ablocks B ly2 S2 = ablocks B lyc Sc ++ optb res n.
Proof.
intros B ly2 S2 lyc Sc res n P Q [(-> & -> & _) | (Hr & -> & _)]; unfold optb.
- cbn. rewrite app_nil_r. reflexivity.
- destruct (Z.eqb_spec res 0) as [Hz | _]; [lia | reflexivity].
Qed.
Lemma bsum_optb_le : forall o n, 0 <= n -> 0 <= bsum (optb o n) <= n.
Proof. intros o n Hn. unfold optb. destruct (o =? 0); cbn; lia. Qed.
End c.
Definition CHT_TS : Z := 524309.
