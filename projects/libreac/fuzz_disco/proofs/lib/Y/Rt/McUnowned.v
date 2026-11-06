(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6i.v:33 tfc_lit_unowned, restated for libreac/fuzz_disco over an arbitrary range whose disjointness from Tfib_owned_static and TFIB_ERRNO is a boolean check, so every S4 lane instantiates it for its own constants; module paths. *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Rt/McUnowned.v for the asan-ubsan image of libreac/fuzz_disco: tfibsegs, Tfib_owned_static, TFIB_ERRNO and TfibSyms from lib/Reusable YB1v, YF0l, YF0m in place of lib/A AB1v, AF0l, AF0m. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YF0l YF0m YE39.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Export McConsts.
Import ListNotations.
Open Scope Z_scope.
Definition rng_unowned_chk (lo hi : Z) : bool :=
forallb (fun r : Z * Z => (hi <=? fst r) || (fst r + snd r <=? lo)) Tfib_owned_static
&& ((hi <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? lo)).
Lemma mc_unowned_range : forall B, TfibSyms B -> forall lo hi,
rng_unowned_chk lo hi = true -> forall a, lo <= a < hi ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB lo hi Hchk a Ha.
unfold rng_unowned_chk in Hchk. apply andb_prop in Hchk as [Hown Herr].
split.
- intros HX. rewrite (ts_owned B TB) in HX. apply Exists_exists in HX as (r & Hr & Hin).
rewrite forallb_forall in Hown. specialize (Hown r Hr).
apply orb_prop in Hown as [H1|H1]; apply Z.leb_le in H1; unfold in_zr in Hin; lia.
- rewrite (ts_errno B TB). apply orb_prop in Herr as [H2|H2]; apply Z.leb_le in H2; lia.
Qed.
Lemma mc_consts_eq : MC_CONSTS_LO = MC_LO /\ MC_CONSTS_HI = MC_HI.
Proof. split; reflexivity. Qed.
Lemma mc_consts_unowned : forall B, TfibSyms B -> forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TB. apply (mc_unowned_range B TB MC_CONSTS_LO MC_CONSTS_HI).
vm_compute. reflexivity.
Qed.
Definition rng_in_rom_chk (lo hi : Z) : bool :=
match nth_error tfibsegs 0 with
| Some s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo)
&& (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))
| None => false
end.
Lemma rng_in_rom_seg0 : forall lo hi,
rng_in_rom_chk lo hi = true -> forall a, lo <= a < hi -> in_rom tfibsegs a.
Proof.
intros lo hi Hchk a Ha. unfold rng_in_rom_chk in Hchk.
destruct (nth_error tfibsegs 0) as [s|] eqn:E; [|discriminate].
apply andb_prop in Hchk as [Hchk Hhi]. apply andb_prop in Hchk as [Hw Hlo].
apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
exists s. split; [exact (nth_error_In tfibsegs 0 E)|]. split; [exact Hw | lia].
Qed.
Lemma mc_consts_in_rom : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_rom tfibsegs a.
Proof.
apply (rng_in_rom_seg0 MC_CONSTS_LO MC_CONSTS_HI). vm_compute. reflexivity.
Qed.
