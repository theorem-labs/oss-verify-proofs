(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG01 YG0h YG0u YG0d YB1u YF9i YF9j YF9m YCeb YD2g YCe8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCi7 YCjc YCp4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition fpc_off (lo hi : Z) (r : Z * Z) : bool := ((fst r + snd r <=? lo) || (hi <=? fst r))%bool.
Lemma trb_fpc_chk :
forallb (fun r => fpc_off 0x10300 0x10308 r && fpc_off 0x10318 0x10320 r && fpc_off 0x10340 0x10348 r && fpc_off 0x10368 0x10370 r && fpc_off 0x10380 0x10388 r &&
fpc_off 0x20ea0 0x20ea4 r)%bool Trb_owned_static = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fpc_off_sound : forall lo hi r a, fpc_off lo hi r = true -> lo <= a < hi -> fst r <= a < fst r + snd r -> False.
Proof. intros lo hi r a Hb Ha Hr. unfold fpc_off in Hb. apply Bool.orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia. Qed.
Theorem TrbB_fp_consts : trb_fp_consts TrbB.
Proof.
intros a Ha. unfold trb_fpc_addr in Ha. cbn [as_owned_static as_errno TrbB]. unfold TRB_ERRNO. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & Hin). unfold in_zr in Hin.
pose proof (proj1 (forallb_forall _ _) trb_fpc_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [Hb H6]. apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
[ exact (fpc_off_sound _ _ r a H1 Ha Hin) | exact (fpc_off_sound _ _ r a H2 Ha Hin) | exact (fpc_off_sound _ _ r a H3 Ha Hin)
| exact (fpc_off_sound _ _ r a H4 Ha Hin) | exact (fpc_off_sound _ _ r a H5 Ha Hin) ].
Qed.
Theorem TrbB_rol_const : trb_rol_const TrbB.
Proof.
intros a Ha. unfold LDK_ROL in Ha. cbn [as_owned_static as_errno TrbB]. unfold TRB_ERRNO. split; [|lia].
intros HE. apply Exists_exists in HE as (r & Hr & Hin). unfold in_zr in Hin.
pose proof (proj1 (forallb_forall _ _) trb_fpc_chk r Hr) as Hb. cbn beta in Hb.
apply andb_prop in Hb as [_ H6].
exact (fpc_off_sound _ _ r a H6 Ha Hin).
Qed.
