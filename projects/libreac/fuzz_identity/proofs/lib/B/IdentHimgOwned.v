(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closer's discharge of identb_himg's HIMG_UNOWNED premise for libreac/fuzz_identity's
   ASan+UBSan build (image B), against the frozen B core table lib/B/AF0m.v (sha256 82901a424bb97a7d...), copied verbatim below. *)
(* identb_himg (lib/B/Prog/IdentEntryLink.v) takes
     HIMG_UNOWNED : forall x, Exists (in_zr x) IDENTB_RO_READS ->
       ~ Exists (in_zr x) (as_owned_static IdentB) /\ ~ (as_errno IdentB <= x < as_errno IdentB + 4)
   over the explicit list IDENTB_RO_READS of the image intervals llvmf_img reads. The B core's record IdentB
   (lib/ReusableB/YD2l.v:12) is applied in IdentTopB.v:234-235; its two fields enter here as Section premises of exactly the form that
   record satisfies by `eq_refl`: as_owned_static IdentB = TFIB_OWNED_STATIC_B and as_errno IdentB = TFIB_ERRNO_B
   (lib/ReusableB/YF0m.v's Tfib_owned_static / TFIB_ERRNO, copied). The check itself is closed:
   every read interval avoids every owned range and the errno word,
   cgif's AD1u FINV_IVS_unowned pattern (forallb, by vm_compute on a closed term). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require IdentEntryLink.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The frozen B core table, VERBATIM from lib/ReusableB/YF0m.v. *)
Definition TFIB_OWNED_STATIC_B : list (Z * Z) :=
[ (0x9e388, 0xa0c00 - 0x9e388); (0xa0f40, 0xcc0); (0xa1c00, 8); (0xa1c58, 0xa4b08 - 0xa1c58); (0xa4b10, 0x5c7910 - 0xa4b10)    ; (0x5d8250, 0x3c)  ;
(0x9c690, 8); (0x9c6e8, 8);
(0x102e8, 8); (0x10308, 8); (0x10328, 8); (0x103a0, 8); (0x103a8, 8); (0x103b8, 8); (0x10428, 64); (0x10528, 64);
(0x9c670, 0x20); (0x9c698, 0x18); (0x9c6b0, 0x38); (0x9d1f8, 8); (0x9d2e8, 8); (0x9d308, 16); (0x9d370, 16); (0x9d380, 8)  ;
(0x20f82, 0x1e);
(0x20fa3, 0x1d);
(0x20fc7, 0x19);
(0x20fe6, 0x1a);
(0x21024, 0x3c);
(0x21067, 0x19);
(0x21087, 0x19);
(0x210a8, 0x18);
(0x210c5, 0x1b);
(0x21124, 0x3c);
(0x21167, 0x19);
(0x21187, 0x19);
(0x211a8, 0x18);
(0x211c5, 0x1b);
(0x211e3, 0x1d);
(0x21207, 0x19);
(0x21226, 0x1a);
(0x21266, 0x1a);
(0x21297, 0x29);
(0x212c6, 0x1a);
(0x212f6, 0x2a);
(0x21327, 0x19);
(0x21347, 0x19);
(0x2137d, 0x23);
(0x213ac, 0x14);
(0x213dd, 0x23);
(0x21406, 0x1a);
(0x21437, 0x29);
(0x21468, 0x18);
(0x21486, 0x1a);
(0x214b8, 0x28);
(0x214e8, 0x18);
(0x21507, 0x19);
(0x21538, 0x28);
(0x21569, 0x17);
(0x21587, 0x19);
(0x215b8, 0x28);
(0x215e9, 0x17);
(0x21607, 0x19);
(0x21637, 0x29);
(0x21668, 0x18);
(0x21687, 0x19);
(0x216b7, 0x29);
(0x216e8, 0x18);
(0x21707, 0x19);
(0x21738, 0x28);
(0x21768, 0x18);
(0x9b478, 0x28);
(0x9b4b8, 0x28);
(0x9b4f8, 0x28);
(0x9c1d8, 0x328);
(0x5d81f8, 8); (0x5d8248, 8); (0x5d8260, 8)  ; (0x5f95f8, 8);
(0x1ce7f, 21); (0x20d10, 4); (0x21d04, 4); (0x21d68, 2); (0x9d318, 8); (0x5f8510, 8) ].
Definition TFIB_ERRNO_B : Z := 0x5d81ac.

(* [lo, hi) avoids the range (b, n) = [b, b + n); the same test as lib/A/AD1y.v ext_avoids. *)
Definition hob_avoids (lo hi : Z) (h : Z * Z) : bool := (fst h + snd h <=? lo) || (hi <=? fst h).
Lemma hob_avoids_sound : forall lo hi l a, forallb (hob_avoids lo hi) l = true -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l a H Ha Hex. apply Exists_exists in Hex as (h & Hin & Hz).
apply (proj1 (forallb_forall _ _) H) in Hin. unfold hob_avoids in Hin. unfold in_zr in Hz.
apply orb_prop in Hin as [Hh|Hh]; apply Z.leb_le in Hh; lia.
Qed.

(* The closed check: each read interval avoids every owned range of the frozen table and the errno word. *)
Definition identb_ro_reads_ok : bool :=
forallb (fun iv => forallb (hob_avoids (fst iv) (fst iv + snd iv)) TFIB_OWNED_STATIC_B &&
                   hob_avoids (fst iv) (fst iv + snd iv) (TFIB_ERRNO_B, 4))
  IdentEntryLink.IDENTB_RO_READS.
Lemma identb_ro_reads_ok_true : identb_ro_reads_ok = true.
Proof. vm_compute. reflexivity. Qed.

Section b.
Variable IdentB : asyms.
(* The B core's record gives both by eq_refl (its as_owned_static / as_errno fields, the AD2l twin). *)
Hypothesis HOWN : as_owned_static IdentB = TFIB_OWNED_STATIC_B.
Hypothesis HERRNO : as_errno IdentB = TFIB_ERRNO_B.
(* HIMG_UNOWNED with identb_himg's exact text. *)
Lemma identb_HIMG_UNOWNED : forall x, Exists (in_zr x) IdentEntryLink.IDENTB_RO_READS ->
~ Exists (in_zr x) (as_owned_static IdentB) /\ ~ (as_errno IdentB <= x < as_errno IdentB + 4).
Proof.
intros x Hx. apply Exists_exists in Hx as (iv & Hin & Hz).
pose proof (proj1 (forallb_forall _ _) identb_ro_reads_ok_true iv Hin) as H.
apply andb_prop in H as [Hown Herr]. unfold in_zr in Hz. rewrite HOWN, HERRNO.
split.
- exact (hob_avoids_sound (fst iv) (fst iv + snd iv) _ x Hown ltac:(lia)).
- unfold hob_avoids in Herr. cbn [fst snd] in Herr.
  apply orb_prop in Herr as [Hh|Hh]; apply Z.leb_le in Hh; lia.
Qed.
End b.
