(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closer's discharge of ident_himg's HIMG_UNOWNED premise for libreac/fuzz_identity's
   ASan build (image A), against the core's generated owned-static table and errno word: verbatim copies of the frozen
   lib/A/AF0m.v (start-up of record a working branch 4ceb4f70606, AF0m.v sha256 894ced30947c45ac...; the list is
   the same in every frozen A AF0m since 9cf01e8ed2e), so this file builds on the integration tip, which carries no AF0m. *)
(* ident_himg (lib/A/Prog/IdentEntryLink.v) takes
     HIMG_UNOWNED : forall x, Exists (in_zr x) IDENT_RO_READS ->
       ~ Exists (in_zr x) (as_owned_static IdentB) /\ ~ (as_errno IdentB <= x < as_errno IdentB + 4)
   over the explicit list IDENT_RO_READS of the image intervals llvmf_img reads (object 5 and the bodies of the
   registered globals read). The core's record has as_owned_static := Tfib_owned_static and as_errno := TFIB_ERRNO
   (lib/A/AF0m.v, copied below), so it meets the two Section premises below by eq_refl.
   The premise is then one closed computation: every read interval avoids every owned range and the errno word.
   This is cgif's AD1u FINV_IVS_unowned pattern (forallb of ext_avoids, by vm_compute on a
   closed term). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01 YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require IdentEntryLink.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The frozen A core table, VERBATIM from lib/A/AF0m.v (see the header). The core is in this tree: its record IdentB
   (AD2l.v:15) meets HOWN / HERRNO below by eq_refl (IdentTop.v:148-149), since this copy equals its Tfib_owned_static
   (AF0m.v:1551) and TFIB_ERRNO_A its TFIB_ERRNO (AF0m.v:24). *)
Definition TFIB_OWNED_STATIC_A : list (Z * Z) :=
[ (0x9e0a8, 0xa0920 - 0x9e0a8); (0xa0c60, 0xc80); (0xa1900, 8); (0xa1958, 0xa4808 - 0xa1958); (0xa4810, 0x5c7610 - 0xa4810)    ; (0x5d7f50, 0x3c)  ;
(0x9c3b0, 8); (0x9c408, 8);
(0x102e8, 8); (0x10308, 8); (0x10328, 8); (0x103a0, 8); (0x103a8, 8); (0x103b8, 8); (0x10428, 64); (0x10528, 64);
(0x9c390, 0x20); (0x9c3b8, 0x18); (0x9c3d0, 0x38); (0x9cf18, 8); (0x9d008, 8); (0x9d028, 16); (0x9d090, 16); (0x9d0a0, 8)  ;
(0x20f82, 0x1e);
(0x20fa7, 0x19);
(0x20fc6, 0x1a);
(0x21004, 0x3c);
(0x21047, 0x19);
(0x21067, 0x19);
(0x21088, 0x18);
(0x210a5, 0x1b);
(0x21104, 0x3c);
(0x21147, 0x19);
(0x21167, 0x19);
(0x21188, 0x18);
(0x211a5, 0x1b);
(0x211c3, 0x1d);
(0x211e7, 0x19);
(0x21206, 0x1a);
(0x21246, 0x1a);
(0x21277, 0x29);
(0x212a6, 0x1a);
(0x212d6, 0x2a);
(0x21307, 0x19);
(0x21327, 0x19);
(0x2135d, 0x23);
(0x2138c, 0x14);
(0x213bd, 0x23);
(0x213e6, 0x1a);
(0x21417, 0x29);
(0x21448, 0x18);
(0x21466, 0x1a);
(0x21498, 0x28);
(0x214c8, 0x18);
(0x214e7, 0x19);
(0x21518, 0x28);
(0x21549, 0x17);
(0x21567, 0x19);
(0x21598, 0x28);
(0x215c9, 0x17);
(0x215e7, 0x19);
(0x21617, 0x29);
(0x21648, 0x18);
(0x21667, 0x19);
(0x21697, 0x29);
(0x216c8, 0x18);
(0x216e7, 0x19);
(0x21718, 0x28);
(0x21748, 0x18);
(0x9b198, 0x28);
(0x9b1d8, 0x28);
(0x9b218, 0x28);
(0x9bef8, 0x328);
(0x5d7ef8, 8); (0x5d7f48, 8); (0x5d7f60, 8)  ; (0x5f92f8, 8);
(0x1ce78, 21); (0x20d08, 4); (0x21ce4, 4); (0x21d48, 2); (0x9d038, 8); (0x5f8210, 8) ].
Definition TFIB_ERRNO_A : Z := 0x5d7eac.

(* [lo, hi) avoids the range (b, n) = [b, b + n); the same test as lib/A/AD1y.v ext_avoids. *)
Definition ho_avoids (lo hi : Z) (h : Z * Z) : bool := (fst h + snd h <=? lo) || (hi <=? fst h).
Lemma ho_avoids_sound : forall lo hi l a, forallb (ho_avoids lo hi) l = true -> lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l a H Ha Hex. apply Exists_exists in Hex as (h & Hin & Hz).
apply (proj1 (forallb_forall _ _) H) in Hin. unfold ho_avoids in Hin. unfold in_zr in Hz.
apply orb_prop in Hin as [Hh|Hh]; apply Z.leb_le in Hh; lia.
Qed.

(* The closed check: each read interval avoids every owned range of TfibB and the errno word. *)
Definition ident_ro_reads_ok : bool :=
forallb (fun iv => forallb (ho_avoids (fst iv) (fst iv + snd iv)) TFIB_OWNED_STATIC_A &&
                   ho_avoids (fst iv) (fst iv + snd iv) (TFIB_ERRNO_A, 4))
  IdentEntryLink.IDENT_RO_READS.
Lemma ident_ro_reads_ok_true : ident_ro_reads_ok = true.
Proof. vm_compute. reflexivity. Qed.

Section b.
Variable IdentB : asyms.
(* The core's record (IdentB in the applied tree) gives both by eq_refl (its as_owned_static / as_errno fields). *)
Hypothesis HOWN : as_owned_static IdentB = TFIB_OWNED_STATIC_A.
Hypothesis HERRNO : as_errno IdentB = TFIB_ERRNO_A.
(* HIMG_UNOWNED with ident_himg's exact text. *)
Lemma ident_HIMG_UNOWNED : forall x, Exists (in_zr x) IdentEntryLink.IDENT_RO_READS ->
~ Exists (in_zr x) (as_owned_static IdentB) /\ ~ (as_errno IdentB <= x < as_errno IdentB + 4).
Proof.
intros x Hx. apply Exists_exists in Hx as (iv & Hin & Hz).
pose proof (proj1 (forallb_forall _ _) ident_ro_reads_ok_true iv Hin) as H.
apply andb_prop in H as [Hown Herr]. unfold in_zr in Hz. rewrite HOWN, HERRNO.
split.
- exact (ho_avoids_sound (fst iv) (fst iv + snd iv) _ x Hown ltac:(lia)).
- unfold ho_avoids in Herr. cbn [fst snd] in Herr.
  apply orb_prop in Herr as [Hh|Hh]; apply Z.leb_le in Hh; lia.
Qed.
End b.
