(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X01v X047 X0jg.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X0su X0v5 X19x.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0su OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record gdesc := mkGD { gd_beg : Z; gd_size : Z; gd_srz : Z; gd_name : Z; gd_mod : Z; gd_dyn : Z; gd_loc : Z; gd_odr : Z }.

Definition gd_cells (g : gdesc) : list cell :=
[C8 (Z_to_bv 64 (gd_beg g)); C8 (Z_to_bv 64 (gd_size g)); C8 (Z_to_bv 64 (gd_srz g)); C8 (Z_to_bv 64 (gd_name g));
C8 (Z_to_bv 64 (gd_mod g)); C8 (Z_to_bv 64 (gd_dyn g)); C8 (Z_to_bv 64 (gd_loc g)); C8 (Z_to_bv 64 (gd_odr g))].

Fixpoint gds_at (m : mem) (a : Z) (gs : list gdesc) : Prop :=
match gs with
| [] => True
| g :: gs' => ro_cells bsegs m a (gd_cells g) /\ gds_at m (a + 64) gs'
end.

Definition ODR_NONE : Z := 0xffffffffffffffff.

Definition asan_gds : list gdesc := [
mkGD 0x232a0 0x18 0x40 0x1f359 0x23300 0x0 0x0 0xffffffffffffffff;
mkGD 0x232e0 0x6 0x20 0x1d9f9 0x23300 0x0 0x0 0xffffffffffffffff;
mkGD 0x23360 0x27 0x60 0x1d9f9 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x233c0 0x30 0x60 0x205c8 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23420 0x33 0x60 0x22933 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23480 0x1e 0x40 0x14011 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x234c0 0x2b 0x60 0x1eb0d 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23520 0x25 0x60 0x19ac9 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23580 0x12 0x40 0x1bba1 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x235c0 0xd 0x20 0x11794 0x235e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23600 0x20 0x40 0x1d9f9 0x23660 0x0 0x0 0xffffffffffffffff;
mkGD 0x23640 0x10 0x20 0x14011 0x23660 0x0 0x0 0xffffffffffffffff;
mkGD 0x23760 0x10 0x20 0x16608 0x23780 0x0 0x0 0xffffffffffffffff;
mkGD 0x237a0 0x9 0x20 0x1d9f9 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x237c0 0x17 0x40 0x152a2 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23800 0x27 0x60 0x14011 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23860 0x12 0x40 0x19ac9 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x238c0 0xb 0x20 0x1d9f9 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23a80 0x19 0x40 0x1d9f9 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ac0 0x25 0x60 0x205c8 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23b20 0x1c 0x40 0x14692 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23b60 0x20 0x40 0x1f393 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ba0 0x4 0x20 0x146ad 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23bc0 0x8 0x20 0x1e42e 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23be0 0x2c 0x60 0x22933 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23c40 0x28 0x60 0x1eb20 0x23a68 0x0 0x0 0x638141;
mkGD 0x23ca0 0x20 0x40 0x152b9 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ce0 0x33 0x60 0x152a2 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23d40 0x3e 0x60 0x14011 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23da0 0x27 0x60 0x1eb0d 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23e00 0x2e 0x60 0x19ac9 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23e60 0x10 0x20 0x1bba1 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23e80 0x2b 0x60 0x11794 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ee0 0x12 0x40 0x21a00 0x23a68 0x0 0x0 0xffffffffffffffff;
mkGD 0x23f20 0x2c 0x60 0x21a08 0x24360 0x0 0x0 0x638142;
mkGD 0x23f80 0x320 0x3e0 0x1e443 0x24360 0x0 0x0 0x638143;
mkGD 0x24380 0x18c 0x200 0x1eb2c 0x24700 0x0 0x0 0x638144;
mkGD 0x24580 0xdc 0x100 0x1c616 0x24700 0x0 0x0 0x638145;
mkGD 0x24680 0x58 0x80 0x1750a 0x24700 0x0 0x0 0x638146;
mkGD 0x24720 0x3c 0x60 0x1ac98 0x24860 0x0 0x0 0xffffffffffffffff;
mkGD 0x24780 0x3c 0x60 0x18fa1 0x24860 0x0 0x0 0xffffffffffffffff;
mkGD 0x247e0 0x54 0x80 0x12a7b 0x24860 0x0 0x0 0x638147;
mkGD 0x24880 0x280 0x320 0x2102c 0x251a0 0x0 0x0 0x638148;
mkGD 0x24ba0 0x140 0x180 0x146e4 0x251a0 0x0 0x0 0x638149;
mkGD 0x24d20 0x140 0x180 0x15b83 0x251a0 0x0 0x0 0x63814a;
mkGD 0x24ea0 0x140 0x180 0x1b4ab 0x251a0 0x0 0x0 0x63814b;
mkGD 0x25020 0x140 0x180 0x1a200 0x251a0 0x0 0x0 0x63814c;
mkGD 0x251c0 0x200 0x280 0x1359d 0x256c0 0x0 0x0 0x63814d;
mkGD 0x25440 0x200 0x280 0x21a27 0x256c0 0x0 0x0 0x63814e;
mkGD 0x256e0 0x80 0xa0 0x1f3a8 0x25780 0x0 0x0 0x63814f;
mkGD 0x257a0 0xa0 0xc0 0x18fb8 0x25860 0x0 0x0 0x638150;
mkGD 0x25880 0x140 0x180 0x19adc 0x25a00 0x0 0x0 0x638151;
mkGD 0x25a20 0x400 0x500 0x1a20e 0x25f20 0x0 0x0 0x638152;
mkGD 0x25f40 0x200 0x280 0x1da0a 0x261c0 0x0 0x0 0x638153;
mkGD 0x261e0 0x140 0x180 0x146f1 0x26360 0x0 0x0 0x638154;
mkGD 0x26380 0x500 0x640 0x1bbc3 0x269c0 0x0 0x0 0x638155;
mkGD 0x269e0 0x280 0x320 0x20690 0x26d00 0x0 0x0 0x638156;
mkGD 0x26d20 0x19 0x40 0x1d9f9 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26d60 0x20 0x40 0x205c8 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26da0 0x1f 0x40 0x22933 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26de0 0x10 0x20 0x14011 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26fc0 0x19 0x40 0x1d9f9 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27000 0x100 0x140 0x18fc8 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27140 0x80 0xa0 0x1eb85 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x271e0 0x40 0x60 0x2105b 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27240 0x33 0x60 0x205c8 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x272a0 0x10 0x20 0x22933 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x272c0 0x12 0x40 0x14011 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27320 0x140 0x180 0x1eb96 0x274a0 0x0 0x0 0x63815a;
mkGD 0x274c0 0x400 0x500 0x16622 0x279c0 0x0 0x0 0x63815b;
mkGD 0xf8380 0xd0 0x100 0x1f37f 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8480 0x60 0x80 0x10d6d 0x238e0 0x0 0x0 0x638140;
mkGD 0xf8500 0x58 0x80 0x219e8 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8580 0x58 0x80 0x16616 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8600 0x58 0x80 0x219f4 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8680 0x58 0x80 0x14018 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8700 0x58 0x80 0x1d9fe 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8780 0x58 0x80 0x1f387 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8800 0x58 0x80 0x19ad0 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8880 0x58 0x80 0x2293a 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8900 0x10 0x20 0x152a9 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8920 0x18 0x40 0x174f9 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8960 0x10 0x20 0x1bba8 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8980 0x18 0x40 0x18534 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf89c0 0x10 0x20 0x15b58 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf89e0 0x18 0x40 0x12883 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8a20 0x10 0x20 0x10d7b 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8a40 0x18 0x40 0x1eb14 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8a80 0x18 0x40 0x1bbb7 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8ac0 0x18 0x40 0x17dca 0x238e0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8b00 0x60 0x80 0x22248 0x26e00 0x0 0x0 0x638157;
mkGD 0xf8b80 0x60 0x80 0x1c624 0x26e00 0x0 0x0 0x638158;
mkGD 0xf8c00 0x18 0x40 0x152c7 0x26e00 0x0 0x0 0x638159;
mkGD 0xf8c40 0x58 0x80 0x22946 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8cc0 0x58 0x80 0x15b90 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8d40 0x58 0x80 0x117c0 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8dc0 0x58 0x80 0x18544 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8e40 0xd8 0x100 0x1faea 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8f40 0x18 0x40 0x117cc 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8f80 0x18 0x40 0x12032 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf8fc0 0xd8 0x100 0x206a0 0x26e00 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 101%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc654%Z (only parsing).  Notation XS1_HI := 0x7fffcf38%Z (only parsing).
Notation XS2_LO := 0x80017070%Z (only parsing).  Notation XS2_HI := 0x80017218%Z (only parsing).
Notation XS3_LO := 0x80018156%Z (only parsing).  Notation XS3_HI := 0x8001847e%Z (only parsing).

Notation ODR_LO := 0x638140%Z (only parsing).  Notation ODR_HI := 0x63815c%Z (only parsing).  Notation ODR_N := 28%nat (only parsing).
Notation GDS_LO := 0x100ab0%Z (only parsing).  Notation GDS_HI := 0x1023f0%Z (only parsing).  Notation GDS_N := 101%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((ODR_LO <=? o) && (o <? ODR_HI)).

Definition gd_okb (g : gdesc) : bool :=
(0 <=? gd_beg g) && (gd_beg g mod 8 =? 0) && (8 <=? gd_srz g) && (gd_srz g mod 8 =? 0)
&& (gd_beg g + gd_srz g <=? SEGTOP_A) && (gd_srz g / 8 <? 0x10000)
&& in_scratchb (SHB + gd_beg g / 8) (gd_srz g / 8) && odr_okb (gd_odr g)
&& (0 <=? gd_size g) && (gd_size g <? 2^64) && (0 <=? gd_name g) && (gd_name g <? 2^64) && (0 <=? gd_mod g) && (gd_mod g <? 2^64)
&& (0 <=? gd_dyn g) && (gd_dyn g <? 2^64) && (0 <=? gd_loc g) && (gd_loc g <? 2^64).

Lemma asan_gds_ok : Forall (fun g => gd_okb g = true) asan_gds.
Proof.
assert (H : forallb gd_okb asan_gds = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. apply Forall_forall. exact H.
Qed.

Lemma gd_okb_spec : forall g, gd_okb g = true ->
0 <= gd_beg g /\ gd_beg g mod 8 = 0 /\ 8 <= gd_srz g /\ gd_srz g mod 8 = 0 /\ gd_beg g + gd_srz g <= SEGTOP_A
/\ gd_srz g / 8 < 0x10000
/\ ((XS1_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS1_HI)
\/ (XS2_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS2_HI)
\/ (XS3_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS3_HI))
/\ (gd_odr g = ODR_NONE \/ ODR_LO <= gd_odr g < ODR_HI)
/\ 0 <= gd_size g < 2^64 /\ 0 <= gd_name g < 2^64 /\ 0 <= gd_mod g < 2^64 /\ 0 <= gd_dyn g < 2^64 /\ 0 <= gd_loc g < 2^64.
Proof.
intros g H. unfold gd_okb, in_scratchb, odr_okb in H.
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
repeat split; try assumption; lia.
Qed.

Definition XENV_FPA : list (Z * Z) :=
[(0x638bf0, 0x638bf4); (0x658ce8, 0x658d10); (0x658e08, 0x658e10); (0x658f08, 0x658f0c); (0x658f28, 0x658f30);
(0x659390, 0x659398); (0x100898, 0x1008a0); (0x100988, 0x100990); (0x100990, 0x102408); (0x102450, 0x102451);
(0x638140, 0x63815c); (0x658d10, 0x658d18); (0x658e10, 0x658e18); (0x638110, 0x638111)].

Definition XENVC (m : mem) : Prop :=
(exists tid : Z, 1 <= tid < 2^31 /\ rw_cells bsegs m 0x638bf0 [C4 (Z_to_bv 64 tid)])
/\ rw_cells bsegs m 0x658e08 [C8 (Z_to_bv 64 0x85d14)]
/\ rw_cells bsegs m 0x658f08 [C4 (Z_to_bv 64 0)]
/\ (exists (cdt thr sec : byte) (tm1 : word),
rw_cells bsegs m 0x658f28 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
/\ rw_cells bsegs m 0x659390 [C8 (Z_to_bv 64 0)]
/\ rw_cells bsegs m 0x100898 [C8 (Z_to_bv 64 0x1007b0)]
/\ rw_cells bsegs m 0x100988 [C8 (Z_to_bv 64 0x1008a0)]
/\ stdin_file m /\ rw_cells bsegs m 0x100a78 [C8 (Z_to_bv 64 0x100990)]
/\ gds_at m 0x100ab0 asan_gds
/\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells bsegs m 0x102400 [C8 v])
/\ rw_cells bsegs m 0x102450 [C1 (Z_to_bv 8 0)]
/\ (exists os : list byte, rw_cells bsegs m ODR_LO [CB ODR_N os]).

Definition atxA (ph : bool) (m : mem) : Prop :=
(exists p1 p2 : list byte, rw_cells bsegs m 0x658ce8 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x658d00 0 0xe6d8c))
/\ (if ph then rw_cells bsegs m 0x658d10 [C8 (Z_to_bv 64 0xe6d8c)] /\ rw_cells bsegs m 0x658e10 [C8 (Z_to_bv 64 0x966dc)]
else (exists j1 : word, rw_cells bsegs m 0x658d10 [C8 j1]) /\ (exists j2 : word, rw_cells bsegs m 0x658e10 [C8 j2])
/\ rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 0)]).

Definition XENVA_ph (ph : bool) (m : mem) : Prop := XENVC m /\ atxA ph m.
Definition XENVA : mem -> Prop := XENVA_ph false.
Definition XENVA1 : mem -> Prop := XENVA_ph true.
Definition XENVA1x (m : mem) : Prop := XENVA1 m /\ rw_cells bsegs m TR_INIT [C1 (Z_to_bv 8 0)].

Lemma XENVA1x_of : forall m, XENVA1 m -> rw_cells bsegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENVA1x m.
Proof. intros m H1 H2. exact (conj H1 H2). Qed.

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma gds_at_agree : forall gs m m' a, gds_at m a gs ->
agree_on (fun x => a <= x < a + 64 * Z.of_nat (length gs)) m m' -> gds_at m' a gs.
Proof.
induction gs as [|g gs IH]; intros m m' a H AG; [exact I|]. destruct H as [H1 H2]. split.
- apply (ro_cells_agree bsegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
- apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Local Ltac DJ := intros xd Hxd Hrd; apply in_REG_CELLS in Hrd; lia.

Lemma XENVC_loc' : forall m m', XENVC m ->
(forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) -> XENVC m'.
Proof.
intros m m' (TID & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR) AG.
assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> (forall x, lo <= x < hi -> ~ in_ranges REG_CELLS x) -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
{ intros lo hi cs A Hin HD H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
intros a Ha. pose proof (rw_cells_bound bsegs m _ _ H). apply AG; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| apply HD; lia]. }
split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x638bf0 0x638bf4); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
split; [apply (R 0x658e08 0x658e10); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
split; [apply (R 0x658f08 0x658f0c); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x658f28 0x658f30); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
split; [apply (R 0x659390 0x659398); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
split; [apply (R 0x100898 0x1008a0); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
split; [apply (R 0x100988 0x100990); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0x100990 0x102408); [cbn; tauto| DJ| lia| | exact C];
destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
split; [apply (R 0x100990 0x102408); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
apply AG; [apply (in_XENV_FPA 0x100990 0x102408); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0x100990 0x102408); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
split; [apply (R 0x102450 0x102451); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
destruct ODR as (os & C). exists os. apply (R 0x638140 0x63815c); [cbn; tauto| DJ| lia| | exact C].
destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia.
Qed.

Lemma XENVC_loc : fp_local XENV_FPA XENVC.
Proof. intros m m' H AG. apply (XENVC_loc' m m' H). intros a Ha _. exact (AG a Ha). Qed.

Lemma atxA_loc : forall ph, fp_local XENV_FPA (atxA ph).
Proof.
intros ph m m' ((p1 & p2 & ATX) & PH) AG.
assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
rw_cells bsegs m A cs -> rw_cells bsegs m' A cs).
{ intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw bsegs m m' _ _ H).
intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
split; [exists p1, p2; apply (R 0x658ce8 0x658d10); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
destruct ph.
- destruct PH as [PF PA]. split; [apply (R 0x658d10 0x658d18); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x658e10 0x658e18); [cbn; tauto| lia| cbn; lia| exact PA]].
- destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
+ exists j1. apply (R 0x658d10 0x658d18); [cbn; tauto| lia| cbn; lia| exact PF].
+ exists j2. apply (R 0x658e10 0x658e18); [cbn; tauto| lia| cbn; lia| exact PA].
+ apply (R 0x638110 0x638111); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
Qed.

Lemma XENV_locA_ph : forall ph, fp_local XENV_FPA (XENVA_ph ph).
Proof. intros ph m m' [HC HA] AG. split; [exact (XENVC_loc m m' HC AG)| exact (atxA_loc ph m m' HA AG)]. Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof. exact (XENV_locA_ph false). Qed.

Lemma XENV_locA1 : fp_local XENV_FPA XENVA1.
Proof. exact (XENV_locA_ph true). Qed.

Lemma REG_fpA : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FPA x.
Proof.
intros x Hx. apply in_REG_CELLS in Hx.
destruct Hx as [H|[H|[H|H]]];
[apply (in_XENV_FPA 0x638110 0x638111)| apply (in_XENV_FPA 0x658ce8 0x658d10)| apply (in_XENV_FPA 0x658d10 0x658d18)| apply (in_XENV_FPA 0x658e10 0x658e18)];
first [cbn; tauto| lia].
Qed.

Lemma XENVA_reg_out : forall m, XENVA m -> reg_pre m.
Proof.
intros m (HC & (p1 & p2 & ATX) & (j1 & PF) & (j2 & PA) & PL).
destruct HC as (TID & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & _).
exists p1, p2, cdt, thr, sec, tm1, j1, j2. cbn [ph_slot] in ATX.
split; [exact ATX|]. split; [exact PF|]. split; [exact PA|]. split; [exact LIBC| exact PL].
Qed.

Lemma XENVA_reg_in : forall m m', XENVA m ->
(forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
reg_post m' -> XENVA1 m'.
Proof.
intros m m' [HC _] AG (p1 & p2 & ATX & PF & PA & PL). split.
- exact (XENVC_loc' m m' HC AG).
- split; [exists p1, p2; exact ATX|]. cbn. split; [exact PF| exact PA].
Qed.

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
intros x (lo & hi & Hin & Hx). cbn in Hin.
split; [| split; [| split]].
- apply client_static_intro.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
- unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
- unfold IO_FPA. cbn.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
- unfold LIB_FP. cbn.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

Definition xit_rt (m : mem) : Prop :=
ro_cells bsegs m 0xf7f78 [C8 (Z_to_bv 64 0x97744); C8 (Z_to_bv 64 0x44a64)]
/\ ro_cells bsegs m 0xfce88 [C8 (Z_to_bv 64 0xf7f88); C8 (Z_to_bv 64 0xf7f78)]
/\ ro_cells bsegs m 0xfc0e8 [C8 (Z_to_bv 64 0xe6cc4); C8 (Z_to_bv 64 0)]
/\ (exists d : word, ro_cells bsegs m 0xfdec8 [C8 d])
/\ ro_cells bsegs m 0xfce00 [C8 (Z_to_bv 64 0x100ab0); C8 (Z_to_bv 64 0x1023f0)]
/\ ro_cells bsegs m 0xfc0f8 [C8 (Z_to_bv 64 0x195560)]
/\ ro_cells bsegs m 0xfc108 [C8 (Z_to_bv 64 0x1975e8); C8 (Z_to_bv 64 0x1032b8); C8 (Z_to_bv 64 0x105ab8);
C8 (Z_to_bv 64 0x1067a8); C8 (Z_to_bv 64 0x1067b0); C8 (Z_to_bv 64 0x1067a0);
C8 (Z_to_bv 64 0xfe040)]

/\ ro_cells bsegs m 0x1032d0 [C4 (Z_to_bv 64 1)]
/\ rw_cells bsegs m 0x103370 [C8 (Z_to_bv 64 0)]
/\ ro_cells bsegs m 0x105ab8 [C8 (Z_to_bv 64 0x7fff8000)]
/\ rw_cells bsegs m 0x106798 [C1 (Z_to_bv 8 1)]
/\ ro_cells bsegs m 0x10531c [C1 (Z_to_bv 8 1)]
/\ ro_cells bsegs m 0x197660 [C8 (Z_to_bv 64 0xffffffffffffffff)]
/\ ro_cells bsegs m 0xfe040 [C8 (Z_to_bv 64 0xf1af8)]
/\ ro_cells bsegs m 0x197960 [C1 (Z_to_bv 8 0)]
/\ stk bsegs m XS1_LO XS1_HI /\ stk bsegs m XS2_LO XS2_HI /\ stk bsegs m XS3_LO XS3_HI.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record gdesc := mkGD { gd_beg : Z; gd_size : Z; gd_srz : Z; gd_name : Z; gd_mod : Z; gd_dyn : Z; gd_loc : Z; gd_odr : Z }.

Definition gd_cells (g : gdesc) : list cell :=
[C8 (Z_to_bv 64 (gd_beg g)); C8 (Z_to_bv 64 (gd_size g)); C8 (Z_to_bv 64 (gd_srz g)); C8 (Z_to_bv 64 (gd_name g));
C8 (Z_to_bv 64 (gd_mod g)); C8 (Z_to_bv 64 (gd_dyn g)); C8 (Z_to_bv 64 (gd_loc g)); C8 (Z_to_bv 64 (gd_odr g))].

Fixpoint gds_at (m : mem) (a : Z) (gs : list gdesc) : Prop :=
match gs with
| [] => True
| g :: gs' => ro_cells asegs m a (gd_cells g) /\ gds_at m (a + 64) gs'
end.

Definition ODR_NONE : Z := 0xffffffffffffffff.

Definition asan_gds : list gdesc := [
mkGD 0x23260 0x18 0x40 0x1f31f 0x232c0 0x0 0x0 0xffffffffffffffff;
mkGD 0x232a0 0x6 0x20 0x1d9bf 0x232c0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23320 0x27 0x60 0x1d9bf 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23380 0x30 0x60 0x2058e 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x233e0 0x33 0x60 0x228f9 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23440 0x1e 0x40 0x13fd4 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23480 0x2b 0x60 0x1ead3 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x234e0 0x25 0x60 0x199e0 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23540 0x12 0x40 0x1bab8 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23580 0xd 0x20 0x1177c 0x235a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x235c0 0x20 0x40 0x1d9bf 0x23620 0x0 0x0 0xffffffffffffffff;
mkGD 0x23600 0x10 0x20 0x13fd4 0x23620 0x0 0x0 0xffffffffffffffff;
mkGD 0x23720 0x10 0x20 0x16518 0x23740 0x0 0x0 0xffffffffffffffff;
mkGD 0x23760 0x9 0x20 0x1d9bf 0x23860 0x0 0x0 0xffffffffffffffff;
mkGD 0x23780 0x17 0x40 0x151b2 0x23860 0x0 0x0 0xffffffffffffffff;
mkGD 0x237c0 0x27 0x60 0x13fd4 0x23860 0x0 0x0 0xffffffffffffffff;
mkGD 0x23820 0x12 0x40 0x199e0 0x23860 0x0 0x0 0xffffffffffffffff;
mkGD 0x23880 0xb 0x20 0x1d9bf 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0x23a40 0x19 0x40 0x1d9bf 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23a80 0x25 0x60 0x2058e 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ae0 0xa 0x20 0x228f9 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23b00 0x1c 0x40 0x14655 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23b40 0x20 0x40 0x1f359 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23b80 0x4 0x20 0x14670 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ba0 0x8 0x20 0x1e3f4 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23bc0 0x2c 0x60 0x151b2 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23c20 0x28 0x60 0x1eae6 0x23f00 0x0 0x0 0x62f901;
mkGD 0x23c80 0x20 0x40 0x151c9 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23cc0 0x33 0x60 0x13fd4 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23d20 0x3e 0x60 0x1ead3 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23d80 0x27 0x60 0x199e0 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23de0 0x2e 0x60 0x1bab8 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23e40 0x10 0x20 0x1177c 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23e60 0x2b 0x60 0x1741a 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23ec0 0x12 0x40 0x219c6 0x23f00 0x0 0x0 0xffffffffffffffff;
mkGD 0x23f20 0x2c 0x60 0x219ce 0x24360 0x0 0x0 0x62f902;
mkGD 0x23f80 0x320 0x3e0 0x1e409 0x24360 0x0 0x0 0x62f903;
mkGD 0x24380 0x18c 0x200 0x1eaf2 0x24700 0x0 0x0 0x62f904;
mkGD 0x24580 0xdc 0x100 0x1c634 0x24700 0x0 0x0 0x62f905;
mkGD 0x24680 0x58 0x80 0x17421 0x24700 0x0 0x0 0x62f906;
mkGD 0x24720 0x3c 0x60 0x1abaf 0x24860 0x0 0x0 0xffffffffffffffff;
mkGD 0x24780 0x3c 0x60 0x18eb8 0x24860 0x0 0x0 0xffffffffffffffff;
mkGD 0x247e0 0x54 0x80 0x12a3e 0x24860 0x0 0x0 0x62f907;
mkGD 0x24880 0x280 0x320 0x20ff2 0x251a0 0x0 0x0 0x62f908;
mkGD 0x24ba0 0x140 0x180 0x146a7 0x251a0 0x0 0x0 0x62f909;
mkGD 0x24d20 0x140 0x180 0x15a93 0x251a0 0x0 0x0 0x62f90a;
mkGD 0x24ea0 0x140 0x180 0x1b3c2 0x251a0 0x0 0x0 0x62f90b;
mkGD 0x25020 0x140 0x180 0x1a117 0x251a0 0x0 0x0 0x62f90c;
mkGD 0x251c0 0x200 0x280 0x13560 0x256c0 0x0 0x0 0x62f90d;
mkGD 0x25440 0x200 0x280 0x219ed 0x256c0 0x0 0x0 0x62f90e;
mkGD 0x256e0 0x80 0xa0 0x1f36e 0x25780 0x0 0x0 0x62f90f;
mkGD 0x257a0 0xa0 0xc0 0x18ecf 0x25860 0x0 0x0 0x62f910;
mkGD 0x25880 0x140 0x180 0x199f3 0x25a00 0x0 0x0 0x62f911;
mkGD 0x25a20 0x400 0x500 0x1a125 0x25f20 0x0 0x0 0x62f912;
mkGD 0x25f40 0x200 0x280 0x1d9d0 0x261c0 0x0 0x0 0x62f913;
mkGD 0x261e0 0x140 0x180 0x146b4 0x26360 0x0 0x0 0x62f914;
mkGD 0x26380 0x500 0x640 0x1bada 0x269c0 0x0 0x0 0x62f915;
mkGD 0x269e0 0x280 0x320 0x20656 0x26d00 0x0 0x0 0x62f916;
mkGD 0x26d20 0x19 0x40 0x1d9bf 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26d60 0x20 0x40 0x2058e 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26da0 0x1f 0x40 0x228f9 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26de0 0x10 0x20 0x13fd4 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0x26fc0 0x19 0x40 0x1d9bf 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27000 0x100 0x140 0x18edf 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27140 0x80 0xa0 0x1eb4b 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x271e0 0x40 0x60 0x21021 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27240 0x33 0x60 0x2058e 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x272a0 0x10 0x20 0x228f9 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x272c0 0x12 0x40 0x151b2 0x27300 0x0 0x0 0xffffffffffffffff;
mkGD 0x27320 0x140 0x180 0x1eb5c 0x274a0 0x0 0x0 0x62f91a;
mkGD 0x274c0 0x400 0x500 0x16532 0x279c0 0x0 0x0 0x62f91b;
mkGD 0xefb00 0xd0 0x100 0x1f345 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xefc00 0x60 0x80 0x10d55 0x238a0 0x0 0x0 0x62f900;
mkGD 0xefc80 0x58 0x80 0x219ae 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xefd00 0x58 0x80 0x16526 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xefd80 0x58 0x80 0x219ba 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xefe00 0x58 0x80 0x13fdb 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xefe80 0x58 0x80 0x1d9c4 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xeff00 0x58 0x80 0x1f34d 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xeff80 0x58 0x80 0x199e7 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0000 0x58 0x80 0x22900 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0080 0x10 0x20 0x151b9 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf00a0 0x18 0x40 0x17409 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf00e0 0x10 0x20 0x1babf 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0100 0x18 0x40 0x1844b 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0140 0x10 0x20 0x15a68 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0160 0x18 0x40 0x12846 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf01a0 0x10 0x20 0x10d63 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf01c0 0x18 0x40 0x1eada 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0200 0x18 0x40 0x1bace 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0240 0x18 0x40 0x17ce1 0x238a0 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0280 0x60 0x80 0x2220e 0x26e00 0x0 0x0 0x62f917;
mkGD 0xf0300 0x60 0x80 0x1c642 0x26e00 0x0 0x0 0x62f918;
mkGD 0xf0380 0x18 0x40 0x151d7 0x26e00 0x0 0x0 0x62f919;
mkGD 0xf03c0 0x58 0x80 0x2290c 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0440 0x58 0x80 0x15aa0 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf04c0 0x58 0x80 0x11783 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0540 0x58 0x80 0x1845b 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf05c0 0xd8 0x100 0x1fab0 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf06c0 0x18 0x40 0x1178f 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0700 0x18 0x40 0x11ff5 0x26e00 0x0 0x0 0xffffffffffffffff;
mkGD 0xf0740 0xd8 0x100 0x20666 0x26e00 0x0 0x0 0xffffffffffffffff ].

Lemma asan_gds_length : length asan_gds = 102%nat.
Proof. reflexivity. Qed.

Notation XS1_LO := 0x7fffc64c%Z (only parsing).  Notation XS1_HI := 0x7fffcf38%Z (only parsing).
Notation XS2_LO := 0x80015f60%Z (only parsing).  Notation XS2_HI := 0x80016108%Z (only parsing).
Notation XS3_LO := 0x80017046%Z (only parsing).  Notation XS3_HI := 0x80017376%Z (only parsing).

Notation ODR_LO := 0x62f900%Z (only parsing).  Notation ODR_HI := 0x62f91c%Z (only parsing).  Notation ODR_N := 28%nat (only parsing).
Notation GDS_LO := 0xf8230%Z (only parsing).  Notation GDS_HI := 0xf9bb0%Z (only parsing).  Notation GDS_N := 102%Z (only parsing).

Definition in_scratchb (d n : Z) : bool :=
((XS1_LO <=? d) && (d + n <=? XS1_HI)) || ((XS2_LO <=? d) && (d + n <=? XS2_HI)) || ((XS3_LO <=? d) && (d + n <=? XS3_HI)).

Definition odr_okb (o : Z) : bool := (o =? ODR_NONE) || ((ODR_LO <=? o) && (o <? ODR_HI)).

Definition gd_okb (g : gdesc) : bool :=
(0 <=? gd_beg g) && (gd_beg g mod 8 =? 0) && (8 <=? gd_srz g) && (gd_srz g mod 8 =? 0)
&& (gd_beg g + gd_srz g <=? SEGTOP_A) && (gd_srz g / 8 <? 0x10000)
&& in_scratchb (SHB + gd_beg g / 8) (gd_srz g / 8) && odr_okb (gd_odr g)
&& (0 <=? gd_size g) && (gd_size g <? 2^64) && (0 <=? gd_name g) && (gd_name g <? 2^64) && (0 <=? gd_mod g) && (gd_mod g <? 2^64)
&& (0 <=? gd_dyn g) && (gd_dyn g <? 2^64) && (0 <=? gd_loc g) && (gd_loc g <? 2^64).

Lemma asan_gds_ok : Forall (fun g => gd_okb g = true) asan_gds.
Proof.
assert (H : forallb gd_okb asan_gds = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. apply Forall_forall. exact H.
Qed.

Lemma gd_okb_spec : forall g, gd_okb g = true ->
0 <= gd_beg g /\ gd_beg g mod 8 = 0 /\ 8 <= gd_srz g /\ gd_srz g mod 8 = 0 /\ gd_beg g + gd_srz g <= SEGTOP_A
/\ gd_srz g / 8 < 0x10000
/\ ((XS1_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS1_HI)
\/ (XS2_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS2_HI)
\/ (XS3_LO <= SHB + gd_beg g / 8 /\ SHB + gd_beg g / 8 + gd_srz g / 8 <= XS3_HI))
/\ (gd_odr g = ODR_NONE \/ ODR_LO <= gd_odr g < ODR_HI)
/\ 0 <= gd_size g < 2^64 /\ 0 <= gd_name g < 2^64 /\ 0 <= gd_mod g < 2^64 /\ 0 <= gd_dyn g < 2^64 /\ 0 <= gd_loc g < 2^64.
Proof.
intros g H. unfold gd_okb, in_scratchb, odr_okb in H.
repeat match goal with H : _ && _ = true |- _ => apply andb_prop in H; destruct H end.
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
repeat split; try assumption; lia.
Qed.

Definition XENV_FPA : list (Z * Z) :=
[(0x6303b0, 0x6303b4); (0x6504a8, 0x6504d0); (0x6505c8, 0x6505d0); (0x6506c8, 0x6506cc); (0x6506e8, 0x6506f0);
(0x650b50, 0x650b58); (0xf8018, 0xf8020); (0xf8108, 0xf8110); (0xf8110, 0xf9bc8); (0xf9c10, 0xf9c11);
(0x62f900, 0x62f91c); (0x6504d0, 0x6504d8); (0x6505d0, 0x6505d8); (0x62f8d0, 0x62f8d1)].

Definition XENVC (m : mem) : Prop :=
(exists tid : Z, 1 <= tid < 2^31 /\ rw_cells asegs m 0x6303b0 [C4 (Z_to_bv 64 tid)])
/\ rw_cells asegs m 0x6505c8 [C8 (Z_to_bv 64 0x85c28)]
/\ rw_cells asegs m 0x6506c8 [C4 (Z_to_bv 64 0)]
/\ (exists (cdt thr sec : byte) (tm1 : word),
rw_cells asegs m 0x6506e8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
/\ rw_cells asegs m 0x650b50 [C8 (Z_to_bv 64 0)]
/\ rw_cells asegs m 0xf8018 [C8 (Z_to_bv 64 0xf7f30)]
/\ rw_cells asegs m 0xf8108 [C8 (Z_to_bv 64 0xf8020)]
/\ stdin_file m /\ rw_cells asegs m 0xf81f8 [C8 (Z_to_bv 64 0xf8110)]
/\ gds_at m 0xf8230 asan_gds
/\ (exists v : word, bv_unsigned v <> 0 /\ rw_cells asegs m 0xf9bc0 [C8 v])
/\ rw_cells asegs m 0xf9c10 [C1 (Z_to_bv 8 0)]
/\ (exists os : list byte, rw_cells asegs m ODR_LO [CB ODR_N os]).

Definition atxA (ph : bool) (m : mem) : Prop :=
(exists p1 p2 : list byte, rw_cells asegs m 0x6504a8 (atexit_cells (Z_to_bv 8 0) p1 p2 (ph_slot ph) 0x6504c0 0 0xde65c))
/\ (if ph then rw_cells asegs m 0x6504d0 [C8 (Z_to_bv 64 0xde65c)] /\ rw_cells asegs m 0x6505d0 [C8 (Z_to_bv 64 0x965f0)]
else (exists j1 : word, rw_cells asegs m 0x6504d0 [C8 j1]) /\ (exists j2 : word, rw_cells asegs m 0x6505d0 [C8 j2])
/\ rw_cells asegs m TR_LATCH [C1 (Z_to_bv 8 0)]).

Definition XENVA_ph (ph : bool) (m : mem) : Prop := XENVC m /\ atxA ph m.
Definition XENVA : mem -> Prop := XENVA_ph false.
Definition XENVA1 : mem -> Prop := XENVA_ph true.
Definition XENVA1x (m : mem) : Prop := XENVA1 m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].

Lemma XENVA1x_of : forall m, XENVA1 m -> rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)] -> XENVA1x m.
Proof. intros m H1 H2. exact (conj H1 H2). Qed.

Lemma in_XENV_FPA : forall lo hi x, In (lo, hi) XENV_FPA -> lo <= x < hi -> in_ranges XENV_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma gds_at_agree : forall gs m m' a, gds_at m a gs ->
agree_on (fun x => a <= x < a + 64 * Z.of_nat (length gs)) m m' -> gds_at m' a gs.
Proof.
induction gs as [|g gs IH]; intros m m' a H AG; [exact I|]. destruct H as [H1 H2]. split.
- apply (ro_cells_agree asegs m m' _ _ H1). apply (agree_sub _ _ _ _ AG). intros x Hx. unfold gd_cells in Hx.
cbn [cells_size csize Nat.add] in Hx. cbn [length]. lia.
- apply (IH m m' (a + 64) H2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length]. lia.
Qed.

Local Ltac DJ := intros xd Hxd Hrd; apply in_REG_CELLS in Hrd; lia.

Lemma XENVC_loc' : forall m m', XENVC m ->
(forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) -> XENVC m'.
Proof.
intros m m' (TID & ATA & EXL & LIBC & OFL & SEU & SOU & SIN & SINU & GDS & FLG & CPL & ODR) AG.
assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> (forall x, lo <= x < hi -> ~ in_ranges REG_CELLS x) -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
rw_cells asegs m A cs -> rw_cells asegs m' A cs).
{ intros lo hi cs A Hin HD H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
intros a Ha. pose proof (rw_cells_bound asegs m _ _ H). apply AG; [apply (in_XENV_FPA lo hi); [exact Hin| lia]| apply HD; lia]. }
split; [destruct TID as (t & Ht & C); exists t; split; [exact Ht| apply (R 0x6303b0 0x6303b4); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
split; [apply (R 0x6505c8 0x6505d0); [cbn; tauto| DJ| lia| cbn; lia| exact ATA]|].
split; [apply (R 0x6506c8 0x6506cc); [cbn; tauto| DJ| lia| cbn; lia| exact EXL]|].
split; [destruct LIBC as (c1 & c2 & c3 & t & C); exists c1, c2, c3, t; apply (R 0x6506e8 0x6506f0); [cbn; tauto| DJ| lia| cbn; lia| exact C]|].
split; [apply (R 0x650b50 0x650b58); [cbn; tauto| DJ| lia| cbn; lia| exact OFL]|].
split; [apply (R 0xf8018 0xf8020); [cbn; tauto| DJ| lia| cbn; lia| exact SEU]|].
split; [apply (R 0xf8108 0xf8110); [cbn; tauto| DJ| lia| cbn; lia| exact SOU]|].
split; [destruct SIN as (j0 & j1 & j2 & j3 & j4 & C); exists j0, j1, j2, j3, j4; apply (R 0xf8110 0xf9bc8); [cbn; tauto| DJ| lia| | exact C];
destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia|].
split; [apply (R 0xf8110 0xf9bc8); [cbn; tauto| DJ| lia| cbn; lia| exact SINU]|].
split; [apply (gds_at_agree _ m m' _ GDS); intros a Ha; rewrite asan_gds_length in Ha; cbn in Ha;
apply AG; [apply (in_XENV_FPA 0xf8110 0xf9bc8); [cbn; tauto| lia]| intros Hr; apply in_REG_CELLS in Hr; lia]|].
split; [destruct FLG as (v & Hv & C); exists v; split; [exact Hv| apply (R 0xf8110 0xf9bc8); [cbn; tauto| DJ| lia| cbn; lia| exact C]]|].
split; [apply (R 0xf9c10 0xf9c11); [cbn; tauto| DJ| lia| cbn; lia| exact CPL]|].
destruct ODR as (os & C). exists os. apply (R 0x62f900 0x62f91c); [cbn; tauto| DJ| lia| | exact C].
destruct C as [[Hw _] _]; cbn in Hw; cbn [cells_size csize]; lia.
Qed.

Lemma XENVC_loc : fp_local XENV_FPA XENVC.
Proof. intros m m' H AG. apply (XENVC_loc' m m' H). intros a Ha _. exact (AG a Ha). Qed.

Lemma atxA_loc : forall ph, fp_local XENV_FPA (atxA ph).
Proof.
intros ph m m' ((p1 & p2 & ATX) & PH) AG.
assert (R : forall lo hi cs A, In (lo, hi) XENV_FPA -> lo <= A -> A + Z.of_nat (cells_size cs) <= hi ->
rw_cells asegs m A cs -> rw_cells asegs m' A cs).
{ intros lo hi cs A Hin H1 H2 H. apply (rw_cells_agree_nw asegs m m' _ _ H).
intros a Ha. apply AG. apply (in_XENV_FPA lo hi); [exact Hin| lia]. }
split; [exists p1, p2; apply (R 0x6504a8 0x6504d0); [cbn; tauto| lia| | exact ATX]; destruct ATX as [[Hw _] _];
unfold atexit_cells in Hw |- *; cbn in Hw; cbn [cells_size csize]; lia|].
destruct ph.
- destruct PH as [PF PA]. split; [apply (R 0x6504d0 0x6504d8); [cbn; tauto| lia| cbn; lia| exact PF]| apply (R 0x6505d0 0x6505d8); [cbn; tauto| lia| cbn; lia| exact PA]].
- destruct PH as ((j1 & PF) & (j2 & PA) & PL). split; [| split].
+ exists j1. apply (R 0x6504d0 0x6504d8); [cbn; tauto| lia| cbn; lia| exact PF].
+ exists j2. apply (R 0x6505d0 0x6505d8); [cbn; tauto| lia| cbn; lia| exact PA].
+ apply (R 0x62f8d0 0x62f8d1); [cbn; tauto| unfold TR_LATCH; lia| unfold TR_LATCH; cbn; lia| exact PL].
Qed.

Lemma XENV_locA_ph : forall ph, fp_local XENV_FPA (XENVA_ph ph).
Proof. intros ph m m' [HC HA] AG. split; [exact (XENVC_loc m m' HC AG)| exact (atxA_loc ph m m' HA AG)]. Qed.

Lemma XENV_locA : fp_local XENV_FPA XENVA.
Proof. exact (XENV_locA_ph false). Qed.

Lemma XENV_locA1 : fp_local XENV_FPA XENVA1.
Proof. exact (XENV_locA_ph true). Qed.

Lemma REG_fpA : forall x, in_ranges REG_CELLS x -> in_ranges XENV_FPA x.
Proof.
intros x Hx. apply in_REG_CELLS in Hx.
destruct Hx as [H|[H|[H|H]]];
[apply (in_XENV_FPA 0x62f8d0 0x62f8d1)| apply (in_XENV_FPA 0x6504a8 0x6504d0)| apply (in_XENV_FPA 0x6504d0 0x6504d8)| apply (in_XENV_FPA 0x6505d0 0x6505d8)];
first [cbn; tauto| lia].
Qed.

Lemma XENVA_reg_out : forall m, XENVA m -> reg_pre m.
Proof.
intros m (HC & (p1 & p2 & ATX) & (j1 & PF) & (j2 & PA) & PL).
destruct HC as (TID & ATA & EXL & (cdt & thr & sec & tm1 & LIBC) & _).
exists p1, p2, cdt, thr, sec, tm1, j1, j2. cbn [ph_slot] in ATX.
split; [exact ATX|]. split; [exact PF|]. split; [exact PA|]. split; [exact LIBC| exact PL].
Qed.

Lemma XENVA_reg_in : forall m m', XENVA m ->
(forall a : word, in_ranges XENV_FPA (bv_unsigned a) -> ~ in_ranges REG_CELLS (bv_unsigned a) -> m' a = m a) ->
reg_post m' -> XENVA1 m'.
Proof.
intros m m' [HC _] AG (p1 & p2 & ATX & PF & PA & PL). split.
- exact (XENVC_loc' m m' HC AG).
- split; [exists p1, p2; exact ATX|]. cbn. split; [exact PF| exact PA].
Qed.

Lemma XENV_imgA : forall x, in_ranges XENV_FPA x -> client_static x /\ ~ drv_cell x /\ outside IO_FPA x /\ outside LIB_FP x.
Proof.
intros x (lo & hi & Hin & Hx). cbn in Hin.
split; [| split; [| split]].
- apply client_static_intro.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
- unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
- unfold IO_FPA. cbn.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (split; [lia| split; [lia| split; [lia| exact I]]])|]). destruct Hin.
- unfold LIB_FP. cbn.
repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat (split; [lia|])); try exact I|]). destruct Hin.
Qed.

Definition xit_rt (m : mem) : Prop :=
ro_cells asegs m 0xef708 [C8 (Z_to_bv 64 0x97490); C8 (Z_to_bv 64 0x44978)]
/\ ro_cells asegs m 0xf4608 [C8 (Z_to_bv 64 0xef718); C8 (Z_to_bv 64 0xef708)]
/\ ro_cells asegs m 0xf3868 [C8 (Z_to_bv 64 0xde594); C8 (Z_to_bv 64 0)]
/\ (exists d : word, ro_cells asegs m 0xf5648 [C8 d])
/\ ro_cells asegs m 0xf4580 [C8 (Z_to_bv 64 0xf8230); C8 (Z_to_bv 64 0xf9bb0)]
/\ ro_cells asegs m 0xf3878 [C8 (Z_to_bv 64 0x18cd20)]
/\ ro_cells asegs m 0xf3888 [C8 (Z_to_bv 64 0x18eda8); C8 (Z_to_bv 64 0xfaa78); C8 (Z_to_bv 64 0xfd278);
C8 (Z_to_bv 64 0xfdf68); C8 (Z_to_bv 64 0xfdf70); C8 (Z_to_bv 64 0xfdf60);
C8 (Z_to_bv 64 0xf57c0)]

/\ ro_cells asegs m 0xfaa90 [C4 (Z_to_bv 64 1)]
/\ rw_cells asegs m 0xfab30 [C8 (Z_to_bv 64 0)]
/\ ro_cells asegs m 0xfd278 [C8 (Z_to_bv 64 0x7fff8000)]
/\ rw_cells asegs m 0xfdf58 [C1 (Z_to_bv 8 1)]
/\ ro_cells asegs m 0xfcadc [C1 (Z_to_bv 8 1)]
/\ ro_cells asegs m 0x18ee20 [C8 (Z_to_bv 64 0xffffffffffffffff)]
/\ ro_cells asegs m 0xf57c0 [C8 (Z_to_bv 64 0xe9284)]
/\ ro_cells asegs m 0x18f120 [C1 (Z_to_bv 8 0)]
/\ stk asegs m XS1_LO XS1_HI /\ stk asegs m XS2_LO XS2_HI /\ stk asegs m XS3_LO XS3_HI.
