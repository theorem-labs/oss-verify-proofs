(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB13.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB13.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AB13.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AB13.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AB13.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.reac_pw.fuzz_headamp.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK04 YK1b YK07.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v.
Local Notation TSEGS := tfibsegs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma tfib_segs_eq : TSEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.
Lemma tfib_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5619712 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5619712%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_rw_window : forall m (x : word),
0x9c000 <= bv_unsigned x < 0x5fa000 -> wview TSEGS m x <> None.
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment TSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite tfib_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
AsanUbsan_segment_000 AsanUbsan_segment_001
AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 8192); [exact tfib_hex2 | rewrite tfib_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5619712); [exact tfib_hex3 | rewrite tfib_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x9e000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
[rewrite tfib_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
[rewrite tfib_segs_eq; cbn; tauto | cbn; lia].
Qed.
Definition TFIB_BSS : Z * Z := (0xa1b60, 0x5fa000).
Definition byte_is0 (s : PrimString.string) (off : N) : bool :=
match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
match fuel with
| O => N.eqb n 0
| S f =>
if N.eqb n 0 then true
else if N.eqb n 1 then byte_is0 s base
else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
end.
Lemma zscanN_sound : forall s fuel base n,
zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
- apply N.eqb_eq in H. lia.
- destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
destruct (N.eqb_spec n 1) as [E1|Hn1].
+ subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_is0 in H.
destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq.
rewrite H. reflexivity.
+ apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *. set (h := (n / 2)%N) in *.
destruct (N.lt_ge_cases i h) as [Hl|Hge].
* exact (IH _ _ H1 i Hl).
* specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.
Lemma tfib_zero3 : zscanN AsanUbsan_seg_bytes_003 64 15200 5604512 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_rom3 : forall x, 0x9e000 <= x < 0x5fa000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at AsanUbsan_seg_bytes_003 (Z.to_N (x - 0x9e000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 131072))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((196608 <=? x) && (x + 1 <=? 196608 + 442368))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((638976 <=? x) && (x + 1 <=? 638976 + 8192))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((647168 <=? x) && (x + 1 <=? 647168 + 5619712))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len3.
replace (Z.to_N (x - 647168) <? 5619712)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at AsanUbsan_seg_bytes_003 (Z.to_N (x - 647168))); reflexivity.
Qed.
Lemma tfib_bss_rom : forall x, fst TFIB_BSS <= x < snd TFIB_BSS -> seg_rom TSEGS (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
intros x Hx. cbn [fst snd TFIB_BSS] in Hx. rewrite tfib_rom3 by lia.
replace (Z.to_N (x - 0x9e000)) with (15200 + Z.to_N (x - 0xa1b60))%N by lia.
apply (zscanN_sound _ _ _ _ tfib_zero3). lia.
Qed.
Lemma tfib_rom2 : forall x, 0x9c000 <= x < 0x9e000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at AsanUbsan_seg_bytes_002 (Z.to_N (x - 0x9c000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 131072))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((196608 <=? x) && (x + 1 <=? 196608 + 442368))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((638976 <=? x) && (x + 1 <=? 638976 + 8192))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len2.
replace (Z.to_N (x - 638976) <? 8192)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at AsanUbsan_seg_bytes_002 (Z.to_N (x - 638976))); reflexivity.
Qed.
Lemma tfib_rw_rom : forall x, 0x9c000 <= x < 0x5fa000 -> seg_rom TSEGS (Z_to_bv 64 x) <> None.
Proof.
intros x Hx. destruct (Z.lt_ge_cases x 0x9e000) as [Hl|Hl].
- rewrite tfib_rom2 by lia. exact (scanN_sound _ 64 0 8192 tfib_hex2 (Z.to_N (x - 0x9c000)) ltac:(lia)).
- rewrite tfib_rom3 by lia. exact (scanN_sound _ 64 0 5619712 tfib_hex3 (Z.to_N (x - 0x9e000)) ltac:(lia)).
Qed.
Lemma tfib_hex0 : scanN AsanUbsan_seg_bytes_000 64 0 131072 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_hex1 : scanN AsanUbsan_seg_bytes_001 64 0 442368 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_len0 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_000) / 2) = 131072%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_len1 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_001) / 2) = 442368%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_rom0 : forall x, 0x10000 <= x < 0x30000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at AsanUbsan_seg_bytes_000 (Z.to_N (x - 0x10000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 131072))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len0.
replace (Z.to_N (x - 65536) <? 131072)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at AsanUbsan_seg_bytes_000 (Z.to_N (x - 65536))); reflexivity.
Qed.
Lemma tfib_rom1 : forall x, 0x30000 <= x < 0x9c000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at AsanUbsan_seg_bytes_001 (Z.to_N (x - 0x30000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 131072))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((196608 <=? x) && (x + 1 <=? 196608 + 442368))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len1.
replace (Z.to_N (x - 196608) <? 442368)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at AsanUbsan_seg_bytes_001 (Z.to_N (x - 196608))); reflexivity.
Qed.
Lemma tfib_rom_all : forall x, 0x10000 <= x < 0x5fa000 -> seg_rom TSEGS (Z_to_bv 64 x) <> None.
Proof.
intros x Hx. destruct (Z.lt_ge_cases x 0x30000) as [H0|H0].
{ rewrite tfib_rom0 by lia. exact (scanN_sound _ 64 0 131072 tfib_hex0 (Z.to_N (x - 0x10000)) ltac:(lia)). }
destruct (Z.lt_ge_cases x 0x9c000) as [H1|H1].
{ rewrite tfib_rom1 by lia. exact (scanN_sound _ 64 0 442368 tfib_hex1 (Z.to_N (x - 0x30000)) ltac:(lia)). }
apply tfib_rw_rom. lia.
Qed.
