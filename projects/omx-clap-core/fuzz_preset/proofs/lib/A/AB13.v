(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for omx-clap-core/fuzz_preset's ASan image (ELF sha256 bff8519bbe3ea0e4) by the internal file gen_geom.py from proofs/cgif/cgif_file_fuzzer/lib/A/AB13.v: every image number is computed from that ELF (program headers, symbols, asan_globals), module paths changed. *)
(* Generator: tools/startup/gen_geom.py sha256 62d913384d64f806abd4c64988fe0dd3acec6cc5f7b3a7be6c55ff04693a6d93; image sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590; donor A/AB13.v blob c68dc7fa455268e983603b84baa495b6312bec29. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK1b YK07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
Local Notation TSEGS := tfibsegs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma tfib_segs_eq : TSEGS = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.
Lemma tfib_hex2 : scanN Asan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_hex3 : scanN Asan_seg_bytes_003 64 0 5623808 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5623808%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_rw_window : forall m (x : word),
0xa1000 <= bv_unsigned x < 0x600000 -> wview TSEGS m x <> None.
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment TSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite tfib_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
Asan_segment_000 Asan_segment_001
Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 8192); [exact tfib_hex2 | rewrite tfib_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5623808); [exact tfib_hex3 | rewrite tfib_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xa3000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
[rewrite tfib_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
[rewrite tfib_segs_eq; cbn; tauto | cbn; lia].
Qed.
Definition TFIB_BSS : Z * Z := (0xa77e0, 0x600000).
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
Lemma tfib_zero3 : zscanN Asan_seg_bytes_003 64 18400 5605408 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_rom3 : forall x, 0xa3000 <= x < 0x600000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at Asan_seg_bytes_003 (Z.to_N (x - 0xa3000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 135168))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((200704 <=? x) && (x + 1 <=? 200704 + 458752))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((659456 <=? x) && (x + 1 <=? 659456 + 8192))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((667648 <=? x) && (x + 1 <=? 667648 + 5623808))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len3.
replace (Z.to_N (x - 667648) <? 5623808)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at Asan_seg_bytes_003 (Z.to_N (x - 667648))); reflexivity.
Qed.
Lemma tfib_bss_rom : forall x, fst TFIB_BSS <= x < snd TFIB_BSS -> seg_rom TSEGS (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
Proof.
intros x Hx. cbn [fst snd TFIB_BSS] in Hx. rewrite tfib_rom3 by lia.
replace (Z.to_N (x - 0xa3000)) with (18400 + Z.to_N (x - 0xa77e0))%N by lia.
apply (zscanN_sound _ _ _ _ tfib_zero3). lia.
Qed.
Lemma tfib_rom2 : forall x, 0xa1000 <= x < 0xa3000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at Asan_seg_bytes_002 (Z.to_N (x - 0xa1000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 135168))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((200704 <=? x) && (x + 1 <=? 200704 + 458752))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((659456 <=? x) && (x + 1 <=? 659456 + 8192))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len2.
replace (Z.to_N (x - 659456) <? 8192)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at Asan_seg_bytes_002 (Z.to_N (x - 659456))); reflexivity.
Qed.
Lemma tfib_rw_rom : forall x, 0xa1000 <= x < 0x600000 -> seg_rom TSEGS (Z_to_bv 64 x) <> None.
Proof.
intros x Hx. destruct (Z.lt_ge_cases x 0xa3000) as [Hl|Hl].
- rewrite tfib_rom2 by lia. exact (scanN_sound _ 64 0 8192 tfib_hex2 (Z.to_N (x - 0xa1000)) ltac:(lia)).
- rewrite tfib_rom3 by lia. exact (scanN_sound _ 64 0 5623808 tfib_hex3 (Z.to_N (x - 0xa3000)) ltac:(lia)).
Qed.
Lemma tfib_hex0 : scanN Asan_seg_bytes_000 64 0 135168 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_hex1 : scanN Asan_seg_bytes_001 64 0 458752 = true.
Proof. native_compute. reflexivity. Qed.
Lemma tfib_len0 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_000) / 2) = 135168%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_len1 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_001) / 2) = 458752%N.
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_rom0 : forall x, 0x10000 <= x < 0x31000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at Asan_seg_bytes_000 (Z.to_N (x - 0x10000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 135168))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len0.
replace (Z.to_N (x - 65536) <? 135168)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at Asan_seg_bytes_000 (Z.to_N (x - 65536))); reflexivity.
Qed.
Lemma tfib_rom1 : forall x, 0x31000 <= x < 0xa1000 ->
seg_rom TSEGS (Z_to_bv 64 x) = hex_byte_at Asan_seg_bytes_001 (Z.to_N (x - 0x31000)).
Proof.
intros x Hx. unfold seg_rom, memory_read. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 x) with x by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia; reflexivity).
rewrite tfib_segs_eq. cbn -[segment_byte_at Z.add].
replace ((65536 <=? x) && (x + 1 <=? 65536 + 135168))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
replace ((200704 <=? x) && (x + 1 <=? 200704 + 458752))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
cbn -[segment_byte_at Z.add Z.sub]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at]. rewrite tfib_len1.
replace (Z.to_N (x - 200704) <? 458752)%N with true by (symmetry; apply N.ltb_lt; lia).
destruct (hex_byte_at Asan_seg_bytes_001 (Z.to_N (x - 200704))); reflexivity.
Qed.
Lemma tfib_rom_all : forall x, 0x10000 <= x < 0x600000 -> seg_rom TSEGS (Z_to_bv 64 x) <> None.
Proof.
intros x Hx. destruct (Z.lt_ge_cases x 0x31000) as [H0|H0].
{ rewrite tfib_rom0 by lia. exact (scanN_sound _ 64 0 135168 tfib_hex0 (Z.to_N (x - 0x10000)) ltac:(lia)). }
destruct (Z.lt_ge_cases x 0xa1000) as [H1|H1].
{ rewrite tfib_rom1 by lia. exact (scanN_sound _ 64 0 458752 tfib_hex1 (Z.to_N (x - 0x31000)) ltac:(lia)). }
apply tfib_rw_rom. lia.
Qed.
