(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Asan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0ms X0na X0jx X0k2 X0k3 X0m4 X0lh X0ll X0kb X0kc X0ly.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require X0lb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS := Asan.M.loaded_segments.
Definition AITAB : itab := mk_itab ASEGS ASAN_A_TEXT_LO ASAN_A_TEXT_N.

Lemma asan_IT_ok : itab_sound ASEGS AITAB.
Proof. apply mk_itab_sound. Qed.

Lemma asan_wx : wx_segs_nowrap ASEGS.
Proof. exact Asan_wx_nowrap. Qed.

Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
cbn [find_segment].
replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
- exact (IH lo hi x Hl Hx).
- symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo ASAN_A) (img_hi ASAN_A) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
APS.in_hull ASAN_A (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
intros a H. apply (find_segment1_none_outside ASEGS (img_lo ASAN_A) (img_hi ASAN_A)); [exact asan_segs_in_hull|].
unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS ASAN_A.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo ASAN_A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi ASAN_A) (segments_reserved ASEGS).
Proof.
assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x34000); (Z_to_bv 64 0x44000, Z_to_bv 64 0xab000);
(Z_to_bv 64 0xef000, Z_to_bv 64 0x6000); (Z_to_bv 64 0xf5000, Z_to_bv 64 0x55d000)])
by (vm_compute; reflexivity).
rewrite E. cbn [img_lo img_hi ASAN_A].
repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_cover : X0lb.hull_cover ASEGS ASAN_A.
Proof.
assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x34000); (Z_to_bv 64 0x44000, Z_to_bv 64 0xab000);
(Z_to_bv 64 0xef000, Z_to_bv 64 0x6000); (Z_to_bv 64 0xf5000, Z_to_bv 64 0x55d000)])
by (vm_compute; reflexivity).
unfold X0lb.hull_cover. rewrite E. cbn [img_lo img_hi ASAN_A]. split; [lia|]. intros z Hz.
destruct (Z_lt_le_dec z 0x44000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x34000); split; [left; reflexivity|]|].
{ cbn [fst snd]. rewrite !u64_lit by lia. lia. }
destruct (Z_lt_le_dec z 0xef000); [exists (Z_to_bv 64 0x44000, Z_to_bv 64 0xab000); split; [right; left; reflexivity|]|].
{ cbn [fst snd]. rewrite !u64_lit by lia. lia. }
destruct (Z_lt_le_dec z 0xf5000); [exists (Z_to_bv 64 0xef000, Z_to_bv 64 0x6000); split; [right; right; left; reflexivity|]|].
{ cbn [fst snd]. rewrite !u64_lit by lia. lia. }
exists (Z_to_bv 64 0xf5000, Z_to_bv 64 0x55d000). split; [right; right; right; left; reflexivity|].
cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok ASAN_A.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi ASAN_A]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_shadow_ok : APS.shadow_ok ASAN_A.
Proof. unfold APS.shadow_ok. cbn [shadow_off ASAN_A]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x642000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_hex2 : scanN Asan_seg_bytes_002 64 0 24576 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3 : scanN Asan_seg_bytes_003 64 0 5623808 = true.
Proof.

apply (scanN_prefix_zwin Asan_seg_bytes_003 20480 5623808 (Uint63.of_Z 40960) (Uint63.of_Z 11206656)).
- vm_cast_no_check (eq_refl true).
- vm_cast_no_check (eq_refl true).
- reflexivity.
- reflexivity.
- vm_compute. discriminate.
- vm_compute. discriminate.
Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 24576%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5623808%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : ASEGS = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
0xef000 <= bv_unsigned x < 0x652000 -> wview ASEGS m x <> None.
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite asan_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
Asan_segment_000 Asan_segment_001
Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 24576); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5623808); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xf5000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
[rewrite asan_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
[rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0kj.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := Asan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS ASAN_A APH.
Proof.
constructor.
- repeat split; reflexivity.
- cbn [img_lo img_hi ASAN_A]. lia.
- vm_compute. reflexivity.
- exact asan_res_hull.
- rewrite asan_res_sizes. reflexivity.
- cbn [rw_lo rw_len ASAN_A]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
- exact asan_shadow_ok.
Qed.
