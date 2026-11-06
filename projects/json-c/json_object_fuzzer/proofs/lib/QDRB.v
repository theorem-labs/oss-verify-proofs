(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWXq.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QLPb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QF1K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QF1K. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qs4A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qs4A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgQ.Mq0.
Local Instance asanimg_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition AITAB : itab := mk_itab JO6SEGS AJO6_TEXT_LO AJO6_TEXT_N.

Lemma asan_IT_ranges_ok : forall rs, itab_sound JO6SEGS (mk_itab_ranges JO6SEGS rs).
Proof. intros rs. apply APS.mk_itab_ranges_sound. Qed.

Lemma asan_wx : wx_segs_nowrap JO6SEGS.
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

Lemma asan_segs_in_hull : segs_in_hull_b JO6SEGS (img_lo AJO6) (img_hi AJO6) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_in_hull : forall a : word,
APS.in_hull AJO6 (bv_unsigned a) = false -> find_segment JO6SEGS (bv_unsigned a) 1 = None.
Proof.
intros a H. apply (find_segment1_none_outside JO6SEGS (img_lo AJO6) (img_hi AJO6)); [exact asan_segs_in_hull|].
unfold APS.in_hull in H. apply andb_false_iff in H as [H|H]; [apply Z.leb_gt in H; left | apply Z.ltb_ge in H; right]; lia.
Qed.

Lemma asan_res_len : APS.res_len_ok JO6SEGS AJO6.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segments_reserved :
segments_reserved JO6SEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2d000); (Z_to_bv 64 0x3d000, Z_to_bv 64 0xa5000);
(Z_to_bv 64 0xe2000, Z_to_bv 64 0x5000); (Z_to_bv 64 0xe7000, Z_to_bv 64 0x55e000)].
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo AJO6 <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AJO6) (segments_reserved JO6SEGS).
Proof.
rewrite asan_segments_reserved. cbn [img_lo img_hi AJO6].
repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok AJO6.
Proof. unfold APS.hull_ok. cbn [img_lo img_hi AJO6]. unfold KHI. repeat split; reflexivity || lia. Qed.

Lemma asan_hull_cov : APS.hull_cov JO6SEGS AJO6.
Proof.
unfold APS.hull_cov. split; [cbn [img_lo img_hi AJO6]; lia|].
intros z Hz. cbn [img_lo img_hi AJO6] in Hz. rewrite asan_segments_reserved.
unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia. rewrite orb_false_r.
repeat match goal with |- (?a || ?b)%bool = true => destruct a eqn:?; [reflexivity | cbn [orb]] end.
match goal with |- ?a = true => destruct a eqn:?; [reflexivity | exfalso] end.
repeat match goal with H : (_ && _)%bool = false |- _ =>
apply andb_false_iff in H; destruct H as [H|H]; [apply Z.leb_gt in H | apply Z.ltb_ge in H] end; lia.
Qed.

Lemma asan_shadow_ok : APS.shadow_ok AJO6.
Proof. unfold APS.shadow_ok. cbn [shadow_off AJO6]. lia. Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved JO6SEGS) = 0x635000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_res_top : reserved_top (segments_reserved JO6SEGS) = 0x645000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_hex2 : scanN Asan_seg_bytes_002 64 0 20480 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma scanN_join : forall s f base n h bh nh,
N.eqb n 0 = false -> N.eqb n 1 = false -> N.div2 n = h -> (base + h)%N = bh -> (n - h)%N = nh ->
scanN s f base h = true -> scanN s f bh nh = true -> scanN s (S f) base n = true.
Proof.
intros s f base n h bh nh H0 H1 Hh Hbh Hnh Ha Hb. cbn [scanN]. rewrite H0, H1. cbv zeta. rewrite Hh, Hbh, Hnh, Ha, Hb. reflexivity.
Qed.
Lemma asan_hex3 : scanN Asan_seg_bytes_003 64 0 5627904 = true.
Proof.
exact (scanN_join Asan_seg_bytes_003 63 0 5627904 2813952 2813952 2813952
eq_refl eq_refl eq_refl eq_refl eq_refl asan_hex3a asan_hex3b).
Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 20480%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5627904%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : JO6SEGS = [Asan_segment_000; Asan_segment_001;
Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
0xe2000 <= bv_unsigned x < 0x645000 -> wview JO6SEGS m x <> None.
Proof.
intros m x Hx. unfold wview. destruct (m x); [discriminate|].
destruct (find_segment JO6SEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
- apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
rewrite asan_segs_eq in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
Asan_segment_000 Asan_segment_001
Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
+ exfalso. lia.
+ exfalso. lia.
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 20480); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
+ cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 5627904); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
- exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xe7000) as [Hl|Hl].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
[rewrite asan_segs_eq; cbn; tauto | cbn; lia].
+ apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
[rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma asan_img_facts : img_facts JO6SEGS AJO6 JO6PH.
Proof.
constructor.
- repeat split; reflexivity.
- cbn [img_lo img_hi AJO6]. lia.
- exact asan_res_top.
- exact asan_res_hull.
- rewrite asan_res_sizes. reflexivity.
- cbn [rw_lo rw_len AJO6]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
- exact asan_shadow_ok.
Qed.
