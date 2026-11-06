(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[global] Notation JO6SEGS := QLPb.JO6SEGS (only parsing).

Definition L_main_jo6 (atop : Z) : lvp :=
mkLVP [(0x10000, 0x645000); (atop, 0x800000000000)]
[(0x7fff7000, 0x7fff7000 + 0x10000000); (0x8fff7000, 0x8fff7000 + 0x20000000000); (0x2008fff7000, 0x2008fff7000 + 0xdfff0001000)]
[(0x7fff8000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)]
0x7fff8000.

Lemma L_main_jo6_shoff_ok : forall atop, shoff_ok (L_main_jo6 atop).
Proof. intros atop. unfold shoff_ok, L_main_jo6. cbn [lv_shoff]. lia. Qed.

Lemma L_main_jo6_bands_excl : forall atop, bands_excl (L_main_jo6 atop).
Proof.
intros atop b Hb. cbn in Hb. destruct Hb as [<-|[<-|[]]].
- exists (0x7fff7000, 0x7fff7000 + 0x10000000). cbn. split; [auto| lia].
- exists (0x2008fff7000, 0x2008fff7000 + 0xdfff0001000). cbn. split; [auto| lia].
Qed.

Lemma L_main_jo6_bands_cover : forall atop, bands_cover (L_main_jo6 atop).
Proof.
intros atop y Hy He. unfold L_main_jo6, Qsn5.in_zivs, Qsn5.zin, Qsn5.shz in *. cbn [lv_excl lv_bands lv_shoff existsb fst snd] in *.
unfold lv_ceiling, sp_window_hi, stack_max_size in Hy.
apply orb_false_iff in He as [He1 He]. apply orb_false_iff in He as [He2 He]. apply orb_false_iff in He as [He3 _].
apply andb_false_iff in He1. apply andb_false_iff in He2. apply andb_false_iff in He3.
rewrite orb_false_r. apply orb_true_iff.
destruct (Z.lt_ge_cases y 0x7fff7000) as [Hlo|Hhi].
- left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt].
+ pose proof (Z.div_pos y 8). lia.
+ assert (y / 8 < 0xfffee00) by (apply Z.div_lt_upper_bound; lia). lia.
- right. assert (Hge : 0x10007fff8000 <= y).
{ destruct He1 as [H|H]; [apply Z.leb_gt in H; lia| apply Z.ltb_ge in H].
destruct He2 as [H2|H2]; [apply Z.leb_gt in H2; lia| apply Z.ltb_ge in H2].
destruct He3 as [H3|H3]; [apply Z.leb_gt in H3; lia| apply Z.ltb_ge in H3]. lia. }
apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt].
+ assert (0x2000ffff000 <= y / 8) by (apply Z.div_le_lower_bound; lia). lia.
+ assert (y / 8 < 0xffffff00000) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma L_main_jo6_segs_in_base : forall atop, segs_in_base (L_main_jo6 atop) JO6SEGS.
Proof.
intros atop seg Hseg. exists (0x10000, 0x645000). split; [cbn; left; reflexivity|].
unfold JO6SEGS in Hseg. cbn [fst snd].
cbn in Hseg. repeat (destruct Hseg as [<-|Hseg]; [vm_compute; split; congruence|]). destruct Hseg.
Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma JO6SEGS_wx_nowrap : QQIi.wx_segs_nowrap JO6SEGS.
Proof. apply QQIi.wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma find_segment_none_above : forall segs a n top,
(forall seg, In seg segs -> Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= top) -> top < a + n -> find_segment segs a n = None.
Proof.
induction segs as [|s rest IH]; intros a n top H Ha; [reflexivity|]. cbn [find_segment].
pose proof (H s (or_introl eq_refl)) as Hs.
destruct (Z.leb (Z.of_N (seg_base s)) a && Z.leb (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
- apply andb_true_iff in E as [_ E]. apply Z.leb_le in E. lia.
- apply (IH a n top); [intros seg Hin; apply H; right; exact Hin | exact Ha].
Qed.

Lemma JO6SEGS_top : forall seg, In seg JO6SEGS -> Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 0x645000.
Proof.
intros seg Hseg. unfold JO6SEGS in Hseg. cbn in Hseg.
repeat (destruct Hseg as [<-|Hseg]; [vm_compute; congruence|]). destruct Hseg.
Qed.

Lemma JO6SEGS_low : forall y : word,
QzgH.kLowEnd < bv_unsigned y -> find_segment JO6SEGS (bv_unsigned y) 1 = None.
Proof.
intros y Hy. unfold QzgH.kLowEnd in Hy.
apply (find_segment_none_above JO6SEGS (bv_unsigned y) 1 0x645000); [exact JO6SEGS_top | lia].
Qed.
