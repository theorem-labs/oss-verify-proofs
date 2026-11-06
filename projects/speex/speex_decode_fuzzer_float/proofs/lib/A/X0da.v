(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0j3 X0hi
X0hn X0j0 X0hh X0hb X0fy X0fg X00b X04b X0jc.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X19m X183 X188 X19k X182 X17w X16j X161 X0ra X0v9 X19t.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19t.
Import ListNotations.
Open Scope Z_scope.

Lemma stk_wmono : forall (m m' : mem) lo hi, stk bsegs m lo hi -> wmono bsegs m m' -> stk bsegs m' lo hi.
Proof.
intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

Lemma rw_cells_stk : forall (m : mem) a cs hi, a + Z.of_nat (cells_size cs) = hi -> rw_cells bsegs m a cs -> stk bsegs m a hi.
Proof.
intros m a cs hi E [_ (H0 & H1 & H)]. split; [lia|]. split; [lia|]. intros x Hx. pose proof (H (x - a) ltac:(lia)) as W.
replace (a + (x - a)) with x in W by lia. split; [exact W | exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_wmono : forall (m m' : mem) a n, wr_at bsegs m a n -> wmono bsegs m m' -> wr_at bsegs m' a n.
Proof. intros m m' a n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (W _ (H i Hi)). Qed.

Lemma u32arr_agree : forall (m m' : mem) a ws, u32arr bsegs m a ws ->
agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> wmono bsegs m m' -> u32arr bsegs m' a ws.
Proof.
intros m m' a ws [Hb Hw] HA W. split.
- apply (bytes_at_agree bsegs m m' a _ Hb). rewrite u32s_length. intros x Hx. apply HA. lia.
- exact (wr_at_wmono m m' _ _ Hw W).
Qed.

Definition in_rngs (l : list (Z * Z)) (x : Z) : Prop := Exists (fun p => fst p <= x < snd p) l.

Definition consts_rngs (L : layoutA) : list (Z * Z) :=
[ (i_spacebeg, i_spacebeg + 24); (i_premapped, i_premapped + 1);
(0xfc0f8, 0xfc100); (0xfc108, 0xfc110); (0x195560, 0x195568); (0x197678, 0x197680); (0x1976ec, 0x1976ed);
(g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
(g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
(0xfc118, 0xfc138); (0x105ab8, 0x105ac0); (0x1067a0, 0x1067b8);
(g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
(g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
(l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
(g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
(g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
(l_T L + 0xc60, l_T L + 0xc60 + 1); (0x1976dd, 0x1976de); (0x1976e4, 0x1976e5); (0xfc110, 0xfc118); (0xfc140, 0xfc148);
(0xfe038, 0xfe040); (0x1032d5, 0x1032d6); (0x1067bc, 0x1067c0); (0x19760a, 0x19760b); (0xfce58, 0xfce60); (0xfce58, 0xfce60);
(0xfcc80, 0xfcc88); (0x106799, 0x10679a); (0xfe040, 0xfe048); (0xfdef8, 0xfdf00); (0xfdfe8, 0xfdff0); (0xfded0, 0xfded8); (0x1976e3, 0x1976e4);
(0x103278, 0x103280); (0x103280, 0x103284); (0x187d22, 0x187d23); (0x1032b8 + 44, 0x1032b8 + 48); (0x1032b8 + 52, 0x1032b8 + 56); (0x1032b8 + 85, 0x1032b8 + 86);
(0x638c98 + 16, 0x638c98 + 20); (0xfcd70, 0xfcd78); (0x197580, 0x197588); (0x10531c, 0x10531d); (l_TCX L + 8, l_TCX L + 8 + 4);
(l_T L, l_T L + 8); (0x197588, 0x197590); (0x102770, 0x102788); (0x1032e8, 0x1032ec);

(0xfc158, 0xfc160); (0x1976c3, 0x1976c4); (0x1976dc, 0x1976dd); (0x658f58, 0x658f60);

(0xfdf08, 0xfdf18); (0x103370, 0x103378);
(0xf7f78, 0xf7f88); (0xfc010, 0xfc018); (0xfc0e8, 0xfc0f8); (0xfcd78, 0xfcd88); (0xfce00, 0xfce10); (0xfce88, 0xfce98);
(0xfdec8, 0xfded0); (0xfdf28, 0xfdf40); (0x1032d0, 0x1032d4); (0x19763c, 0x19763d); (0x197960, 0x197961);

(0xfdee8, 0xfdef8); (0x1976e6, 0x1976e8);

(0xf8380, 0xf8450); (0xf8480, 0xf84e0); (0xf8500, 0xf8558); (0xf8580, 0xf85d8); (0xf8600, 0xf8658); (0xf8680, 0xf86d8);
(0xf8700, 0xf8758); (0xf8780, 0xf87d8); (0xf8800, 0xf8858); (0xf8880, 0xf88d8); (0xf8900, 0xf8910); (0xf8920, 0xf8938);
(0xf8960, 0xf8970); (0xf8980, 0xf8998); (0xf89c0, 0xf89d0); (0xf89e0, 0xf89f8); (0xf8a20, 0xf8a30); (0xf8a40, 0xf8a58);
(0xf8a80, 0xf8a98); (0xf8ac0, 0xf8ad8); (0xf8b00, 0xf8b60); (0xf8b80, 0xf8be0); (0xf8c00, 0xf8c18); (0xf8c40, 0xf8c98);
(0xf8cc0, 0xf8d18); (0xf8d40, 0xf8d98); (0xf8dc0, 0xf8e18); (0xf8e40, 0xf8f18); (0xf8f40, 0xf8f58); (0xf8f80, 0xf8f98);
(0xf8fc0, 0xf9098); (0xfcd90, 0xfcd98); (0xfcd98, 0xfcda0); (0xfcda0, 0xfcda8); (0xfcda8, 0xfcdb0); (0xfcdb0, 0xfcdb8);
(0xfcdb8, 0xfcdc0); (0xfcdc0, 0xfcdc8); (0xfcdc8, 0xfcdd0); (0xfcdd0, 0xfcdd8); (0xfcdd8, 0xfcde0); (0xfcde0, 0xfcde8);
(0xfcde8, 0xfcdf0); (0xfcdf0, 0xfcdf8); (0xfcdf8, 0xfce00) ].

Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Ltac in_rng_search := unfold in_rngs;
solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.

Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Ltac rwc_frameX X := eapply (rw_cells_agree bsegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Ltac roc_frameX X := eapply (ro_cells_agree bsegs _ _ _ _ X); eapply agree_sub; [eassumption|];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Lemma consts_rep_frame : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' -> wmono bsegs m m' ->
consts_rep L m'.
Proof.
intros L m m' H HA W.
destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
& (K1 & K2) & (C1 & C2 & C3 & C4) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
& X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43)).
assert (M' : m2s_cells m') by (split; [rwc_frame | split; [rwc_frame | rwc_frame]]).
split; [split; [rwc_frame | rwc_frame]|].
split; [split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | rwc_frame]]]]|].
split; [split; [split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | rwc_frame]]] | rwc_frame]|].
split; [exact M'|].
split; [split; [rwc_frame | split; [exact M' | split; [split; [rwc_frame | rwc_frame] | split; [rwc_frame | rwc_frame]]]]|].
split; [split; [rwc_frame | rwc_frame]|].
split; [split; [roc_frame | split; [roc_frame | split; [roc_frame | roc_frame]]]|].
split; [rwc_frameX X1|]. split; [roc_frameX X2|]. split; [roc_frameX X3|]. split; [roc_frameX X4|]. split; [roc_frameX X5|]. split; [roc_frameX X6|].
split; [roc_frameX X7|]. split; [rwc_frameX X8|]. split; [roc_frameX X9|]. split; [roc_frameX X10|]. split; [roc_frameX X11|]. split; [roc_frameX X12|].
split; [roc_frameX X13|]. split; [roc_frameX X14|]. split; [roc_frameX X15|]. split; [roc_frameX X16|]. split; [roc_frameX X17|]. split; [roc_frameX X18|].
split; [rwc_frameX X19|]. split; [rwc_frameX X20|]. split; [rwc_frameX X21|]. split; [rwc_frameX X22|]. split; [rwc_frameX X23|]. split; [rwc_frameX X24|].
split; [rwc_frameX X25|]. split; [rwc_frameX X26|]. split; [rwc_frameX X27|]. split; [rwc_frameX X28|]. split; [rwc_frameX X29|]. split; [rwc_frameX X30|].
split; [rwc_frameX X31|].
split; [exact (stk_wmono m m' _ _ X32 W)|].
split; [rwc_frameX X33|]. split; [rwc_frameX X34|]. split; [rwc_frameX X35|]. split; [rwc_frameX X36|].
split; [rwc_frameX X37|]. split; [rwc_frameX X38|]. split; [rwc_frameX X39|]. split; [rwc_frameX X40|]. split; [rwc_frameX X41|].
unfold io_rw, io_ro in *. split.
- repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwc_frameX Y|] end.
apply Forall_nil.
- repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; roc_frameX Y|] end.
apply Forall_nil.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma stk_wmono : forall (m m' : mem) lo hi, stk asegs m lo hi -> wmono asegs m m' -> stk asegs m' lo hi.
Proof.
intros m m' lo hi (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros a Ha.
destruct (H a Ha) as [Hw _]. pose proof (W _ Hw) as Hw'. split; [exact Hw'| exact (wview_mrd_A m' _ Hw')].
Qed.

Lemma rw_cells_stk : forall (m : mem) a cs hi, a + Z.of_nat (cells_size cs) = hi -> rw_cells asegs m a cs -> stk asegs m a hi.
Proof.
intros m a cs hi E [_ (H0 & H1 & H)]. split; [lia|]. split; [lia|]. intros x Hx. pose proof (H (x - a) ltac:(lia)) as W.
replace (a + (x - a)) with x in W by lia. split; [exact W | exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_wmono : forall (m m' : mem) a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (H0 & H1 & H) W. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (W _ (H i Hi)). Qed.

Lemma u32arr_agree : forall (m m' : mem) a ws, u32arr asegs m a ws ->
agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> wmono asegs m m' -> u32arr asegs m' a ws.
Proof.
intros m m' a ws [Hb Hw] HA W. split.
- apply (bytes_at_agree asegs m m' a _ Hb). rewrite u32s_length. intros x Hx. apply HA. lia.
- exact (wr_at_wmono m m' _ _ Hw W).
Qed.

Definition in_rngs (l : list (Z * Z)) (x : Z) : Prop := Exists (fun p => fst p <= x < snd p) l.

Definition consts_rngs (L : layoutA) : list (Z * Z) :=
[ (i_spacebeg, i_spacebeg + 24); (i_premapped, i_premapped + 1);
(0xf3878, 0xf3880); (0xf3888, 0xf3890); (0x18cd20, 0x18cd28); (0x18ee38, 0x18ee40); (0x18eeac, 0x18eead);
(g_tsd_key_inited, g_tsd_key_inited + 1); (g_tsd_key, g_tsd_key + 4); (pth_tsd, pth_tsd + 8);
(g_pthread_tsd_main, g_pthread_tsd_main + 8); (l_TCX L + 0x98, l_TCX L + 0x98 + 8);
(0xf3898, 0xf38b8); (0xfd278, 0xfd280); (0xfdf60, 0xfdf78);
(g_got_real_memset, g_got_real_memset + 8); (g_real_memset, g_real_memset + 8);
(g_can_poison, g_can_poison + 1); (g_cf_clear_shadow_mmap_threshold, g_cf_clear_shadow_mmap_threshold + 8);
(l_T L + off_t_stack_top, l_T L + off_t_stack_top + 16); (l_T L + off_t_stack_switching, l_T L + off_t_stack_switching + 1);
(g_GOT_shadow_offset_cell, g_GOT_shadow_offset_cell + 8); (g_shadow_memory_dynamic_address, g_shadow_memory_dynamic_address + 8);
(g_GOT_detect_uar, g_GOT_detect_uar + 8); (g_detect_stack_use_after_return, g_detect_stack_use_after_return + 4);
(l_T L + 0xc60, l_T L + 0xc60 + 1); (0x18ee9d, 0x18ee9e); (0x18eea4, 0x18eea5); (0xf3890, 0xf3898); (0xf38c0, 0xf38c8);
(0xf57b8, 0xf57c0); (0xfaa95, 0xfaa96); (0xfdf7c, 0xfdf80); (0x18edca, 0x18edcb); (0xf45d8, 0xf45e0); (0xf45d8, 0xf45e0);
(0xf4400, 0xf4408); (0xfdf59, 0xfdf5a); (0xf57c0, 0xf57c8); (0xf5678, 0xf5680); (0xf5768, 0xf5770); (0xf5650, 0xf5658); (0x18eea3, 0x18eea4);
(0xfaa38, 0xfaa40); (0xfaa40, 0xfaa44); (0x17f4e2, 0x17f4e3); (0xfaa78 + 44, 0xfaa78 + 48); (0xfaa78 + 52, 0xfaa78 + 56); (0xfaa78 + 85, 0xfaa78 + 86);
(0x630458 + 16, 0x630458 + 20); (0xf44f0, 0xf44f8); (0x18ed40, 0x18ed48); (0xfcadc, 0xfcadd); (l_TCX L + 8, l_TCX L + 8 + 4);
(l_T L, l_T L + 8); (0x18ed48, 0x18ed50); (0xf9f30, 0xf9f48); (0xfaaa8, 0xfaaac);

(0xf38d8, 0xf38e0); (0x18ee83, 0x18ee84); (0x18ee9c, 0x18ee9d); (0x650718, 0x650720);

(0xf5688, 0xf5698); (0xfab30, 0xfab38);
(0xef708, 0xef718); (0xf3790, 0xf3798); (0xf3868, 0xf3878); (0xf44f8, 0xf4508); (0xf4580, 0xf4590); (0xf4608, 0xf4618);
(0xf5648, 0xf5650); (0xf56a8, 0xf56c0); (0xfaa90, 0xfaa94); (0x18edfc, 0x18edfd); (0x18f120, 0x18f121);

(0xf5668, 0xf5678); (0x18eea6, 0x18eea8);

(0xefb00, 0xefbd0); (0xefc00, 0xefc60); (0xefc80, 0xefcd8); (0xefd00, 0xefd58); (0xefd80, 0xefdd8); (0xefe00, 0xefe58);
(0xefe80, 0xefed8); (0xeff00, 0xeff58); (0xeff80, 0xeffd8); (0xf0000, 0xf0058); (0xf0080, 0xf0090); (0xf00a0, 0xf00b8);
(0xf00e0, 0xf00f0); (0xf0100, 0xf0118); (0xf0140, 0xf0150); (0xf0160, 0xf0178); (0xf01a0, 0xf01b0); (0xf01c0, 0xf01d8);
(0xf0200, 0xf0218); (0xf0240, 0xf0258); (0xf0280, 0xf02e0); (0xf0300, 0xf0360); (0xf0380, 0xf0398); (0xf03c0, 0xf0418);
(0xf0440, 0xf0498); (0xf04c0, 0xf0518); (0xf0540, 0xf0598); (0xf05c0, 0xf0698); (0xf06c0, 0xf06d8); (0xf0700, 0xf0718);
(0xf0740, 0xf0818); (0xf4510, 0xf4518); (0xf4518, 0xf4520); (0xf4520, 0xf4528); (0xf4528, 0xf4530); (0xf4530, 0xf4538);
(0xf4538, 0xf4540); (0xf4540, 0xf4548); (0xf4548, 0xf4550); (0xf4550, 0xf4558); (0xf4558, 0xf4560); (0xf4560, 0xf4568);
(0xf4568, 0xf4570); (0xf4570, 0xf4578); (0xf4578, 0xf4580) ].

Ltac unfold_consts := unfold i_spacebeg, i_premapped, INST, g_instance, g_got_common_flags, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main,
g_got_real_memset, g_real_memset, g_can_poison, g_cf_clear_shadow_mmap_threshold, off_t_stack_top, off_t_stack_switching,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Ltac in_rng_search := unfold in_rngs;
solve [ repeat (first [ apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl ]) ].

Lemma in_rngs_same : forall l lo hi x, In (lo, hi) l -> lo <= x < hi -> in_rngs l x.
Proof. intros l lo hi x H Hx. unfold in_rngs. apply Exists_exists. exists (lo, hi). split; [exact H | exact Hx]. Qed.

Ltac rng_fast Hx := match type of Hx with ?A <= _ < ?B => apply (in_rngs_same _ A B); [solve [repeat (first [left; reflexivity | right])] | exact Hx] end.

Ltac rwc_frame := eapply rw_cells_agree; [eassumption | eapply agree_sub; [eassumption|] | eassumption];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Ltac roc_frame := eapply ro_cells_agree; [eassumption | eapply agree_sub; [eassumption|]];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Ltac rwc_frameX X := eapply (rw_cells_agree asegs _ _ _ _ X); [eapply agree_sub; [eassumption|] | eassumption];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].
Ltac roc_frameX X := eapply (ro_cells_agree asegs _ _ _ _ X); eapply agree_sub; [eassumption|];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold consts_rngs; unfold_consts; first [rng_fast Hx | in_rng_search].

Lemma consts_rep_frame : forall L (m m' : mem), consts_rep L m -> agree_on (in_rngs (consts_rngs L)) m m' -> wmono asegs m m' ->
consts_rep L m'.
Proof.
intros L m m' H HA W.
destruct H as ((I1 & I2) & (G1 & G2 & G3 & G4 & G5) & ((T1 & T2 & T3 & T4) & T5) & (M1 & M2 & M3) & (P1 & PM & (S1 & S2) & P3 & P4)
& (K1 & K2) & (C1 & C2 & C3 & C4) & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24
& X25 & X26 & X27 & X28 & X29 & X30 & X31 & X32 & X33 & X34 & X35 & X36 & X37 & X38 & X39 & X40 & X41 & X42 & X43)).
assert (M' : m2s_cells m') by (split; [rwc_frame | split; [rwc_frame | rwc_frame]]).
split; [split; [rwc_frame | rwc_frame]|].
split; [split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | rwc_frame]]]]|].
split; [split; [split; [rwc_frame | split; [rwc_frame | split; [rwc_frame | rwc_frame]]] | rwc_frame]|].
split; [exact M'|].
split; [split; [rwc_frame | split; [exact M' | split; [split; [rwc_frame | rwc_frame] | split; [rwc_frame | rwc_frame]]]]|].
split; [split; [rwc_frame | rwc_frame]|].
split; [split; [roc_frame | split; [roc_frame | split; [roc_frame | roc_frame]]]|].
split; [rwc_frameX X1|]. split; [roc_frameX X2|]. split; [roc_frameX X3|]. split; [roc_frameX X4|]. split; [roc_frameX X5|]. split; [roc_frameX X6|].
split; [roc_frameX X7|]. split; [rwc_frameX X8|]. split; [roc_frameX X9|]. split; [roc_frameX X10|]. split; [roc_frameX X11|]. split; [roc_frameX X12|].
split; [roc_frameX X13|]. split; [roc_frameX X14|]. split; [roc_frameX X15|]. split; [roc_frameX X16|]. split; [roc_frameX X17|]. split; [roc_frameX X18|].
split; [rwc_frameX X19|]. split; [rwc_frameX X20|]. split; [rwc_frameX X21|]. split; [rwc_frameX X22|]. split; [rwc_frameX X23|]. split; [rwc_frameX X24|].
split; [rwc_frameX X25|]. split; [rwc_frameX X26|]. split; [rwc_frameX X27|]. split; [rwc_frameX X28|]. split; [rwc_frameX X29|]. split; [rwc_frameX X30|].
split; [rwc_frameX X31|].
split; [exact (stk_wmono m m' _ _ X32 W)|].
split; [rwc_frameX X33|]. split; [rwc_frameX X34|]. split; [rwc_frameX X35|]. split; [rwc_frameX X36|].
split; [rwc_frameX X37|]. split; [rwc_frameX X38|]. split; [rwc_frameX X39|]. split; [rwc_frameX X40|]. split; [rwc_frameX X41|].
unfold io_rw, io_ro in *. split.
- repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; rwc_frameX Y|] end.
apply Forall_nil.
- repeat match goal with X : Forall _ (_ :: _) |- Forall _ (_ :: _) =>
let Y := fresh "Y" in apply Forall_cons_iff in X as [Y X]; apply Forall_cons; [cbn [fst snd] in Y |- *; roc_frameX Y|] end.
apply Forall_nil.
Qed.
