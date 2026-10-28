(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1f7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma land_m4 x : 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551612 = x - x mod 4.
Proof.
intros Hx. change 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. apply zb_shr_shl; lia.
Qed.

Lemma lts_lit_false a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.
Lemma lts_lit_true a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> a < b ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_lt. lia. Qed.

Section S.
Context {RCEIL : RunCeiling}.
Variables (IQ AK lo : Z) (m0 : mem).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LOW : lo + 4352 <= bv_unsigned sp.
Hypothesis GLO : NB_GLOBALS_TOP <= lo.
Hypothesis SP63 : bv_unsigned sp < 2 ^ 63.
Hypothesis AI : apart IQ 40 lo (bv_unsigned sp - lo).
Hypothesis AA : apart AK 40 lo (bv_unsigned sp - lo).
Hypothesis AAI : apart AK 40 IQ 40.
Hypothesis IQ0 : 0 < IQ.
Hypothesis IQ4 : IQ mod 4 = 0.
Hypothesis AK0 : 0 < AK.
Hypothesis AK4 : AK mod 4 = 0.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Local Notation usp := (bv_unsigned sp).
Local Notation W := [(lo, usp); (AK, AK + 40)].
Local Notation POST := (lsp_to_lpc_post AK lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
Local Notation FRAME := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation LOWJ j6 j4 := [C8 (Z_to_bv 64 0); CB 88 j6; C8 (Z_to_bv 64 0); CB 3944 j4].

Local Ltac inner_call j wp y2 y3 y4 y5 y6 y7 y8 y9 WP XF FRM MI :=
eapply evt_cut;
[ eapply (inner_loop (bv_unsigned sp) j _) with (k := 4%nat) (wdone := []) (wrest := wp) (xrest := [y2; y3; y4; y5; y6; y7; y8; y9])
(q := bv_unsigned sp + -176) (xq := bv_unsigned sp + -220) (o2 := 0) (o3 := 4) (o5 := 0);
[ lia | reflexivity | reflexivity | cbn [length Z.of_nat]; lia | cbn [length Z.of_nat]; lia
| cbn [length Z.of_nat]; lia | cbn [length Z.of_nat]; lia | cbn [length Z.of_nat]; lia | lia | lia
| exact FRM | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia
| exact WP
| replace (bv_unsigned sp + -220 + -4) with (bv_unsigned sp + -224) by lia; exact XF ]
| ].

Local Ltac inner_ret m :=
post_call rsegs m; rename MI0 into MI || idtac;
lazymatch goal with
| H : rw_cells _ _ (bv_unsigned sp + -176) (f32 ?ws), L : length ?ws = 22%nat |- _ =>
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|? ?]]]]]]]]]]]]]]]]]]]]]]];
try (cbn in L; lia);
rewrite !f32_cons, f32_nil in H; rename H into WP'
end.

Local Ltac n4_checks :=
zstep; zstep; zstep;
zstep; zstep; if_false_x; zstep; zstep; if_false_z; zstep; rewrite land_m4 by lia; zstep; if_false_x.

#[using="IQ LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16"] Lemma jloop : forall (k : nat) (j qa : Z) (adone arest wp xf : list word) (aw : word) (ja jb j6 j4 : list byte)
(xs2 xs3 xs4 xs5 xs6 xs7 xs8 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length arest = k -> j + Z.of_nat k = 10 -> 1 <= j -> length adone = Z.to_nat (j - 1) -> qa = AK + 4 * (j - 1) ->
length wp = 22%nat -> length xf = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4272) ->
rw_cells rsegs m (usp + -80) FRAME -> rw_cells rsegs m (usp + -88) [CB 8 ja] ->
rw_cells rsegs m (usp + -176) (f32 wp) -> rw_cells rsegs m (usp + -184) [CB 8 jb] ->
rw_cells rsegs m (usp + -224) (f32 xf) -> rw_cells rsegs m (usp + -4272) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 adone) -> rw_cells rsegs m qa (f32 (aw :: arest)) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -224)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (-4)) (Z_to_bv 64 5) sp (Z_to_bv 64 2147483647)
(Z_to_bv 64 j) (Z_to_bv 64 AK) (Z_to_bv 64 10) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -176)) (Z_to_bv 64 (usp + -224))
(Z_to_bv 64 (18446744073709551615 - (usp + -224))) (Z_to_bv 64 (18446744073709551615 - (usp + -176)))
xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 (-8)) (Z_to_bv 64 80) (Z_to_bv 64 8589934592) (Z_to_bv 64 1))
G (Z_to_bv 64 0x27d9c) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros j qa adone arest wp xf aw ja jb j6 j4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 G fc m
LR Hjk Hj LD Hqa Lwp Lxf FRM MI MU WM ST FR PADA WP PADB XF LJ ADONE ACUR;
pose proof (rw_cells_bound _ _ _ _ ACUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ ADONE) as BD; rewrite cells_size_f32, LD in BD;
destruct wp as [|v0 [|v1 [|v2 [|v3 wp]]]]; try (cbn in Lwp; lia);
destruct xf as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|y9 [|? ?]]]]]]]]]]]; try (cbn in Lxf; lia); cbn [length] in Lwp, Lxf;
rewrite !f32_cons in WP; rewrite !f32_cons, f32_nil in XF.
- destruct arest; [|cbn in LR; lia]. cbn [length] in Hjk. rewrite f32_cons, f32_nil in ACUR.
zstep. if_false_x. zstep. zstep. zstep. zstep.
inner_call j wp y2 y3 y4 y5 y6 y7 y8 y9 WP XF FRM MI.
inner_ret m.
n4_checks. zstep. if_false_x.
zstep. zstep. zstep. replace (Z.shiftl j 2 + AK + -4) with qa by (rewrite Z.shiftl_mul_pow2 by lia; lia).
zstep. if_false_x. zstep. zstep. zstep. if_false_z. zstep. if_false_x.
do 9 zstep. zstep. if_false_x. zstep.
zstep. rewrite swrap32_small by lia. zstep. zstep. zstep.
assert (PB : negb (bv_lts (Z_to_bv 64 10) (Z_to_bv 64 (j + 1))) = false) by (rewrite lts_lit_true by lia; reflexivity).
if_false_by PB. clear PB.
do 13 zstep.
chunk_snoc ADONE ACUR. rewrite f32_snoc in ADONE.
release_frame LJ ST (bv_unsigned sp + -224). release_frame XF ST (bv_unsigned sp + -184).
release_frame PADB ST (bv_unsigned sp + -176). release_frame WP' ST (bv_unsigned sp + -88).
release_frame PADA ST (bv_unsigned sp + -80). release_frame FR ST (bv_unsigned sp).
apply evt_done; unfold lsp_to_lpc_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
split; [exact ADONE|]. rewrite length_app, LD; cbn [length]; lia.
- destruct arest as [|aw' arest]; [cbn in LR; lia|]. cbn [length] in LR, Hjk, BC. rewrite !f32_cons in ACUR.
zstep. if_false_x. zstep. zstep. zstep. zstep.
inner_call j wp y2 y3 y4 y5 y6 y7 y8 y9 WP XF FRM MI.
inner_ret m.
n4_checks. zstep. if_false_x.
zstep. zstep. zstep. replace (Z.shiftl j 2 + AK + -4) with qa by (rewrite Z.shiftl_mul_pow2 by lia; lia).
zstep. if_false_x. zstep. zstep. zstep. if_false_z. zstep. if_false_x.
do 9 zstep. zstep. if_false_x. zstep.
zstep. rewrite swrap32_small by lia. zstep. zstep. zstep.
assert (PB : negb (bv_lts (Z_to_bv 64 10) (Z_to_bv 64 (j + 1))) = true) by (rewrite lts_lit_false by lia; reflexivity).
if_true_by PB. clear PB.
chunk_uncons ACUR as AC1. chunk_snoc ADONE AC1. rewrite f32_snoc in ADONE.
eapply (IH (j + 1) (qa + 4) (adone ++ [_]) arest [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9]);
[ lia | lia | lia | rewrite length_app, LD; cbn [length]; lia | lia | reflexivity | reflexivity
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA
| exact WP' | exact PADB | exact XF | exact LJ | exact ADONE | exact ACUR ].
Qed.

#[using="IQ LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16"] Lemma tailJ0 : forall (aks wp xf : list word) (ja jb j6 j4 : list byte)
(t0 t1 t2 xs1 xa0 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length aks = 10%nat -> length wp = 22%nat -> length xf = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4272) ->
rw_cells rsegs m (usp + -80) FRAME -> rw_cells rsegs m (usp + -88) [CB 8 ja] ->
rw_cells rsegs m (usp + -176) (f32 wp) -> rw_cells rsegs m (usp + -184) [CB 8 jb] ->
rw_cells rsegs m (usp + -224) (f32 xf) -> rw_cells rsegs m (usp + -4272) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 aks) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -224)) gp tp t0 t1 t2 sp xs1
xa0 (Z_to_bv 64 AK) (Z_to_bv 64 10) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -176)) (Z_to_bv 64 (usp + -224))
(Z_to_bv 64 (18446744073709551615 - (usp + -224))) xa7
xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x27d40) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
intros until m. intros LA Lwp Lxf FRM MI MU WM ST FR PADA WP PADB XF LJ A.
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
destruct wp as [|v0 [|v1 [|v2 [|v3 wp]]]]; try (cbn in Lwp; lia).
destruct xf as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|y9 [|? ?]]]]]]]]]]]; try (cbn in Lxf; lia). cbn [length] in Lwp, Lxf.
rewrite !f32_cons in WP. rewrite !f32_cons, f32_nil in XF.
do 23 zstep. rewrite zb_lxor_ones by lia. cond_prep.
zstep. if_false_x. zstep. zstep. zstep. zstep.
inner_call constr:(0) wp y2 y3 y4 y5 y6 y7 y8 y9 WP XF FRM MI.
inner_ret m.
n4_checks. zstep. if_true_x.
zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
destruct aks as [|a0w arest]; [cbn in LA; lia|]. cbn [length] in LA. rewrite f32_cons in A.
eapply (jloop 9%nat 1 AK [] arest [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9]);
[ lia | lia | lia | reflexivity | lia | reflexivity | reflexivity
| assumption | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA
| exact WP' | exact PADB | exact XF | exact LJ
| apply rw_cells_nil; lia | exact A ].
Qed.

#[using="IQ LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16"] Lemma xloop : forall (k : nat) (aks xdone xrest frest wp : list word) (qx qf o c : Z) (xw fw : word) (ja jb j6 j4 : list byte)
(xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length aks = 10%nat -> length xrest = k -> length frest = k -> (length xdone + k = 9)%nat -> length wp = 22%nat ->
qx = usp + -224 + 4 * Z.of_nat (length xdone) -> qf = IQ + 4 * Z.of_nat (length xdone) ->
o = 4 * Z.of_nat (length xdone) -> c = Z.of_nat k + 1 ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4272) ->
rw_cells rsegs m (usp + -80) FRAME -> rw_cells rsegs m (usp + -88) [CB 8 ja] ->
rw_cells rsegs m (usp + -176) (f32 wp) -> rw_cells rsegs m (usp + -184) [CB 8 jb] ->
rw_cells rsegs m (usp + -224) (f32 xdone) -> rw_cells rsegs m qx (f32 (xw :: xrest)) ->
rw_cells rsegs m (usp + -4272) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 aks) -> rw_cells rsegs m qf (f32 (fw :: frest)) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -224)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 c) (Z_to_bv 64 qx) sp xs1
(Z_to_bv 64 IQ) (Z_to_bv 64 AK) (Z_to_bv 64 10) (Z_to_bv 64 5) (Z_to_bv 64 (usp + -176)) (Z_to_bv 64 (usp + -224))
(Z_to_bv 64 (18446744073709551615 - (usp + -224))) (Z_to_bv 64 o)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 qf) (Z_to_bv 64 qf) t5 t6)
G (Z_to_bv 64 0x27cc8) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros aks xdone xrest frest wp qx qf o c xw fw ja jb j6 j4 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t5 t6 G fc m
LA LXR LFR LXD Lwp Hqx Hqf Ho Hc FRM MI MU WM ST FR PADA WP PADB XD XC LJ A FQ;
pose proof (rw_cells_bound _ _ _ _ FQ) as BF; rewrite cells_size_f32 in BF; cbn [length] in BF;
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
- destruct xrest; [|cbn in LXR; lia]. destruct frest; [|cbn in LFR; lia]. cbn [length] in LXD.
rewrite f32_cons, f32_nil in XC. rewrite f32_cons, f32_nil in FQ.
zstep. zstep. if_false_z. zstep. if_false_x. zstep. if_false_x. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. if_cases B.
+ do 7 zstep. zstep. if_false_x. zstep. zstep. zstep. zstep. zstep. rewrite swrap32_small by lia. zstep. zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD.
eapply (tailJ0 aks wp (xdone ++ [_]));
[ exact LA | exact Lwp | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact LJ | exact A ].
+ do 5 zstep. zstep. if_false_x. zstep. zstep. zstep. zstep. zstep. rewrite swrap32_small by lia. zstep. zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD.
eapply (tailJ0 aks wp (xdone ++ [_]));
[ exact LA | exact Lwp | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact LJ | exact A ].
- destruct xrest as [|xw' xrest]; [cbn in LXR; lia|]. destruct frest as [|fw' frest]; [cbn in LFR; lia|]. cbn [length] in LXR, LFR, LXD, BF.
rewrite !f32_cons in XC. rewrite !f32_cons in FQ.
zstep. zstep. if_false_z. zstep. if_false_x. zstep. if_false_x. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. if_cases B.
+ do 7 zstep. zstep. if_false_x. zstep. zstep. zstep. zstep. zstep. rewrite swrap32_small by lia. zstep. zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. chunk_uncons FQ as F1.
eapply (IH aks (xdone ++ [_]) xrest frest wp (qx + 4) (qf + 4) (o + 4) (c + -1));
[ exact LA | lia | lia | rewrite length_app; cbn [length]; lia | exact Lwp
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact XC | exact LJ | exact A | exact FQ ].
+ do 5 zstep. zstep. if_false_x. zstep. zstep. zstep. zstep. zstep. rewrite swrap32_small by lia. zstep. zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. chunk_uncons FQ as F1.
eapply (IH aks (xdone ++ [_]) xrest frest wp (qx + 4) (qf + 4) (o + 4) (c + -1));
[ exact LA | lia | lia | rewrite length_app; cbn [length]; lia | exact Lwp
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| rewrite length_app; cbn [length]; lia | lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact XC | exact LJ | exact A | exact FQ ].
Qed.
End S.
