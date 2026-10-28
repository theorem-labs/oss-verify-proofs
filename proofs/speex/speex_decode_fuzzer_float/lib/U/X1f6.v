(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1f5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition lsp_to_lpc8_post (AK lo : Z)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (aks' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (AK, AK + 32)] m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' AK (f32 aks') /\ length aks' = 8%nat.
Definition lsp_to_lpc8_stmt_copy : Prop :=
forall (IQ AK lo : Z) (qs aks : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m IQ (f32 qs) -> length qs = 8%nat ->
rw_cells rsegs m AK (f32 aks) -> length aks = 8%nat ->
stk rsegs m lo (bv_unsigned sp) -> lo + LSP2LPC_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
apart IQ 32 lo (bv_unsigned sp - lo) -> apart AK 32 lo (bv_unsigned sp - lo) -> apart AK 32 IQ 32 ->
a0 = Z_to_bv 64 IQ -> a1 = Z_to_bv 64 AK -> a2 = Z_to_bv 64 8 -> a3 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
0 < IQ -> IQ mod 4 = 0 -> 0 < AK -> AK mod 4 = 0 -> bv_unsigned sp mod 16 = 0 ->
evt rsegs (lsp_to_lpc8_post AK lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_lsp_to_lpc) fc None m (seg_rom rsegs)).

Lemma land_m4_al : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof.
intros x Hx H. change 18446744073709551612 with (Z.ldiff (Z.ones 64) (Z.ones 2)).
rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
change (2^2) with 4. Z.div_mod_to_equations. lia.
Qed.
Lemma lts_lt_true8 a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> a < b ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_lt. lia. Qed.
Lemma lts_ge_false8' a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.

Section S.
Context {RCEIL : RunCeiling}.
Variables (IQ AK lo : Z) (m0 : mem).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LOW : lo + 4352 <= bv_unsigned sp.
Hypothesis GLO : NB_GLOBALS_TOP <= lo.
Hypothesis SP63 : bv_unsigned sp < 2 ^ 63.
Hypothesis AI : apart IQ 32 lo (bv_unsigned sp - lo).
Hypothesis AA : apart AK 32 lo (bv_unsigned sp - lo).
Hypothesis AAI : apart AK 32 IQ 32.
Hypothesis IQ0 : 0 < IQ.
Hypothesis IQ4 : IQ mod 4 = 0.
Hypothesis AK0 : 0 < AK.
Hypothesis AK4 : AK mod 4 = 0.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Local Notation usp := (bv_unsigned sp).
Local Notation W := [(lo, usp); (AK, AK + 32)].
Local Notation POST := (lsp_to_lpc8_post AK lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
Local Notation FRAME := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation LOWJ j6 j4 := [C8 (Z_to_bv 64 0); CB 72 j6; C8 (Z_to_bv 64 0); CB 3976 j4].

Ltac j_inner j m wr WP XF y2 y3 y4 y5 y6 y7 :=
eapply evt_cut;
[ eapply (inner_loop (bv_unsigned sp) j m) with (k := 3%nat) (wdone := []) (wrest := wr) (xrest := [y2; y3; y4; y5; y6; y7]) (i := 0);
[ lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia
| eassumption | eassumption | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia
| replace (bv_unsigned sp + -160 + 16 * 0) with (bv_unsigned sp + -160) by lia; exact WP
| replace (bv_unsigned sp + -192 + 8 * 0) with (bv_unsigned sp + -192) by lia; exact XF ]
| post_call rsegs m ].

Ltac j_tail :=
zstep; zstep; zstep;
zstep; zstep; if_false_z;
zstep; zstep; if_false_z;
zstep;
match goal with |- context [Z.land ?x 18446744073709551612] =>
rewrite (land_m4_al x) by (lia || (Z.div_mod_to_equations; lia)) end;
zstep; if_false_z.

Ltac j_wp :=
(rename MI0 into MI || idtac);
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -160) (f32 ?ws), L : length ?ws = 18%nat |- _ =>
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|? ?]]]]]]]]]]]]]]]]]]];
try (cbn in L; lia); rewrite !f32_cons, f32_nil in H; rename H into WP' end.

Ltac j_body j m wr WP XF y2 y3 y4 y5 y6 y7 qa :=
zstep; if_false_x; do 4 zstep;
j_inner j m wr WP XF y2 y3 y4 y5 y6 y7;
j_wp; j_tail;
zstep; if_false_z; do 3 zstep;
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
replace e with qa by (rewrite ?Z.shiftl_mul_pow2 by lia; lia) end;
zstep; if_false_z; zstep; zstep; zstep; if_false_z; zstep; if_false_x;
do 6 zstep; zstep; zstep; zstep;
zstep; if_false_z; zstep;
zstep; try rewrite swrap32_small by lia; zstep; zstep;
zstep.

#[using="IQ LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16"] Lemma jloop : forall (k : nat) (j qa : Z) (adone arest wp xf : list word) (aw : word) (ja j6 j4 : list byte)
(xs2 xs3 xs4 xs5 xs6 xs7 xs8 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length arest = k -> j + Z.of_nat k = 8 -> 1 <= j -> length adone = Z.to_nat (j - 1) -> qa = AK + 4 * (j - 1) ->
length wp = 18%nat -> length xf = 8%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4256) ->
rw_cells rsegs m (usp + -80) FRAME -> rw_cells rsegs m (usp + -88) [CB 8 ja] ->
rw_cells rsegs m (usp + -160) (f32 wp) ->
rw_cells rsegs m (usp + -192) (f32 xf) -> rw_cells rsegs m (usp + -4256) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 adone) -> rw_cells rsegs m qa (f32 (aw :: arest)) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 (-4)) (Z_to_bv 64 5) sp (Z_to_bv 64 2147483647)
(Z_to_bv 64 j) (Z_to_bv 64 AK) (Z_to_bv 64 8) (Z_to_bv 64 4) (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (18446744073709551615 - (usp + -192))) (Z_to_bv 64 (18446744073709551615 - (usp + -160)))
xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 (-8)) (Z_to_bv 64 64) (Z_to_bv 64 8589934592) (Z_to_bv 64 1))
G (Z_to_bv 64 0x27d9c) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros j qa adone arest wp xf aw ja j6 j4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 G fc m
LR Hjk Hj LD Hqa Lwp Lxf FRM MI MU WM ST FR PADA WP XF LJ ADONE ACUR;
pose proof (rw_cells_bound _ _ _ _ ACUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ ADONE) as BD; rewrite cells_size_f32, LD in BD;
destruct wp as [|v0 [|v1 [|v2 [|v3 wp]]]]; try (cbn in Lwp; lia);
destruct xf as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|? ?]]]]]]]]]; try (cbn in Lxf; lia); cbn [length] in Lwp, Lxf;
rewrite !f32_cons in WP; rewrite !f32_cons, f32_nil in XF.
- destruct arest; [|cbn in LR; lia]. cbn [length] in Hjk. rewrite f32_cons, f32_nil in ACUR.
j_body j m wp WP XF y2 y3 y4 y5 y6 y7 qa.
rewrite (lts_lt_true8 8 (j + 1)) by lia. change (negb true) with false. cbv iota.
do 13 zstep.
chunk_snoc ADONE ACUR. rewrite f32_snoc in ADONE.
release_frame LJ ST (bv_unsigned sp + -192). release_frame XF ST (bv_unsigned sp + -160).
release_frame WP' ST (bv_unsigned sp + -88).
release_frame PADA ST (bv_unsigned sp + -80). release_frame FR ST (bv_unsigned sp).
apply evt_done; unfold lsp_to_lpc8_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
split; [exact ADONE|]. rewrite length_app, LD; cbn [length]; lia.
- destruct arest as [|aw' arest]; [cbn in LR; lia|]. cbn [length] in LR, Hjk, BC. rewrite !f32_cons in ACUR.
j_body j m wp WP XF y2 y3 y4 y5 y6 y7 qa.
rewrite (lts_ge_false8' 8 (j + 1)) by lia. change (negb false) with true. cbv iota.
chunk_uncons ACUR as AC1. chunk_snoc ADONE AC1. rewrite f32_snoc in ADONE.
eapply (IH (j + 1) (qa + 4) (adone ++ [_]) arest [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] [y0; y1; y2; y3; y4; y5; y6; y7]);
[ lia | lia | lia | rewrite length_app, LD; cbn [length]; lia | lia | reflexivity | reflexivity
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA
| exact WP' | exact XF | exact LJ | exact ADONE | exact ACUR ].
Qed.

#[using="IQ LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16"] Lemma tailJ0 : forall (aks wp xf : list word) (ja j6 j4 : list byte)
(t0 t1 t2 xa0 xa7 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length aks = 8%nat -> length wp = 18%nat -> length xf = 8%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4256) ->
rw_cells rsegs m (usp + -80) FRAME -> rw_cells rsegs m (usp + -88) [CB 8 ja] ->
rw_cells rsegs m (usp + -160) (f32 wp) ->
rw_cells rsegs m (usp + -192) (f32 xf) -> rw_cells rsegs m (usp + -4256) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 aks) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp t0 t1 t2 sp xs1 xa0 (Z_to_bv 64 AK) (Z_to_bv 64 8) (Z_to_bv 64 4)
(Z_to_bv 64 (usp + -160)) (Z_to_bv 64 (usp + -192)) (Z_to_bv 64 (18446744073709551615 - (usp + -192))) xa7
xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x27d40) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
intros until m. intros LA Lwp Lxf FRM MI MU WM ST FR PADA WP XF LJ A.
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
destruct wp as [|v0 [|v1 [|v2 [|v3 wp]]]]; try (cbn in Lwp; lia).
destruct xf as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|? ?]]]]]]]]]; try (cbn in Lxf; lia). cbn [length] in Lwp, Lxf.
rewrite !f32_cons in WP. rewrite !f32_cons, f32_nil in XF.
do 23 zstep. cond_prep.
rewrite (zb_lxor_ones (bv_unsigned sp + -160)) by lia.
zstep. if_false_x. do 4 zstep.
j_inner 0 m wp WP XF y2 y3 y4 y5 y6 y7.
j_wp. j_tail.
zstep. if_true_x. zstep. zstep.
zstep. zstep. zstep. zstep. if_true_x.
destruct aks as [|a0w arest]; [cbn in LA; lia|]. cbn [length] in LA. rewrite f32_cons in A.
eapply (jloop 7%nat 1 AK [] arest [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] [y0; y1; y2; y3; y4; y5; y6; y7]);
[ lia | lia | lia | reflexivity | lia | reflexivity | reflexivity
| assumption | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA
| exact WP' | exact XF | exact LJ
| apply rw_cells_nil; lia | exact A ].
Qed.

Ltac xl_checks := zstep; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z; zstep; zstep; if_false_z.
Ltac xl_tail := zstep; if_false_z; do 4 zstep; zstep; try rewrite swrap32_small by lia; zstep.

#[using="IQ LOW GLO SP63 AI AA AAI IQ0 IQ4 AK0 AK4 SP16"] Lemma xloop : forall (k : nat) (aks xdone xrest frest wp : list word) (qx qf ox : Z) (xw fw : word) (ja j6 j4 : list byte)
(t1 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length aks = 8%nat -> length xrest = k -> length frest = k -> (length xdone + k = 7)%nat -> length wp = 18%nat ->
qx = usp + -192 + 4 * Z.of_nat (length xdone) -> qf = IQ + 4 * Z.of_nat (length xdone) -> ox = 4 * Z.of_nat (length xdone) ->
t1 = Z_to_bv 64 (Z.of_nat (S k)) ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4256) ->
rw_cells rsegs m (usp + -80) FRAME -> rw_cells rsegs m (usp + -88) [CB 8 ja] ->
rw_cells rsegs m (usp + -160) (f32 wp) ->
rw_cells rsegs m (usp + -192) (f32 xdone) -> rw_cells rsegs m qx (f32 (xw :: xrest)) ->
rw_cells rsegs m (usp + -4256) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 aks) -> rw_cells rsegs m qf (f32 (fw :: frest)) ->
evt rsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -192)) gp tp (Z_to_bv 64 1) t1 (Z_to_bv 64 qx) sp xs1 (Z_to_bv 64 IQ) (Z_to_bv 64 AK)
(Z_to_bv 64 8) (Z_to_bv 64 4) (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 (usp + -192))
(Z_to_bv 64 (18446744073709551615 - (usp + -192))) (Z_to_bv 64 ox)
xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 qf) (Z_to_bv 64 qf) t5 t6)
G (Z_to_bv 64 0x27cc8) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros aks xdone xrest frest wp qx qf ox xw fw ja j6 j4 t1 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 t5 t6 G fc m
LA LXR LFR LXD Lwp Hqx Hqf Hox -> FRM MI MU WM ST FR PADA WP XD XC LJ A FQ;
pose proof (rw_cells_bound _ _ _ _ FQ) as BF; rewrite cells_size_f32 in BF; cbn [length] in BF;
pose proof (rw_cells_bound _ _ _ _ XC) as BXC; rewrite cells_size_f32 in BXC; cbn [length] in BXC;
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
- destruct xrest; [|cbn in LXR; lia]. destruct frest; [|cbn in LFR; lia]. cbn [length] in LXD.
rewrite f32_cons, f32_nil in XC. rewrite f32_cons, f32_nil in FQ.
change (Z.of_nat 1) with 1.
xl_checks. zstep. zstep. zstep. zstep. if_cases B.
+ do 7 zstep. xl_tail. zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD.
eapply (tailJ0 aks wp (xdone ++ [_]));
[ exact LA | exact Lwp | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact XD | exact LJ | exact A ].
+ do 5 zstep. xl_tail. zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD.
eapply (tailJ0 aks wp (xdone ++ [_]));
[ exact LA | exact Lwp | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact XD | exact LJ | exact A ].
- destruct xrest as [|xw' xrest]; [cbn in LXR; lia|]. destruct frest as [|fw' frest]; [cbn in LFR; lia|]. cbn [length] in LXR, LFR, LXD, BF, BXC.
rewrite !f32_cons in XC. rewrite !f32_cons in FQ.
xl_checks. zstep. zstep. zstep. zstep. if_cases B.
+ do 7 zstep. xl_tail. zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. chunk_uncons FQ as F1.
eapply (IH aks (xdone ++ [_]) xrest frest wp (qx + 4) (qf + 4) (ox + 4));
[ exact LA | lia | lia | rewrite length_app; cbn [length]; lia | exact Lwp
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| f_equal; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact XD | exact XC | exact LJ | exact A | exact FQ ].
+ do 5 zstep. xl_tail. zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. chunk_uncons FQ as F1.
eapply (IH aks (xdone ++ [_]) xrest frest wp (qx + 4) (qf + 4) (ox + 4));
[ exact LA | lia | lia | rewrite length_app; cbn [length]; lia | exact Lwp
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| f_equal; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact XD | exact XC | exact LJ | exact A | exact FQ ].
Qed.

End S.
