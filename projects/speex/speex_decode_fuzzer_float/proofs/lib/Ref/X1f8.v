(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1f7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

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
Local Notation usp := (bv_unsigned sp).
Local Notation W := [(lo, usp); (AK, AK + 40)].
Local Notation POST := (lsp_to_lpc_post AK lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
Local Notation FRAME := [C8 (Z_to_bv 64 0); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation LOWJ j6 j4 := [C8 (Z_to_bv 64 0); CB 88 j6; C8 (Z_to_bv 64 0); CB 3944 j4].

#[using="IQ LOW GLO SP63 AI AA AAI"] Lemma jloop : forall (k : nat) (j qa : Z) (adone arest wp xf : list word) (aw : word) (ja jb j6 j4 : list byte)
(t0 t1 t2 xa5 xa6 xa7 xs3 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length arest = k -> j + Z.of_nat k = 10 -> 1 <= j -> length adone = Z.to_nat (j - 1) -> qa = AK + 4 * (j - 1) ->
length wp = 22%nat -> length xf = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4256) ->
rw_cells rsegs m (usp + -64) FRAME -> rw_cells rsegs m (usp + -72) [CB 8 ja] ->
rw_cells rsegs m (usp + -160) (f32 wp) -> rw_cells rsegs m (usp + -168) [CB 8 jb] ->
rw_cells rsegs m (usp + -208) (f32 xf) -> rw_cells rsegs m (usp + -4256) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 adone) -> rw_cells rsegs m qa (f32 (aw :: arest)) ->
evt rsegs POST
(MS (mkR (Z_to_bv 64 145204) (Z_to_bv 64 (usp + -208)) gp tp t0 t1 t2 sp (Z_to_bv 64 10)
(Z_to_bv 64 j) (Z_to_bv 64 (usp + -204)) (Z_to_bv 64 2) (Z_to_bv 64 11) (Z_to_bv 64 (usp + -84)) xa5 xa6 xa7
(Z_to_bv 64 (AK + -4)) xs3 (Z_to_bv 64 (usp + -164)) (Z_to_bv 64 21474836480) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x23840) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros j qa adone arest wp xf aw ja jb j6 j4 t0 t1 t2 xa5 xa6 xa7 xs3 t3 t4 t5 t6 G fc m
LR Hjk Hj LD Hqa Lwp Lxf FRM MI MU WM ST FR PADA WP PADB XF LJ ADONE ACUR;
pose proof (rw_cells_bound _ _ _ _ ACUR) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ ADONE) as BD; rewrite cells_size_f32, LD in BD;
destruct wp as [|v0 [|v1 [|v2 [|v3 wp]]]]; try (cbn in Lwp; lia);
destruct xf as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|y9 [|? ?]]]]]]]]]]]; try (cbn in Lxf; lia); cbn [length] in Lwp, Lxf;
rewrite !f32_cons in WP; rewrite !f32_cons, f32_nil in XF.
- destruct arest; [|cbn in LR; lia]. cbn [length] in Hjk. rewrite f32_cons, f32_nil in ACUR.
zstep. if_true_x. zstep. zstep. zstep.
eapply evt_cut.
{ eapply (inner_loop (bv_unsigned sp) j m) with (k := 4%nat) (wdone := []) (wrest := wp) (xrest := [y2; y3; y4; y5; y6; y7; y8; y9]) (q := bv_unsigned sp + -164) (xq := bv_unsigned sp + -204);
[ lia | reflexivity | reflexivity | cbn [length Z.of_nat]; lia | cbn [length Z.of_nat]; lia | lia | lia
| exact FRM | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia
| replace (bv_unsigned sp + -164 + 4) with (bv_unsigned sp + -160) by lia; exact WP
| replace (bv_unsigned sp + -204 + -4) with (bv_unsigned sp + -208) by lia; exact XF ]. }
post_call rsegs m. rename MI0 into MI || idtac.
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -160) (f32 ?ws) |- _ => rename H into WP' end.
lazymatch goal with H : length ?ws = 22%nat |- _ => rename H into Lws end.
lazymatch type of WP' with rw_cells _ _ _ (f32 ?ws) =>
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|? ?]]]]]]]]]]]]]]]]]]]]]]];
try (cbn in Lws; lia) end.
rewrite !f32_cons, f32_nil in WP'.
zstep. if_false_x. do 8 zstep.
replace (AK + -4 + Z.shiftl j 2) with qa by (rewrite Z.shiftl_mul_pow2 by lia; lia).
zstep. zstep. zstep. zstep. zstep. zstep. if_false_x.

do 10 zstep.
chunk_snoc ADONE ACUR. rewrite f32_snoc in ADONE.
release_frame LJ ST (bv_unsigned sp + -208). release_frame XF ST (bv_unsigned sp + -168).
release_frame PADB ST (bv_unsigned sp + -160). release_frame WP' ST (bv_unsigned sp + -72).
release_frame PADA ST (bv_unsigned sp + -64). release_frame FR ST (bv_unsigned sp).
apply evt_done; unfold lsp_to_lpc_post.
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
split; [exact ADONE|]. rewrite length_app, LD; cbn [length]; lia.
- destruct arest as [|aw' arest]; [cbn in LR; lia|]. cbn [length] in LR, Hjk, BC. rewrite !f32_cons in ACUR.
zstep. if_true_x. zstep. zstep. zstep.
eapply evt_cut.
{ eapply (inner_loop (bv_unsigned sp) j m) with (k := 4%nat) (wdone := []) (wrest := wp) (xrest := [y2; y3; y4; y5; y6; y7; y8; y9]) (q := bv_unsigned sp + -164) (xq := bv_unsigned sp + -204);
[ lia | reflexivity | reflexivity | cbn [length Z.of_nat]; lia | cbn [length Z.of_nat]; lia | lia | lia
| exact FRM | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia
| replace (bv_unsigned sp + -164 + 4) with (bv_unsigned sp + -160) by lia; exact WP
| replace (bv_unsigned sp + -204 + -4) with (bv_unsigned sp + -208) by lia; exact XF ]. }
post_call rsegs m. rename MI0 into MI || idtac.
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -160) (f32 ?ws) |- _ => rename H into WP' end.
lazymatch goal with H : length ?ws = 22%nat |- _ => rename H into Lws end.
lazymatch type of WP' with rw_cells _ _ _ (f32 ?ws) =>
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|? ?]]]]]]]]]]]]]]]]]]]]]]];
try (cbn in Lws; lia) end.
rewrite !f32_cons, f32_nil in WP'.
zstep. if_false_x. do 8 zstep.
replace (AK + -4 + Z.shiftl j 2) with qa by (rewrite Z.shiftl_mul_pow2 by lia; lia).
zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons ACUR as AC1. chunk_snoc ADONE AC1. rewrite f32_snoc in ADONE.
eapply (IH (j + 1) (qa + 4) (adone ++ [_]) arest [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9]);
[ lia | lia | lia | rewrite length_app, LD; cbn [length]; lia | lia | reflexivity | reflexivity
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA
| exact WP' | exact PADB | exact XF | exact LJ | exact ADONE | exact ACUR ].
Qed.

#[using="LOW GLO SP63 AI AA AAI"] Lemma tailJ0 : forall (aks wp xf : list word) (ja jb j6 j4 : list byte)
(t0 t1 t2 xa3 xa4 xa5 xa6 xa7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length aks = 10%nat -> length wp = 22%nat -> length xf = 10%nat ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4256) ->
rw_cells rsegs m (usp + -64) FRAME -> rw_cells rsegs m (usp + -72) [CB 8 ja] ->
rw_cells rsegs m (usp + -160) (f32 wp) -> rw_cells rsegs m (usp + -168) [CB 8 jb] ->
rw_cells rsegs m (usp + -208) (f32 xf) -> rw_cells rsegs m (usp + -4256) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 aks) ->
evt rsegs POST
(MS (mkR (Z_to_bv 64 145204) (Z_to_bv 64 (usp + -208)) gp tp t0 t1 t2 sp (Z_to_bv 64 10)
(Z_to_bv 64 (usp + -168)) (Z_to_bv 64 (usp + -208)) (Z_to_bv 64 (usp + -168)) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 AK) (Z_to_bv 64 (IQ + 40)) (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x237f0) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
intros until m. intros LA Lwp Lxf FRM MI MU WM ST FR PADA WP PADB XF LJ A.
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
destruct wp as [|v0 [|v1 [|v2 [|v3 wp]]]]; try (cbn in Lwp; lia).
destruct xf as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|y7 [|y8 [|y9 [|? ?]]]]]]]]]]]; try (cbn in Lxf; lia). cbn [length] in Lwp, Lxf.
rewrite !f32_cons in WP. rewrite !f32_cons, f32_nil in XF.
zstep. if_false_x.
do 19 zstep.
zstep. if_true_x. zstep. zstep. zstep.
eapply evt_cut.
{ eapply (inner_loop (bv_unsigned sp) 0 m) with (k := 4%nat) (wdone := []) (wrest := wp) (xrest := [y2; y3; y4; y5; y6; y7; y8; y9]) (q := bv_unsigned sp + -164) (xq := bv_unsigned sp + -204);
[ lia | reflexivity | reflexivity | cbn [length Z.of_nat]; lia | cbn [length Z.of_nat]; lia | lia | lia
| exact FRM | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia
| replace (bv_unsigned sp + -164 + 4) with (bv_unsigned sp + -160) by lia; exact WP
| replace (bv_unsigned sp + -204 + -4) with (bv_unsigned sp + -208) by lia; exact XF ]. }
post_call rsegs m. rename MI0 into MI || idtac.
lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -160) (f32 ?ws) |- _ => rename H into WP' end.
lazymatch goal with H : length ?ws = 22%nat |- _ => rename H into Lws end.
lazymatch type of WP' with rw_cells _ _ _ (f32 ?ws) =>
destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|? ?]]]]]]]]]]]]]]]]]]]]]]];
try (cbn in Lws; lia) end.
rewrite !f32_cons, f32_nil in WP'.
zstep. if_true. zstep. zstep. zstep. zstep. zstep. if_true_x.
destruct aks as [|a0w arest]; [cbn in LA; lia|]. cbn [length] in LA. rewrite f32_cons in A.
eapply (jloop 9%nat 1 AK [] arest [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] [y0; y1; y2; y3; y4; y5; y6; y7; y8; y9]);
[ lia | lia | lia | reflexivity | lia | reflexivity | reflexivity
| assumption | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA
| exact WP' | exact PADB | exact XF | exact LJ
| apply rw_cells_nil; lia | exact A ].
Qed.

#[using="LOW GLO SP63 AI AA AAI"] Lemma xloop : forall (k : nat) (aks xdone xrest frest wp : list word) (qx qf : Z) (xw fw : word) (ja jb j6 j4 : list byte)
(t0 t1 t2 xa3 xa4 xa5 xa6 xa7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length aks = 10%nat -> length xrest = k -> length frest = k -> (length xdone + k = 9)%nat -> length wp = 22%nat ->
qx = usp + -208 + 4 * Z.of_nat (length xdone) -> qf = IQ + 4 * Z.of_nat (length xdone) ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
stk rsegs m lo (usp + -4256) ->
rw_cells rsegs m (usp + -64) FRAME -> rw_cells rsegs m (usp + -72) [CB 8 ja] ->
rw_cells rsegs m (usp + -160) (f32 wp) -> rw_cells rsegs m (usp + -168) [CB 8 jb] ->
rw_cells rsegs m (usp + -208) (f32 xdone) -> rw_cells rsegs m qx (f32 (xw :: xrest)) ->
rw_cells rsegs m (usp + -4256) (LOWJ j6 j4) ->
rw_cells rsegs m AK (f32 aks) -> rw_cells rsegs m qf (f32 (fw :: frest)) ->
evt rsegs POST
(MS (mkR (Z_to_bv 64 145204) (Z_to_bv 64 (usp + -208)) gp tp t0 t1 t2 sp (Z_to_bv 64 10)
(Z_to_bv 64 (usp + -168)) (Z_to_bv 64 (usp + -208)) (Z_to_bv 64 qx) xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 AK) (Z_to_bv 64 qf) (Z_to_bv 64 (usp + -160)) (Z_to_bv 64 5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x237a0) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AI, AA, AAI. unfold NB_GLOBALS_TOP in GLO.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
induction k as [|k IH]; intros aks xdone xrest frest wp qx qf xw fw ja jb j6 j4 t0 t1 t2 xa3 xa4 xa5 xa6 xa7 t3 t4 t5 t6 G fc m
LA LXR LFR LXD Lwp Hqx Hqf FRM MI MU WM ST FR PADA WP PADB XD XC LJ A FQ;
pose proof (rw_cells_bound _ _ _ _ FQ) as BF; rewrite cells_size_f32 in BF; cbn [length] in BF;
pose proof (rw_cells_bound _ _ _ _ A) as BA; rewrite cells_size_f32, LA in BA.
- destruct xrest; [|cbn in LXR; lia]. destruct frest; [|cbn in LFR; lia]. cbn [length] in LXD.
rewrite f32_cons, f32_nil in XC. rewrite f32_cons, f32_nil in FQ.
zstep. zstep. zstep. zstep. if_cases B.
+ do 7 zstep. zstep. zstep. zstep. zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (qf + 4) with (IQ + 40) by lia. replace (qx + 4) with (bv_unsigned sp + -168) by lia.
eapply (tailJ0 aks wp (xdone ++ [_]));
[ exact LA | exact Lwp | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact LJ | exact A ].
+ do 5 zstep. zstep. zstep. zstep. zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (qf + 4) with (IQ + 40) by lia. replace (qx + 4) with (bv_unsigned sp + -168) by lia.
eapply (tailJ0 aks wp (xdone ++ [_]));
[ exact LA | exact Lwp | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact LJ | exact A ].
- destruct xrest as [|xw' xrest]; [cbn in LXR; lia|]. destruct frest as [|fw' frest]; [cbn in LFR; lia|]. cbn [length] in LXR, LFR, LXD, BF.
rewrite !f32_cons in XC. rewrite !f32_cons in FQ.
zstep. zstep. zstep. zstep. if_cases B.
+ do 7 zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. chunk_uncons FQ as F1.
eapply (IH aks (xdone ++ [_]) xrest frest wp (qx + 4) (qf + 4));
[ exact LA | lia | lia | rewrite length_app; cbn [length]; lia | exact Lwp
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact XC | exact LJ | exact A | exact FQ ].
+ do 5 zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. chunk_uncons FQ as F1.
eapply (IH aks (xdone ++ [_]) xrest frest wp (qx + 4) (qf + 4));
[ exact LA | lia | lia | rewrite length_app; cbn [length]; lia | exact Lwp
| rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR | exact PADA | exact WP | exact PADB | exact XD | exact XC | exact LJ | exact A | exact FQ ].
Qed.
End S.
