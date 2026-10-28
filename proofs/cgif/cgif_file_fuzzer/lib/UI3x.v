(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09 YP0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI00 UI3t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0j YI0k UI3w YI5a YI2w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma ra_np2_aux_ge : forall f n p, 0 <= p -> n <= 2 ^ (p + Z.of_nat f) -> n <= 2 ^ YO07.np2_aux f n p /\ p <= YO07.np2_aux f n p <= p + Z.of_nat f.
Proof.
induction f as [|f IH]; intros n p Hp Hn; cbn [YO07.np2_aux].
- rewrite Z.add_0_r in Hn. lia.
- destruct (Z.ltb_spec (2 ^ p) n) as [Hl|Hl].
+ assert (Hn' : n <= 2 ^ (p + 1 + Z.of_nat f)) by (replace (p + 1 + Z.of_nat f) with (p + Z.of_nat (S f)) by lia; exact Hn).
pose proof (IH n (p + 1) ltac:(lia) Hn'). lia.
+ lia.
Qed.
Lemma ra_pal_pow_bounds : forall n, 0 <= n <= 256 -> n <= 2 ^ YO07.pal_pow n /\ 1 <= YO07.pal_pow n <= 8.
Proof.
intros n Hn. unfold YO07.pal_pow, YO07.calcNextPower2Ex.
pose proof (ra_np2_aux_ge 17 n 0 ltac:(lia) ltac:(cbn; lia)) as [G1 G2].
assert (G3 : forall f p, 0 <= p <= 8 -> YO07.np2_aux f n p <= 8).
{ induction f as [|f IH]; intros p Hp; cbn [YO07.np2_aux]; [lia|].
destruct (Z.ltb_spec (2 ^ p) n) as [Hl|Hl]; [|lia].
assert (p < 8) by (destruct (Z.eq_dec p 8) as [->|]; [change (2 ^ 8) with 256 in Hl; lia | lia]).
apply IH. lia. }
pose proof (G3 17%nat 0 ltac:(lia)).
split; [| lia]. eapply Z.le_trans; [exact G1|]. apply Z.pow_le_mono_r; lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ra_gce_length : forall cx, Z.of_nat (length (ra_gce cx)) <= 8.
Proof using. intros cx. unfold ra_gce, YO07.u16le. destruct (_ || _); cbn; lia. Qed.
Lemma ra_hdr_length : forall cx, Z.of_nat (length (ra_hdr cx)) = 10.
Proof using. intros cx. unfold ra_hdr, YO07.u16le. cbn. reflexivity. Qed.
Lemma ra_lctb_length : forall cx LCTV, 0 <= c_slct cx <= 256 -> Z.of_nat (length (ra_lctb cx LCTV)) <= 768.
Proof using.
intros cx LCTV Hs. unfold ra_lctb, YO07.zeros.
destruct (Z.eqb_spec (c_slct cx) 0) as [E|Hnz]; cbn [negb]; [cbn; lia|].
rewrite length_app, repeat_length. pose proof (firstn_le_length (Z.to_nat (c_slct cx * 3)) LCTV) as F.
destruct (ra_pal_pow_bounds (c_slct cx) Hs) as [T1 PP].
assert (T : 2 ^ YO07.pal_pow (c_slct cx) <= 256) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma ra_record_length : forall cx LCTV raster, 0 <= c_slct cx <= 256 -> Z.of_nat (length raster) <= 2 * c_nP cx + 16 ->
Z.of_nat (length (ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV ++ [ra_iclen cx - 1] ++ raster)) <= 2 * c_nP cx + 2048.
Proof using.
intros cx LCTV raster Hs HM. rewrite !length_app. cbn [length].
pose proof (ra_gce_length cx). pose proof (ra_hdr_length cx). pose proof (ra_lctb_length cx LCTV Hs). lia.
Qed.
Definition ra_rb (b : rbound) (s : astate) (Lbb : Z) : Prop :=
exists bo, res_ok s bo /\ forall s', res_ok s' (rb_free bo Lbb) -> res_ok s' (rawadd_rb b).
Definition ra_exitX (cx : ra_cx) (IMGV LCTV : list Z) (res rcur' : Z) : Prop :=
exists code, ra_model cx IMGV LCTV = (code, []) /\ Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32.
Lemma exitX_prev : forall cx IMGV LCTV (a0 : word), c_rcur cx <> 0 -> c_rcur cx <> 6 -> 0 <= c_rcur cx < 2 ^ 32 ->
bv_unsigned a0 = (if c_rcur cx <? 2 ^ 31 then c_rcur cx else c_rcur cx - 2 ^ 32 + 2 ^ 64) -> ra_exitX cx IMGV LCTV (bv_unsigned a0) (c_rcur cx).
Proof using.
intros cx IMGV LCTV a0 H0 H6 Hr Ha. exists (rc_int (c_rcur cx)).
assert (Hne : rc_int (c_rcur cx) <> 0 /\ rc_int (c_rcur cx) <> 6) by (unfold rc_int; destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)); lia).
split; [apply ra_model_prev; tauto|]. rewrite Ha. unfold rc_int.
destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)) as [Hlo | Hhi].
- split; [reflexivity | rewrite Z.mod_small; lia].
- split.
+ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (c_rcur cx - 2 ^ 32 + 2 ^ 64) with (c_rcur cx - 2 ^ 32 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
+ replace (c_rcur cx - 2 ^ 32) with (c_rcur cx + (-1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full, Z.mod_small; lia.
Qed.
Lemma exitX_badlct : forall cx IMGV LCTV (r : word), (c_rcur cx = 0 \/ c_rcur cx = 6) -> 256 < c_slct cx -> bv_unsigned r = 2 ^ 64 - 1 ->
ra_exitX cx IMGV LCTV (bv_unsigned r) (bv_unsigned r mod 2 ^ 32).
Proof using.
intros cx IMGV LCTV r Hr Hs Hv. exists (-1). split; [apply ra_model_badlct; assumption|]. rewrite Hv. split; [apply bv_eq; reflexivity | reflexivity].
Qed.
Lemma exitX_eindex : forall cx IMGV LCTV (r : word), (c_rcur cx = 0 \/ c_rcur cx = 6) -> c_slct cx <= 256 ->
YO07.lzw_stream (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) = None -> bv_unsigned r = 5 ->
ra_exitX cx IMGV LCTV (bv_unsigned r) (bv_unsigned r mod 2 ^ 32).
Proof using. intros cx IMGV LCTV r Hr Hs Hn Hv. exists 5. rewrite (ra_model_lzw cx IMGV LCTV Hr Hs), Hn, Hv. split; [reflexivity | split; reflexivity]. Qed.
Section c.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition ra_postR (FP : list (Z * Z)) (Q : Z -> Z -> Prop) (RP : astate -> Prop) (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem' (c_raw cx) LAY_Raw (rvals' cx rcur') /\
Permutation (blocks L' A') (blocks L A) /\
Q res rcur' /\ RP A'.
Definition ra_post4R (FP : list (Z * Z)) (Q : Z -> Z -> (word -> option byte) -> Model -> Prop) (RP : astate -> Prop) (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem' (c_raw cx) LAY_Raw (rvals' cx rcur') /\
Permutation (blocks L' A') (blocks L A) /\
Q res rcur' mem' md' /\ RP A'.
End c.
Lemma ra_rb_entry : forall s b, res_ok s b -> res_ok s (rawadd_rb b).
Proof using. intros s b H. apply (rawadd_exit s b 0 0); [unfold RAWADD_K, LZW_K; lia | lia | apply res_ok_acc0; exact H]. Qed.
Lemma ra_rb_plain : forall b s Lbb, 0 <= Lbb -> res_ok s (lzw_rb b (prN Lbb)) -> ra_rb b s Lbb.
Proof using.
intros b s Lbb HL H. exists (lzw_rb b (prN Lbb)). split; [exact H|]. intros s' H'. unfold lzw_rb in H'.
apply (rawadd_exit s' b LZW_K (prN Lbb - prN Lbb)); [unfold RAWADD_K, LZW_K; lia | lia |].
eapply res_ok_mono; [apply rb_free_acc | exact H'].
Qed.
Lemma ra_rb_plain_eidx : forall b s, res_ok s (lzw_rb b 0) -> res_ok s (rawadd_rb b).
Proof using. intros b s H. unfold lzw_rb in H. apply (rawadd_exit s b LZW_K 0); [unfold RAWADD_K, LZW_K; lia | lia | exact H]. Qed.
Lemma ra_rb_il : forall b s N Lbb, 0 <= N -> 0 <= Lbb ->
res_ok s (rb_free (lzw_rb (rb_acc b 1 (prN N)) (prN Lbb)) N) -> ra_rb b s Lbb.
Proof using.
intros b s N Lbb HN HL H. exists (rb_acc b (1 + LZW_K) (prN Lbb)). split.
- eapply res_ok_mono; [| exact H]. rewrite lzw_rb_acc1. eapply rb_le_trans; [apply rb_free_acc|]. apply rb_acc_mono; [apply rb_le_refl | unfold LZW_K; lia | lia].
- intros s' H'. apply (rawadd_exit s' b (1 + LZW_K) (prN Lbb - prN Lbb)); [unfold RAWADD_K, LZW_K; lia | lia |].
eapply res_ok_mono; [apply rb_free_acc | exact H'].
Qed.
Lemma ra_rb_il_eidx : forall b s N, 0 <= N -> res_ok s (rb_free (lzw_rb (rb_acc b 1 (prN N)) 0) N) -> res_ok s (rawadd_rb b).
Proof using.
intros b s N HN H. apply (rawadd_exit s b (1 + LZW_K) (prN N + 0 - prN N)); [unfold RAWADD_K, LZW_K; lia | lia |].
rewrite lzw_rb_acc1 in H. eapply res_ok_mono; [apply rb_free_acc | exact H].
Qed.
Lemma ra_rb_il_malloc : forall b s N, 0 <= N -> res_ok s (rb_malloc b N) -> res_ok s (rb_acc b 1 (prN N)).
Proof using. intros b s N HN H. eapply res_ok_mono; [apply rb_malloc_acc; exact HN | exact H]. Qed.
End a.
