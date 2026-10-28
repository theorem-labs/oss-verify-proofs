(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0px X0q5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1ky X1kt X1kg.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rrealloc_entry : Z := 0x33270.

Definition rre_hdr_post (ra sp gp tp t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(P G B E sc mword rsv stride : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t2 t3 t4,
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 4 - stride)) t2 s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword)
(Z_to_bv 64 88424) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - rsv)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x33454) fc None m (seg_rom rsegs).

Lemma rre_hdr_walk2 : forall (ra sp gp tp t2 t3 t4 t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc m
(P G B : Z) (b3 off16 last_idx freeable sc maplen r32 : Z),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
let stride := if negb (maplen =? 0) && (last_idx =? 0) then maplen * 4096 - 16 else 16 * size_class sc in
let E := B + 16 + stride * idx + stride - 4 in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
bv_unsigned a0 = P -> 0 <= B -> 16 <= stride -> P <= E -> E + 8 <= 2^64 ->
(maplen = 0 \/ last_idx <> 0 -> sc < 48 /\ ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
(maplen <> 0 -> off16 <= maplen * 256 - 1) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ ov_read_bytes rsegs m (wa (E - 4)) 4 = Some (le4 (wz r32)) /\ ov_read_bytes rsegs m (wa (E - 5)) 1 = Some [b8 0]) ->
rsv <= E - P -> ov_read_bytes rsegs m (wa (E - rsv)) 1 = Some [b8 0] -> ov_read_bytes rsegs m (wa E) 1 = Some [b8 0] ->
evt rsegs (rre_hdr_post ra sp gp tp t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 P G B E sc mword rsv stride F fc m)
(MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword)
(Z_to_bv 64 88424) (wz off16) (wz b3) t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x333bc) fc None m (seg_rom rsegs)).
Proof.
intros until r32. intros idx mword stride E rsv0 rsv HP B0 S16 PE E64 RS B3 O16 LI FB SC ML Hml BIG RSVLE RZ RE0.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
assert (MW4 : Z.shiftr mword 12 = maplen).
{ subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
rewrite Z.div_add, Z.div_small by lia. lia. }

assert (TAIL : forall (x7 x28 : word),
evt rsegs (rre_hdr_post ra sp gp tp t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 P G B E sc mword rsv stride F fc m)
(MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) x7 s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword)
(Z_to_bv 64 88424) (Z_to_bv 64 stride) (wz b3) t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
F (Z_to_bv 64 0x333e4) fc None m (seg_rom rsegs))).
{ intros x7 x28.
pose proof (bv_unsigned_in_range 64 a0) as AR0. change (bv_modulus 64) with (2^64) in AR0.

st1. st1. st1. st1. st1. st1. st1.
rewrite ?wz_unsigned, ?unsigned_lit by lia.
replace (B + stride * idx + 16 + stride + -4) with E by (unfold E; lia).
replace (B + stride * idx + 16 + stride) with (E + 4) by (unfold E; lia).
replace (B + stride * idx + 16) with (E + 4 - stride) by (unfold E; lia).
fold rsv0.

st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
-
replace (Z_to_bv 64 rsv0) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).

st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }

st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
rewrite HP. unfold rre_hdr_post. finish.
- first [ pose proof (BIG ltac:(lia)) as sfP_; sf_destruct 4%nat sfP_ as R5 R32 RB4 RB5 | sf_fb; destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5) ].

st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

replace (E - 4) with (E + 4 + -8) in RB4 by lia.
st1. rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

replace (E - 5) with (E + 4 + -9) in RB5 by lia.
st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
replace (wz r32) with (Z_to_bv 64 rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
rewrite HP. unfold rre_hdr_post. finish. }

st1. rewrite MW4. st1. if_cases K12; zify_cond K12; rewrite ?wz_unsigned, ?unsigned_lit in K12 by lia.
-
destruct (RS ltac:(left; exact K12)) as [SC48 RS'].
assert (RS'' : ov_read_bytes rsegs m (Z_to_bv 64 (88424 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (88424 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS'. }
pose proof (size_class_range sc ltac:(lia)) as SZ.
st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. rewrite ?zx16_wz by lia. st1.
rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (size_class sc * 16) with stride by (unfold stride; rewrite K12; cbn; lia).
apply TAIL.
-
st1. st1. st1. if_cases K13; zify_cond K13.
2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K13 by lia. change (2^8) with 256 in K13. change 18446744073709551615 with (Z.ones 64) in K13.
rewrite Z.land_ones, ?wz_unsigned, ?unsigned_lit in K13 by lia. rewrite Z.mod_small in K13 by lia. lia. }

st1. if_cases K14; zify_cond K14; rewrite ?wz_unsigned, ?unsigned_lit in K14 by lia.
+
st1. st1. rewrite land_pgmask by lia.
assert (MP : mword - mword mod 4096 = maplen * 4096).
{ replace mword with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
rewrite MP. st1. st1.
replace (maplen * 4096 + -16) with stride by (unfold stride; replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; lia); rewrite K14; cbn; lia).
apply TAIL.
+
destruct (RS ltac:(right; exact K14)) as [SC48 RS'].
assert (RS'' : ov_read_bytes rsegs m (Z_to_bv 64 (88424 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (88424 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS'. }
pose proof (size_class_range sc ltac:(lia)) as SZ.
st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia. rewrite ?zx16_wz by lia. st1.
rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (size_class sc * 16) with stride by (unfold stride; replace (last_idx =? 0) with false by (symmetry; apply Z.eqb_neq; lia); rewrite andb_false_r; lia).
apply TAIL.
Qed.

Definition rre_gm_post (ra sp gp tp x18 t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(G B : Z) (b3 off16 last_idx sc : Z) (mword : Z)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t3 t4,
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (Z.land b3 31)) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 (wz G) a0 a1 (wz B) (Z_to_bv 64 sc) (wz mword)
(Z_to_bv 64 88424) (wz off16) (wz b3) x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x333bc) fc None m (seg_rom rsegs).

Lemma rre_hdr_walk1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m
(P G B A : Z) (b3 off16 avail freed last_idx freeable sc maplen secret: Z) (prev next : word),
let idx := Z.land b3 31 in
let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
bv_unsigned a0 = P -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
ov_read_bytes rsegs m (wa (P - 4)) 1 = Some [b8 0] ->
ov_read_bytes rsegs m (wa (P - 3)) 1 = Some [b8 b3] ->
ov_read_bytes rsegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
ov_read_bytes rsegs m (wa B) 8 = Some (le8 (wz G)) ->
rw_cells rsegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
ov_read_bytes rsegs m (wa A) 8 = Some (le8 (wz secret)) ->
ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
(sc < 48 -> ov_read_bytes rsegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
(sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
(48 <= sc -> sc = 63) ->
evt rsegs (rre_gm_post ra sp gp tp s2 t5 t6 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 G B b3 off16 last_idx sc mword F fc m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x332c8) fc None m (seg_rom rsegs)).
Proof.
intros until next. intros idx mword HP AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
Hidx Hav Hfr Hsc Hsc63.
assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (EA0 : a0 = Z_to_bv 64 P) by (rewrite <- HP; symmetry; apply Z_to_bv_bv_unsigned).

st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite ?unsigned_lit, zb_land_mask in K by lia. lia. }

rewrite EA0. st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }

st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16. st1.
assert (RG' : ov_read_bytes rsegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
{ replace (P - off16 * 16 + -16) with B by lia. exact RG. }
st1.
set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).

st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }

assert (MW1 : Z.land mword 31 = last_idx).
{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }

st1. rewrite sx32_wz_sxv by lia. st1. st1.
rewrite sllw1_word' by lia.
assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }

pose proof (sxv_range freed) as SXF.
st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }

st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }

assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. if_cases K8; zify_cond K8.
-   specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
rewrite GW, <- EA0. unfold rre_gm_post. finish.
- specialize (RS ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)). specialize (Hsc ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).

st1.
assert (RS' : ov_read_bytes rsegs m (Z_to_bv 64 (88424 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (88424 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
clear RS. pose proof (size_class_range sc ltac:(lia)) as SZ. st1.
try rewrite (Z.mod_small (size_class sc)) by lia. rewrite ?zx16_wz by lia. fold idx.
st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }

st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
st1. rewrite GW, <- EA0. unfold rre_gm_post. finish.
Qed.

