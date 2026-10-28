(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma eb_win7 : forall m EB (eb : list word) (n : Z), rw_cells rsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= n -> n + 7 <= 500 ->
exists y0 y1 y2 y3 y4 y5 y6, rw_cells rsegs m (EB + 4 * n) (f32 [y0; y1; y2; y3; y4; y5; y6]).
Proof.
intros m EB eb n X L Hn Hn2.
pose proof (rw_cells_f32_mid rsegs m EB eb (Z.to_nat n) 7 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 7 (skipn (Z.to_nat n) eb)) as w eqn:Hw.
assert (Lw : length w = 7%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|y6 [|? ?]]]]]]]]; try (cbn in Lw; lia).
first [ unshelve sf_eexists 7%nat; [ exact (y0) | exact (y1) | exact (y2) | exact (y3) | exact (y4) | exact (y5) | exact (y6) | ] | sf_fb; exists y0, y1, y2, y3, y4, y5, y6 ]. exact W.
Qed.
Lemma eb_win1 : forall m EB (eb : list word) (n : Z), rw_cells rsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= n -> n + 1 <= 500 ->
exists y0, rw_cells rsegs m (EB + 4 * n) (f32 [y0]).
Proof.
intros m EB eb n X L Hn Hn2.
pose proof (rw_cells_f32_mid rsegs m EB eb (Z.to_nat n) 1 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 1 (skipn (Z.to_nat n) eb)) as w eqn:Hw.
assert (Lw : length w = 1%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|? ?]]; try (cbn in Lw; lia).
exists y0. exact W.
Qed.

Lemma addr_shift2 : forall base x r, r = base + 4 * x ->
Z_to_bv 64 (base + Z.shiftl (x mod 18446744073709551616) 2) = Z_to_bv 64 r.
Proof.
intros base x r ->. apply Z_to_bv_eqm. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (base + (x - 18446744073709551616 * (x / 18446744073709551616)) * 4)
with ((base + 4 * x) + (- 4 * (x / 18446744073709551616)) * 18446744073709551616) by lia.
change (2^64) with 18446744073709551616. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma al_add4 : forall a o, a mod 4 = 0 -> o mod 4 = 0 -> (a + o) mod 4 = 0.
Proof. intros a o Ha Ho. rewrite Z.add_mod by lia. rewrite Ha, Ho. reflexivity. Qed.

Lemma swrap32_mod64_add : forall x k, -2^31 <= x + k < 2^31 ->
bv_swrap 32 (x mod 18446744073709551616 + k) = x + k.
Proof.
intros x k H. rewrite <- (swrap32_small (x + k)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z. f_equal.
rewrite (Z.mod_eq x 18446744073709551616) by lia.
replace (x - 18446744073709551616 * (x / 18446744073709551616) + k + 2147483648)
with ((x + k + 2147483648) + (- 4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

Section D.
Context {RCEIL : RunCeiling}.

Variables (EB eoff p IP q lo : Z) (eb c : list word) (m0 : mem).

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.

Variables (mi mj d frow : Z) (xra xs7 xs8 : word) (g0 g1 g2 g3 g4 g5 g6 : word).
Hypothesis LEB : length eb = 500%nat.
Hypothesis LC : length c = 28%nat.
Hypothesis R1 : 0 <= eoff - p - 6.
Hypothesis R2 : eoff - p <= 414.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis Hq : q + 192 = bv_unsigned sp.
Hypothesis QLO : lo <= q.
Hypothesis GLO : NB_GLOBALS_TOP <= lo.
Hypothesis GIP : NB_GLOBALS_TOP <= IP.
Hypothesis FROW : frow + 28 <= NB_GLOBALS_TOP.
Hypothesis AEB : apart EB 2000 lo (q + 192 - lo).
Hypothesis AIP : apart IP 320 lo (q + 192 - lo).
Hypothesis AIE : apart IP 320 EB 2000.
Hypothesis Hmi : 0 <= mi <= 3.
Hypothesis Hmj : 0 <= mj <= 6.
Hypothesis Hd : d = mj - p - 3.
Hypothesis EX0 : 0 < EB + 4 * eoff.
Hypothesis EL0 : 0 < EB + 4 * (eoff - p - 6).
Hypothesis EB4 : EB mod 4 = 0.
Hypothesis IP4 : IP mod 4 = 0.
Local Notation exc := (EB + 4 * eoff).
Local Notation FRAME := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation W := [(lo, q + 192); (IP, IP + 320)].

Definition ip_post : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ip' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (IP, IP + 320)] m0 m'
/\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' IP (f32 ip') /\ length ip' = 80%nat.

Ltac nrm := tnorm; rewrite ?subm64, ?Z.lxor_nilpotent; balits.
Ltac sg :=
repeat match goal with |- context [?a mod 18446744073709551616] => rewrite (Z.mod_small a 18446744073709551616) by lia end;
try (match goal with |- context [Z.lxor (?x mod 18446744073709551616) 9223372036854775808] => rewrite (lxor_sign_mod x) by lia end);
try (match goal with |- context [Z.lxor (Z.lxor (Z.b2z (?Y <? ?A)) (Z.b2z (?y + 9223372036854775808 <? 9223372036854775808))) 1] =>
rewrite (ptr_sgn_guard A y Y) by lia end).
Ltac al3 := repeat match goal with |- context [Z.land ?a 3] =>
rewrite (land3_al a) by first [ assumption | apply al_add4; [ assumption | reflexivity ] ] end.
Ltac ubd := first [ lit_if | (nrm; sg; al3; first [ lit_if | sh_if_false | (bdec; lit_if) ]) | ub_dec ].
Ltac upto p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then ubd else ub_step)); first [ ub_at_pc p | ub_show_pc_fail p ].
Ltac fixaddr r := match goal with |- context [Z_to_bv 64 (?B + Z.shiftl (?x mod 18446744073709551616) 2)] => rewrite (addr_shift2 B x r) by lia end.
Ltac tap r := upto 0x24e4c%Z; nrm; fixaddr r; upto 0x24e84%Z; zstep.
Ltac tl cs Hcs := let A := fresh "A" in assert (A : cs mod 4 = 0) by (clear - IP4 Hcs; Z.div_mod_to_equations; lia);
upto 0x24efc%Z;
match goal with |- context [Z_to_bv 64 (IP + ?e)] => replace (IP + e) with cs by (rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?Z.mod_small by lia; lia) end;
upto 0x24f0c%Z; nrm; zstep.
Ltac epilogue CORR FR ST MU :=
do 12 zstep;
apply rw_cells_f32_CB in CORR; rewrite LC in CORR; change (4 * 28)%nat with 112%nat in CORR;
chunk_cat CORR FR;
release_frame CORR ST (q + 192);
rewrite Hq in ST; rewrite Hq in MU; rewrite Hq; rewrite Z_to_bv_lit_self;
apply evt_done; unfold ip_post;
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split; [reflexivity|];
split; [exact MU|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
split; [exact ST|].

#[using="mj LEB LC R1 R2 R3 R4 Hq QLO GLO GIP FROW AEB AIP AIE Hmi Hmj Hd EX0 EL0 EB4 IP4"] Lemma floopA : forall (k : nat) (done rest : list word) (i cs : Z) (cw : word) (xs2 xs4 xs5 xs6 xt5 xt6 : word)
(G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> cs = IP + 4 * i -> 1 <= mi ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m IP (f32 done) -> rw_cells rsegs m cs (f32 (cw :: rest)) ->
rw_cells rsegs m (q + 112) FRAME -> rw_cells rsegs m q (f32 c) ->
stk rsegs m lo q -> ro_cells rsegs m frow (f32 [g0; g1; g2; g3; g4; g5; g6]) ->
evt rsegs ip_post
(MS (mkR xra (Z_to_bv 64 q) gp tp (Z_to_bv 64 0x11354) (Z_to_bv 64 (28 * (mi - 1))) (Z_to_bv 64 frow) (Z_to_bv 64 exc) (Z_to_bv 64 IP)
(Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - IP)) (Z_to_bv 64 mi) (Z_to_bv 64 3) (Z_to_bv 64 28) (Z_to_bv 64 0) (Z_to_bv 64 (p - mj + 3)) (Z_to_bv 64 0)
xs2 (Z_to_bv 64 1) xs4 xs5 xs6 xs7 xs8 s9 s10 s11 (Z_to_bv 64 (18446744073709551615 - frow)) (Z_to_bv 64 80) xt5 xt6)
G (Z_to_bv 64 0x24e00) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AEB, AIP, AIE. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO', GIP, FROW.
induction k as [|k IH]; intros done rest i cs cw xs2 xs4 xs5 xs6 xt5 xt6 G fc m LR LD Hi Hcs Hmi1 FRM MI MU WM XEB XD XC FR CORR ST RO;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ CORR) as BCO; rewrite cells_size_f32, LC in BCO;
first [ pose proof (eb_win7 m EB eb (eoff + d + i - 3) XEB LEB ltac:(lia) ltac:(lia)) as sfP_; sf_destruct 8%nat sfP_ as y0 y1 y2 y3 y4 y5 y6 WIN | sf_fb; destruct (eb_win7 m EB eb (eoff + d + i - 3) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & WIN) ];
remember (EB + 4 * (eoff + d + i - 3)) as rb eqn:Hrb;
rewrite !f32_cons, f32_nil in WIN; pose proof RO as ROW; rewrite !f32_cons, f32_nil in ROW;
pose proof (ro_cells_bound _ _ _ _ RO) as BRO; rewrite cells_size_f32 in BRO; cbn [length] in BRO;
assert (RB4 : rb mod 4 = 0) by (rewrite Hrb; clear - EB4; Z.div_mod_to_equations; lia).
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
zstep. if_false_x. upto 0x24e2c%Z.
tap rb. upto 0x24e2c%Z. tap (rb + 4). upto 0x24e2c%Z. tap (rb + 8). upto 0x24e2c%Z. tap (rb + 12). upto 0x24e2c%Z.
tap (rb + 16). upto 0x24e2c%Z. tap (rb + 20). upto 0x24e2c%Z. tap (rb + 24). upto 0x24ef0%Z.
tl cs Hcs. if_false_x. upto 0x24f18%Z. clear WIN ROW.
chunk_snoc XD XC. rewrite f32_snoc in XD.
epilogue CORR FR ST MU.
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
zstep. if_false_x. upto 0x24e2c%Z.
tap rb. upto 0x24e2c%Z. tap (rb + 4). upto 0x24e2c%Z. tap (rb + 8). upto 0x24e2c%Z. tap (rb + 12). upto 0x24e2c%Z.
tap (rb + 16). upto 0x24e2c%Z. tap (rb + 20). upto 0x24e2c%Z. tap (rb + 24). upto 0x24ef0%Z.
tl cs Hcs. if_true_x. clear WIN ROW.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (cs + 4) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia | lia
| assumption | exact MI | exact MU | exact WM | exact XEB | exact XD | exact XC | exact FR | exact CORR | exact ST | exact RO ].
Qed.

#[using="mj LEB LC R1 R2 R3 R4 Hq QLO GLO GIP AEB AIP AIE Hmi Hmj Hd EX0 EL0 EB4 IP4"] Lemma floopB : forall (k : nat) (done rest : list word) (i cs : Z) (cw : word) (t0 t1 t2 t3 xs2 xs4 xs5 xs6 xt5 xt6 : word)
(G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> cs = IP + 4 * i -> mi = 0 ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m IP (f32 done) -> rw_cells rsegs m cs (f32 (cw :: rest)) ->
rw_cells rsegs m (q + 112) FRAME -> rw_cells rsegs m q (f32 c) ->
stk rsegs m lo q ->
evt rsegs ip_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 (Z_to_bv 64 exc) (Z_to_bv 64 IP)
(Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - IP)) (Z_to_bv 64 mi) (Z_to_bv 64 3) (Z_to_bv 64 28) (Z_to_bv 64 0) (Z_to_bv 64 (p - mj + 3)) (Z_to_bv 64 0)
xs2 (Z_to_bv 64 1) xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 (Z_to_bv 64 80) xt5 xt6)
G (Z_to_bv 64 0x24e00) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AEB, AIP, AIE. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO', GIP, FROW.
induction k as [|k IH]; intros done rest i cs cw t0 t1 t2 t3 xs2 xs4 xs5 xs6 xt5 xt6 G fc m LR LD Hi Hcs Hmi0 FRM MI MU WM XEB XD XC FR CORR ST;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ CORR) as BCO; rewrite cells_size_f32, LC in BCO;
destruct (eb_win1 m EB eb (eoff + d + i) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & WIN);
remember (EB + 4 * (eoff + d + i)) as rb eqn:Hrb;
rewrite !f32_cons, f32_nil in WIN; subst mi;
assert (RB4 : rb mod 4 = 0) by (rewrite Hrb; clear - EB4; Z.div_mod_to_equations; lia).
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
upto 0x24ec4%Z. nrm. fixaddr rb. upto 0x24ef0%Z.
tl cs Hcs. if_false_x. upto 0x24f18%Z. clear WIN.
chunk_snoc XD XC. rewrite f32_snoc in XD.
epilogue CORR FR ST MU.
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
upto 0x24ec4%Z. nrm. fixaddr rb. upto 0x24ef0%Z.
tl cs Hcs. if_true_x. clear WIN.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (cs + 4) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia | lia
| assumption | exact MI | exact MU | exact WM | exact XEB | exact XD | exact XC | exact FR | exact CORR | exact ST ].
Qed.
End D.
