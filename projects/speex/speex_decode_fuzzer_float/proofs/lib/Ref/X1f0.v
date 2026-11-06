(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1hm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

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

Variables (EB eoff p IP q lo : Z) (eb c : list word) (pad : list byte) (m0 : mem).

Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.

Variables (mi mj d a2v a3v frow : Z) (xra t3 t4 t5 t6 xs3 xs4 xs5 : word) (g0 g1 g2 g3 g4 g5 g6 : word).
Hypothesis LEB : length eb = 500%nat.
Hypothesis LC : length c = 28%nat.
Hypothesis R1 : 0 <= eoff - p - 6.
Hypothesis R2 : eoff - p <= 414.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis Hq : q + 176 = bv_unsigned sp.
Hypothesis QLO : lo <= q.
Hypothesis GLO : NB_GLOBALS_TOP <= lo.
Hypothesis GIP : NB_GLOBALS_TOP <= IP.
Hypothesis FROW : frow + 28 <= NB_GLOBALS_TOP.
Hypothesis AEB : apart EB 2000 lo (q + 176 - lo).
Hypothesis AIP : apart IP 320 lo (q + 176 - lo).
Hypothesis AIE : apart IP 320 EB 2000.
Hypothesis Hmi : 0 <= mi <= 3.
Hypothesis Hmj : 0 <= mj <= 6.
Hypothesis Hd : d = mj - p - 3.
Hypothesis Ha2 : a2v = EB + 4 * eoff - 12.
Hypothesis Ha3 : a3v = EB + 4 * eoff + 16.
Local Notation exc := (EB + 4 * eoff).
Local Notation FRAME := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Local Notation W := [(lo, q + 176); (IP, IP + 320)].

Definition ip_post : machine_state -> Prop :=
fun ms' => exists (rv : word) (kk : iclob) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ip' : list word),
ms' = MS (callR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv kk) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (IP, IP + 320)] m0 m'
/\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' IP (f32 ip') /\ length ip' = 80%nat.

Ltac store_tail cs XC :=
do 3 zstep;
match goal with |- context [Z_to_bv 64 (IP + Z.shiftl ?ii 2)] =>
replace (IP + Z.shiftl ii 2) with cs by (rewrite Z.shiftl_mul_pow2 by lia; lia) end;
zstep; zstep; first [rewrite swrap32_mod64_add by lia | rewrite swrap32_small by lia]; zstep.
Ltac epilogue PAD CORR FR ST MU :=
do 9 zstep;
apply rw_cells_f32_CB in CORR; rewrite LC in CORR; change (4 * 28)%nat with 112%nat in CORR;
chunk_cat PAD CORR; chunk_cat PAD FR;
release_frame PAD ST (q + 176);
rewrite Hq in ST; rewrite Hq in MU; rewrite Hq; rewrite Z_to_bv_lit_self;
apply evt_done; unfold ip_post;
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _; split; [reflexivity|];
split; [exact MU|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
split; [exact ST|].

#[using="mj LEB LC R1 R2 R3 R4 Hq QLO GLO GIP FROW AEB AIP AIE Hmi Hmj Hd Ha2 Ha3"] Lemma floopA : forall (k : nat) (done rest : list word) (i cs di : Z) (cw : word) (t0 t1 t2 : word)
(G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> cs = IP + 4 * i -> di = d + i -> 1 <= mi ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m IP (f32 done) -> rw_cells rsegs m cs (f32 (cw :: rest)) ->
rw_cells rsegs m (q + 120) FRAME -> rw_cells rsegs m q [CB 8 pad] -> rw_cells rsegs m (q + 8) (f32 c) ->
stk rsegs m lo q -> ro_cells rsegs m frow (f32 [g0; g1; g2; g3; g4; g5; g6]) ->
evt rsegs ip_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 (Z_to_bv 64 IP) (Z_to_bv 64 exc) (Z_to_bv 64 mi) (Z_to_bv 64 i)
(Z_to_bv 64 a2v) (Z_to_bv 64 a3v) (Z_to_bv 64 d) (Z_to_bv 64 frow) (Z_to_bv 64 80) (Z_to_bv 64 di)
(Z_to_bv 64 p) xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x21a98) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AEB, AIP, AIE. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO', GIP, FROW.
induction k as [|k IH]; intros done rest i cs di cw t0 t1 t2 G fc m LR LD Hi Hcs Hdi Hmi1 FRM MI MU WM XEB XD XC FR PAD CORR ST RO;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ CORR) as BCO; rewrite cells_size_f32, LC in BCO;
first [ pose proof (eb_win7 m EB eb (eoff + d + i - 3) XEB LEB ltac:(lia) ltac:(lia)) as sfP_; sf_destruct 8%nat sfP_ as y0 y1 y2 y3 y4 y5 y6 WIN | sf_fb; destruct (eb_win7 m EB eb (eoff + d + i - 3) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & WIN) ];
remember (EB + 4 * (eoff + d + i - 3)) as rb eqn:Hrb;
rewrite !f32_cons, f32_nil in WIN; pose proof RO as ROW; rewrite !f32_cons, f32_nil in ROW.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
zstep. if_false_x. do 5 zstep.
rewrite (addr_shift2 a2v di rb) by lia. rewrite (addr_shift2 a3v di (rb + 28)) by lia.
do 6 zstep. if_true_x. do 6 zstep. if_true_x. do 6 zstep. if_true_x. do 6 zstep. if_true_x.
do 6 zstep. if_true_x. do 6 zstep. if_true_x. do 6 zstep. if_false_x.
zstep. store_tail cs XC. if_false_x. clear WIN ROW.
chunk_snoc XD XC. rewrite f32_snoc in XD.
epilogue PAD CORR FR ST MU.
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
zstep. if_false_x. do 5 zstep.
rewrite (addr_shift2 a2v di rb) by lia. rewrite (addr_shift2 a3v di (rb + 28)) by lia.
do 6 zstep. if_true_x. do 6 zstep. if_true_x. do 6 zstep. if_true_x. do 6 zstep. if_true_x.
do 6 zstep. if_true_x. do 6 zstep. if_true_x. do 6 zstep. if_false_x.
zstep. store_tail cs XC. if_true_x. clear WIN ROW.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (cs + 4) (di + 1) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia | lia | lia
| assumption | exact MI | exact MU | exact WM | exact XEB | exact XD | exact XC | exact FR | exact PAD | exact CORR | exact ST | exact RO ].
Qed.

#[using="mj LEB LC R1 R2 R3 R4 Hq QLO GLO AEB AIP AIE Hmi Hmj Hd"] Lemma floopB : forall (k : nat) (done rest : list word) (i cs di : Z) (cw : word) (t0 t1 t2 xa5 : word)
(G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> cs = IP + 4 * i -> di = d + i -> mi = 0 ->
frm0 fc -> mem_inv rsegs m -> munch W m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m IP (f32 done) -> rw_cells rsegs m cs (f32 (cw :: rest)) ->
rw_cells rsegs m (q + 120) FRAME -> rw_cells rsegs m q [CB 8 pad] -> rw_cells rsegs m (q + 8) (f32 c) ->
stk rsegs m lo q ->
evt rsegs ip_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 (Z_to_bv 64 IP) (Z_to_bv 64 exc) (Z_to_bv 64 mi) (Z_to_bv 64 i)
(Z_to_bv 64 a2v) (Z_to_bv 64 a3v) (Z_to_bv 64 d) xa5 (Z_to_bv 64 80) (Z_to_bv 64 di)
(Z_to_bv 64 p) xs3 xs4 xs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x21a98) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AEB, AIP, AIE. pose proof GLO as GLO'. unfold NB_GLOBALS_TOP in GLO', GIP, FROW.
induction k as [|k IH]; intros done rest i cs di cw t0 t1 t2 xa5 G fc m LR LD Hi Hcs Hdi Hmi0 FRM MI MU WM XEB XD XC FR PAD CORR ST;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ CORR) as BCO; rewrite cells_size_f32, LC in BCO;
destruct (eb_win1 m EB eb (eoff + d + i) XEB LEB ltac:(lia) ltac:(lia)) as (y0 & WIN);
remember (EB + 4 * (eoff + d + i)) as rb eqn:Hrb;
rewrite !f32_cons, f32_nil in WIN; subst mi.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
zstep. if_true_x. zstep. rewrite swrap32_mod64_add by lia. zstep. zstep.
rewrite (addr_shift2 exc (d + i) rb) by lia. zstep.
store_tail cs XC. if_false_x. clear WIN.
chunk_snoc XD XC. rewrite f32_snoc in XD.
epilogue PAD CORR FR ST MU.
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
zstep. if_true_x. zstep. rewrite swrap32_mod64_add by lia. zstep. zstep.
rewrite (addr_shift2 exc (d + i) rb) by lia. zstep.
store_tail cs XC. if_true_x. clear WIN.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (cs + 4) (di + 1) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia | lia | lia
| assumption | exact MI | exact MU | exact WM | exact XEB | exact XD | exact XC | exact FR | exact PAD | exact CORR | exact ST ].
Qed.
End D.
