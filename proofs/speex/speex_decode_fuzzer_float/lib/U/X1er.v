(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1fd.
Import ListNotations.
Open Scope bv_scope.
Local Notation psegs := Ubsan.M.loaded_segments.

Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Record hpc := HPC { hc_n0 : word; hc_n1 : word; hc_n2 : word; hc_d1 : word; hc_d2 : word }.
Definition hp_coefs (filtID : Z) : hpc :=
if (filtID =? 0)%Z then HPC (Z_to_bv 64 18446744070479208398) (Z_to_bv 64 18446744072635080738) (Z_to_bv 64 18446744070479208398) (Z_to_bv 64 18446744070487581236) (Z_to_bv 64 18446744072625994785)
else if (filtID =? 1)%Z then HPC (Z_to_bv 64 18446744070479341274) (Z_to_bv 64 18446744072635212439) (Z_to_bv 64 18446744070479341274) (Z_to_bv 64 18446744070487712350) (Z_to_bv 64 18446744072626258691)
else if (filtID =? 2)%Z then HPC (Z_to_bv 64 18446744070479387747) (Z_to_bv 64 18446744072635259919) (Z_to_bv 64 18446744070479387747) (Z_to_bv 64 18446744070487767295) (Z_to_bv 64 18446744072626339557)
else if (filtID =? 3)%Z then HPC (Z_to_bv 64 18446744070479710205) (Z_to_bv 64 18446744072635581370) (Z_to_bv 64 18446744070479710205) (Z_to_bv 64 18446744070488093444) (Z_to_bv 64 18446744072626973568)
else HPC (Z_to_bv 64 18446744070477924270) (Z_to_bv 64 18446744072633796526) (Z_to_bv 64 18446744070477924270) (Z_to_bv 64 18446744070483041321) (Z_to_bv 64 18446744072615643578).

Definition hp_v (c : hpc) (st : word * word) (x : word) : word := fmadd_s RNE (hc_n0 c) (# x) (# (fst st)).
Definition hp_next (c : hpc) (st : word * word) (x : word) : word * word :=
(fmadd_s RNE (hc_d1 c) (hp_v c st x) (fmadd_s RNE (hc_n1 c) (# x) (# (snd st))),
fmadd_s RNE (hc_n2 c) (# x) (fmul_s RNE (hp_v c st x) (hc_d2 c))).
Fixpoint hp_st (c : hpc) (st : word * word) (xs : list word) : word * word :=
match xs with [] => st | x :: xs' => hp_st c (hp_next c st x) xs' end.
Fixpoint hp_ys (c : hpc) (st : word * word) (xs : list word) : list word :=
match xs with [] => [] | x :: xs' => hp_v c st x :: hp_ys c (hp_next c st x) xs' end.
Lemma hp_st_app : forall c a b st, hp_st c st (a ++ b) = hp_st c (hp_st c st a) b.
Proof. induction a; intros; cbn; [reflexivity| apply IHa]. Qed.
Lemma hp_ys_app : forall c a b st, hp_ys c st (a ++ b) = hp_ys c st a ++ hp_ys c (hp_st c st a) b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. reflexivity. Qed.
Lemma length_hp_ys : forall c xs st, length (hp_ys c st xs) = length xs.
Proof. induction xs; intros; cbn; [reflexivity|]. now rewrite IHxs. Qed.
#[local] Hint Rewrite length_hp_ys : chunk_sizes.

Lemma fnmsub_fmadd_s : forall md a b c, fnmsub_s md a b c = fmadd_s md (fneg_s a) b c.
Proof.
intros md a b c. unfold fnmsub_s, fmadd_s. do 4 f_equal.
unfold fneg_s. rewrite unbox_nan_box, Z_to_bv_unsigned. unfold fp_neg.
change (Z.shiftl 1 (fp_mw fmt_single + fp_ew fmt_single)) with (2^31)%Z.
pose proof (bv_unsigned_in_range 32 (unbox_s a)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 32)%Z with (2^32)%Z in R.
set (u := bv_unsigned (unbox_s a)) in *. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
symmetry. apply Z.mod_small.
destruct (Z.lt_ge_cases u (2^31)).
- rewrite zb_lxor_pow2_small by lia. lia.
- replace u with ((u - 2^31) + 2^31)%Z by lia. rewrite <- (zb_lxor_pow2_small (u - 2^31) 31) by lia.
rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. lia.
Qed.

Definition hp_pcoef_words : list word :=
[Z_to_bv 64 1065353216; Z_to_bv 64 3220480564; Z_to_bv 64 1063926817; Z_to_bv 64 1065353216; Z_to_bv 64 3220611678;
Z_to_bv 64 1064190723; Z_to_bv 64 1065353216; Z_to_bv 64 3220666623; Z_to_bv 64 1064271589; Z_to_bv 64 1065353216;
Z_to_bv 64 3220992772; Z_to_bv 64 1064905600; Z_to_bv 64 1065353216; Z_to_bv 64 3215940649; Z_to_bv 64 1053575610].
Definition hp_zcoef_words : list word :=
[Z_to_bv 64 1064624078; Z_to_bv 64 3220496418; Z_to_bv 64 1064624078; Z_to_bv 64 1064756954; Z_to_bv 64 3220628119;
Z_to_bv 64 1064756954; Z_to_bv 64 1064803427; Z_to_bv 64 3220675599; Z_to_bv 64 1064803427; Z_to_bv 64 1065125885;
Z_to_bv 64 3220997050; Z_to_bv 64 1065125885; Z_to_bv 64 1063339950; Z_to_bv 64 3219212206; Z_to_bv 64 1063339950].
Definition A_hp_pcoef : Z := 0x112dc.
Definition A_hp_zcoef : Z := 0x11318.

Lemma hp_pcoef_at : forall m, mem_inv psegs m -> bytes_at psegs m A_hp_pcoef (cells_bytes (f32 hp_pcoef_words)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold A_hp_pcoef; lia| unfold A_hp_pcoef; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.
Lemma hp_zcoef_at : forall m, mem_inv psegs m -> bytes_at psegs m A_hp_zcoef (cells_bytes (f32 hp_zcoef_words)).
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold A_hp_zcoef; lia| unfold A_hp_zcoef; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma cells_wf_f32_hp : forall ws, cells_wf (f32 ws).
Proof. induction ws; cbn; [exact I| split; [exact I| exact IHws]]. Qed.
Lemma rw_cells_recast_hp : forall segs m A cs cs',
rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
intros segs m A cs cs' [[Hwf Hb] Hw] Hwf' Hb'. split; [split; [exact Hwf'| rewrite Hb'; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), Hb', (cells_bytes_length cs Hwf). exact Hw.
Qed.
Lemma rw_cells_f32_of_CB : forall segs m A n ws,
rw_cells segs m A [CB n (cells_bytes (f32 ws))] -> rw_cells segs m A (f32 ws).
Proof.
intros segs m A n ws H. eapply rw_cells_recast_hp; [exact H| apply cells_wf_f32_hp|].
cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
Qed.
Lemma rw_cells_cons_at : forall segs m A B c cs,
rw_cells segs m A (c :: cs) -> B = (A + Z.of_nat (csize c))%Z -> rw_cells segs m A [c] /\ rw_cells segs m B cs.
Proof. intros segs m A B c cs H ->. apply rw_cells_uncons. exact H. Qed.
Lemma rw_cells_f32_at : forall segs m A B ws (i : nat),
rw_cells segs m A (f32 ws) -> B = (A + Z.of_nat (4 * i))%Z -> (i <= length ws)%nat ->
rw_cells segs m A (f32 (firstn i ws)) /\ rw_cells segs m B (f32 (skipn i ws)).
Proof.
intros segs m A B ws i H -> Hi. rewrite <- (firstn_skipn i ws) in H. rewrite f32_app in H.
apply rw_cells_app in H. rewrite cells_size_f32, firstn_length_le in H by exact Hi. exact H.
Qed.
Lemma rw_cells_join_at : forall segs m A B cs1 cs2,
rw_cells segs m A cs1 -> rw_cells segs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells segs m A (cs1 ++ cs2).
Proof. intros segs m A B cs1 cs2 H1 H2 ->. apply rw_cells_join; assumption. Qed.

Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D S n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom psegs)
/\ munch [(D, D + n)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ rw_cells psegs m' D [CB (Z.to_nat n) src]
/\ bytes_at psegs m' S src.
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
bytes_at psegs m S src -> length src = Z.to_nat n ->
rw_cells psegs m D [CB (Z.to_nat n) junk] ->
(0 <= D)%Z -> (D + n < 2^64)%Z -> (0 <= S)%Z -> (S + n < 2^64)%Z -> (0 <= n)%Z ->
(S + n <= D \/ D + n <= S)%Z ->
mem_inv psegs m ->
evt psegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c5c) fc None m (seg_rom psegs)).
Proof.
intros until junk. intros SRC LEN DST HD HD2 HS HS2 Hn SEP MI.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (X1fd.memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); change X1fd.rsegs with psegs; rewrite ?ED, ?ES, ?EN; eauto. }
intros ms' P. unfold X1fd.memcpy_post in P. change X1fd.rsegs with psegs in P. rewrite !ED, !ES, !EN in P. exact P.
Qed.

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs : list word) (m0 m1 : word) (p pm : Z).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 : word.
Variable mi : word -> option byte.
Variable lo : Z.
Local Notation N := (Z.of_nat (length xs)).
Local Notation W := ([(lo, bv_unsigned sp); (p, p + 4 * Z.of_nat (length xs)); (pm, pm + 8)]%Z).
Local Notation WL := ([(p, p + 4 * Z.of_nat (length xs)); (pm, pm + 8)]%Z).

Definition highpass_post (c : hpc) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g10 g11 g12 g13 g14 g15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF g0 g1 f2 f3 f4 f5 f6 f7 f8 f9 g10 g11 g12 g13 g14 g15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch W mi m' /\ wmono psegs mi m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' p (f32 (hp_ys c (m0, m1) xs))
/\ rw_cells psegs m' pm (f32 [fst (hp_st c (m0, m1) xs); snd (hp_st c (m0, m1) xs)])
/\ stk psegs m' lo (bv_unsigned sp).

Definition hp_exit (c : hpc) (xra xs4 : word) (FB : Z) (me : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 s1' a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g10 g11 g12 g13 g14 g15 fc' m',
ms' = MS (mkR xra (Z_to_bv 64 FB) gp tp t0 t1 t2 (Z_to_bv 64 pm) s1' a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) (Z_to_bv 64 p) xs4
s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g10 g11 g12 g13 g14 g15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22e84) fc' None m' (seg_rom psegs)
/\ munch WL me m' /\ wmono psegs me m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' p (f32 (hp_ys c (m0, m1) xs))
/\ rw_cells psegs m' pm (f32 [fst (hp_st c (m0, m1) xs); snd (hp_st c (m0, m1) xs)]).

Ltac hp_ck1 := zstep; if_false_z.

#[using="Type"] Lemma hp_loop : forall (c : hpc) (FB ZR PR : Z) (zn0 zn1 zn2 pd0 pd1 pd2 xra xs4 : word) (me : word -> option byte)
rest done x q (s1v t0v t1v a2v a3v a4v a5v a6v a7v f15v t6v g10 g11 g12 g13 g14 : word) fc m,
nan_box (low32 zn1) = hc_n1 c -> nan_box (low32 zn2) = hc_n2 c ->
fneg_s (nan_box (low32 pd1)) = hc_d1 c -> fneg_s (nan_box (low32 pd2)) = hc_d2 c ->
f15v = hc_n0 c ->
t0v = Z_to_bv 64 (-4) -> t1v = Z_to_bv 64 (-9) -> a7v = Z_to_bv 64 (-5) ->
a2v = Z_to_bv 64 1 -> a3v = Z_to_bv 64 1 -> a4v = Z_to_bv 64 1 -> a5v = Z_to_bv 64 1 -> a6v = Z_to_bv 64 1 ->
xs = done ++ x :: rest ->
q = (p + 4 * Z.of_nat (length done))%Z ->
s1v = Z_to_bv 64 (Z.of_nat (S (length rest))) ->
(N < 2^31)%Z ->
(p + 4 * N <= pm \/ pm + 8 <= p)%Z ->
(0 < p)%Z -> (p mod 4 = 0)%Z -> (0 < pm)%Z -> (pm mod 4 = 0)%Z ->
(ZR + 12 <= p \/ p + 4 * N <= ZR)%Z -> (ZR + 12 <= pm \/ pm + 8 <= ZR)%Z ->
(PR + 12 <= p \/ p + 4 * N <= PR)%Z -> (PR + 12 <= pm \/ pm + 8 <= PR)%Z ->
frm0 fc -> mem_inv psegs m -> munch WL me m -> wmono psegs me m ->
rw_cells psegs m ZR (f32 [zn0; zn1; zn2]) -> rw_cells psegs m PR (f32 [pd0; pd1; pd2]) ->
rw_cells psegs m p (f32 (hp_ys c (m0, m1) done)) ->
rw_cells psegs m q (f32 (x :: rest)) ->
rw_cells psegs m pm (f32 [fst (hp_st c (m0, m1) done); snd (hp_st c (m0, m1) done)]) ->
evt psegs (hp_exit c xra xs4 FB me)
(MS (mkR xra (Z_to_bv 64 FB) gp tp t0v t1v (Z_to_bv 64 q) (Z_to_bv 64 pm) s1v
(Z_to_bv 64 PR) (Z_to_bv 64 ZR) a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 p) (Z_to_bv 64 p) xs4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) (Z_to_bv 64 q) (Z_to_bv 64 q) t6v)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 g10 g11 g12 g13 g14 f15v f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22de8) fc None m (seg_rom psegs)).
Proof.
intros c FB ZR PR zn0 zn1 zn2 pd0 pd1 pd2 xra xs4 me rest.
induction rest as [|x' rest IH]; intros done x q s1v t0v t1v a2v a3v a4v a5v a6v a7v f15v t6v g10 g11 g12 g13 g14 fc m
HN1 HN2 HD1 HD2 HN0 Ht0 Ht1 Ha7 Ha2 Ha3 Ha4 Ha5 Ha6 Hxs Hq Hs1 LEN SEP P0 P4 M0 M4 SZp SZm SPp SPm
FRM MI MU WM ZRc PRc DONE X PM; subst s1v t0v t1v a2v a3v a4v a5v a6v a7v f15v;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX |- *;
pose proof (rw_cells_bound _ _ _ _ PM) as BPM; rewrite cells_size_f32 in BPM; cbn [length] in BPM;
pose proof (rw_cells_bound _ _ _ _ ZRc) as BZ; rewrite cells_size_f32 in BZ; cbn [length] in BZ;
pose proof (rw_cells_bound _ _ _ _ PRc) as BP; rewrite cells_size_f32 in BP; cbn [length] in BP;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in X; rewrite !f32_cons, ?f32_nil in ZRc; rewrite !f32_cons, ?f32_nil in PRc;
rewrite !f32_cons, ?f32_nil in PM; cbn [fst snd] in PM.
-
hp_ck1. zstep. zstep. hp_ck1. hp_ck1. hp_ck1. hp_ck1. hp_ck1. hp_ck1.
do 5 zstep. rewrite HN1. do 3 zstep. rewrite fnmsub_fmadd_s, HD1. zstep.
hp_ck1. hp_ck1. do 4 zstep. rewrite HD2, HN2. do 3 zstep.
hp_ck1. zstep. zstep. hp_ck1. hp_ck1. zstep.
do 6 zstep. if_false_x.
unfold hp_exit. finish.
+ chunk_snoc DONE X. subst xs. rewrite hp_ys_app, f32_app. cbn [hp_ys]. rewrite f32_cons, f32_nil. exact DONE.
+ subst xs. rewrite hp_st_app. cbn [hp_st hp_next fst snd]. rewrite f32_cons, f32_cons, f32_nil. exact PM.
-
hp_ck1. zstep. zstep. hp_ck1. hp_ck1. hp_ck1. hp_ck1. hp_ck1. hp_ck1.
do 5 zstep. rewrite HN1. do 3 zstep. rewrite fnmsub_fmadd_s, HD1. zstep.
hp_ck1. hp_ck1. do 4 zstep. rewrite HD2, HN2. do 3 zstep.
hp_ck1. zstep. zstep. hp_ck1. hp_ck1. zstep.
do 6 zstep. if_true_x.
chunk_uncons X as X1. chunk_snoc DONE X1.
eapply (IH (done ++ [x]) x' (q + 4)%Z); try eassumption.
all: try reflexivity.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite length_app; cbn [length]; lia).
all: try (f_equal; lia).
all: try (rewrite hp_ys_app, f32_app; cbn [hp_ys]; rewrite f32_cons, f32_nil; exact DONE).
all: try (rewrite hp_st_app; cbn [hp_st hp_next fst snd]; rewrite f32_cons, f32_cons, f32_nil; exact PM).
Qed.

Ltac hp_cat H1 H2 :=
lazymatch type of H1 with rw_cells ?segs ?m ?A1 ?cs1 =>
lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
let H := fresh "CAT" in
assert (H : rw_cells segs m A1 (cs1 ++ cs2))
by (eapply rw_cells_join_at; [exact H1 | exact H2 |
rewrite ?cells_size_app, ?cells_size_f32; cbn [cells_size csize Nat.add Nat.mul length firstn skipn hp_zcoef_words hp_pcoef_words]; lia]);
clear H1 H2; rename H into H1
end end.

Ltac hp_after_copies FB FZ FP i zoff poff :=
zstep; zstep; if_true_x; zstep; zstep; if_false_z;
do 5 zstep; rewrite ?zb_lxor_ones by lia; zstep; if_false_z;
zstep; zstep; rewrite ?zb_lxor_ones by lia; zstep; if_false_z;
zstep; if_false_x; zstep; zstep;
destruct (rw_cells_f32_at _ _ _ (FB + zoff)%Z _ i FZ ltac:(cbn; lia) ltac:(unfold hp_zcoef_words; cbn; lia)) as [FZa FZm];
destruct (rw_cells_f32_at _ _ _ (FB + zoff + 12)%Z _ 3 FZm ltac:(cbn; lia) ltac:(unfold hp_zcoef_words; cbn; lia)) as [FZr FZb];
destruct (rw_cells_f32_at _ _ _ (FB + poff)%Z _ i FP ltac:(cbn; lia) ltac:(unfold hp_pcoef_words; cbn; lia)) as [FPa FPm];
destruct (rw_cells_f32_at _ _ _ (FB + poff + 12)%Z _ 3 FPm ltac:(cbn; lia) ltac:(unfold hp_pcoef_words; cbn; lia)) as [FPr FPb];
clear FZ FP FZm FPm;
unfold hp_zcoef_words, hp_pcoef_words in FZa, FZr, FZb, FPa, FPr, FPb; cbn [firstn skipn] in FZa, FZr, FZb, FPa, FPr, FPb;
rewrite !f32_cons, ?f32_nil in FZa; rewrite !f32_cons, ?f32_nil in FZr; rewrite !f32_cons, ?f32_nil in FZb;
rewrite !f32_cons, ?f32_nil in FPa; rewrite !f32_cons, ?f32_nil in FPr; rewrite !f32_cons, ?f32_nil in FPb;
do 20 zstep; cond_prep.

Ltac hp_loop_prem FZr FPr Exs :=
first [ exact FZr | exact FPr | apply munch_refl | apply wmono_refl | exact Exs
| (rewrite Exs; reflexivity) | (rewrite Exs; f_equal; cbn [length]; lia)
| (cbn [hp_ys]; rewrite f32_nil; apply rw_cells_nil; lia)
| (cbn [hp_st fst snd]; assumption)
| assumption
| (rewrite <- Exs; assumption)
| (cbn [length]; lia)
| (apply bv_eq; vm_compute; reflexivity) ].

Ltac hp_epilogue FB HFB F0 FZa FZr FZb FPa FPr FPb FS ST :=
do 8 zstep;
hp_cat F0 FZa; hp_cat F0 FZr; hp_cat F0 FZb; hp_cat F0 FPa; hp_cat F0 FPr; hp_cat F0 FPb; hp_cat F0 FS;
let ST2 := fresh "ST" in
pose proof (stk_release psegs _ _ FB _ ST F0 ltac:(lia)) as ST2;
lazymatch type of ST2 with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST2
by (rewrite ?cells_size_app, ?cells_size_f32; cbn [cells_size csize Nat.add Nat.mul length firstn skipn hp_zcoef_words hp_pcoef_words]; lia) end;
replace (FB + 176)%Z with (bv_unsigned sp) by lia; rewrite Z_to_bv_bv_unsigned;
unfold highpass_post; finish.

#[using="Type"] Lemma highpass_spec : forall (filtID : Z) t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 fc,
rw_cells psegs mi p (f32 xs) -> rw_cells psegs mi pm (f32 [m0; m1]) ->
(p + 4 * Z.of_nat (length xs) <= pm \/ pm + 8 <= p)%Z ->
mem_inv psegs mi -> frm0 fc ->
a2 = Z_to_bv 64 (Z.of_nat (length xs)) -> (1 <= Z.of_nat (length xs) < 2^31)%Z ->
a3 = Z_to_bv 64 filtID -> (filtID = 1 \/ filtID = 3)%Z ->
stk psegs mi lo (bv_unsigned sp) -> (lo + 176 <= bv_unsigned sp)%Z -> (0x6e000 <= lo)%Z ->
(p + 4 * Z.of_nat (length xs) <= lo \/ bv_unsigned sp <= p)%Z -> (pm + 8 <= lo \/ bv_unsigned sp <= pm)%Z ->
(0 < p)%Z -> (p mod 4 = 0)%Z -> (0 < pm)%Z -> (pm mod 4 = 0)%Z ->
evt psegs (highpass_post (hp_coefs filtID))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 (Z_to_bv 64 pm) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x22cfc) fc None mi (seg_rom psegs)).
Proof.
intros filtID t0 t1 t2 a2 a3 a5 a6 a7 t3 t4 t5 t6 fc X PM SEP MI FRM -> LEN -> FID ST LO GLO APX APM P0 P4 M0 M4.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ PM) as BPM; rewrite cells_size_f32 in BPM; cbn [length] in BPM.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
pose proof (munch_refl W mi) as MU. pose proof (wmono_refl psegs mi) as WM.
pose proof ST as (STa & STb & _).
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
carve_frame 176%nat ST.
zstep.
remember (bv_unsigned sp + -176)%Z as FB eqn:HFB.
apply (rw_cells_split_CB psegs _ _ [] 176 _ [] [8; 60; 60; 48]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
destruct (rw_cells_cons_at _ _ _ (FB + 8)%Z _ _ FR ltac:(cbn; lia)) as [F0 FR1]. clear FR.
destruct (rw_cells_cons_at _ _ _ (FB + 68)%Z _ _ FR1 ltac:(cbn; lia)) as [FZ FR2]. clear FR1.
destruct (rw_cells_cons_at _ _ _ (FB + 128)%Z _ _ FR2 ltac:(cbn; lia)) as [FP FS]. clear FR2.
do 6 zstep. do 10 zstep.
call memcpy_callZ; [ apply hp_pcoef_at; assumption | reflexivity | exact FP
| lia | lia | unfold A_hp_pcoef; lia | unfold A_hp_pcoef; lia | lia | unfold A_hp_pcoef; lia | assumption | ].
match goal with H : rw_cells _ _ (FB + 68)%Z [CB _ _] |- _ => apply rw_cells_f32_of_CB in H; rename H into FP end.
do 5 zstep.
call memcpy_callZ; [ apply hp_zcoef_at; assumption | reflexivity | exact FZ
| lia | lia | unfold A_hp_zcoef; lia | unfold A_hp_zcoef; lia | lia | unfold A_hp_zcoef; lia | assumption | ].
match goal with H : rw_cells _ _ (FB + 8)%Z [CB _ _] |- _ => apply rw_cells_f32_of_CB in H; rename H into FZ end.
destruct FID as [-> | ->].
- hp_after_copies FB FZ FP 3%nat 20%Z 80%Z.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (MM := mm) in *; clearbody MM end.
eapply evt_cut.
{ eapply (hp_loop (hp_coefs 1) FB (FB + 20) (FB + 80) (Z_to_bv 64 1064756954) (Z_to_bv 64 3220628119) (Z_to_bv 64 1064756954)
(Z_to_bv 64 1065353216) (Z_to_bv 64 3220611678) (Z_to_bv 64 1064190723) _ _ MM rest [] x p).
all: hp_loop_prem FZr FPr Exs. }
post_call psegs MM.
hp_epilogue FB HFB F0 FZa FZr FZb FPa FPr FPb FS ST.
- hp_after_copies FB FZ FP 9%nat 44%Z 104%Z.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (MM := mm) in *; clearbody MM end.
eapply evt_cut.
{ eapply (hp_loop (hp_coefs 3) FB (FB + 44) (FB + 104) (Z_to_bv 64 1065125885) (Z_to_bv 64 3220997050) (Z_to_bv 64 1065125885)
(Z_to_bv 64 1065353216) (Z_to_bv 64 3220992772) (Z_to_bv 64 1064905600) _ _ MM rest [] x p).
all: hp_loop_prem FZr FPr Exs. }
post_call psegs MM.
hp_epilogue FB HFB F0 FZa FZr FZb FPa FPr FPb FS ST.
Qed.

End S.
