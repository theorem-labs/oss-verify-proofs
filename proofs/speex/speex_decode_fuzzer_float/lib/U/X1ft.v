(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1nq X1mc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Lemma stk_store_ok : forall m lo hi a (j : nat),
stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi -> store_ok rsegs m (wa a) j = true.
Proof.
intros m lo hi a j (H0 & H1 & H) Hlo Hhi.
replace a with (lo + (a - lo)) by lia. apply (wr_at_store_ok rsegs m lo (hi - lo)); [| lia | lia].
split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (H (lo + i) ltac:(lia))).
Qed.
Ltac probe_store ST e :=
let HS := fresh "HS" in
lazymatch type of ST with stk ?segs ?m ?lo ?hi =>
unshelve epose proof (stk_store_ok m lo hi e 8%nat ST _ _) as HS; [lia | lia |] end;
step; change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)); store_done.

Lemma lts_ge_false a b : -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> b <= a ->
bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros Ha Hb H. unfold bv_lts. rewrite !zb_signed_small by lia. apply Z.ltb_ge. lia. Qed.

Definition qmf_synth_stmt_N (N : Z) : Prop :=
forall (Y G0 G1 lo : Z) (ys g0 g1 : list word) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m Y (f32 ys) -> length ys = Z.to_nat N ->
rw_cells rsegs m G0 (f32 g0) -> length g0 = 64%nat -> rw_cells rsegs m G1 (f32 g1) -> length g1 = 64%nat ->
rw_cells rsegs m (bv_unsigned sp) [C8 stk8] ->
stk rsegs m lo (bv_unsigned sp) -> lo + QMF_DEPTH <= bv_unsigned sp -> NB_GLOBALS_TOP <= lo -> bv_unsigned sp < 2^63 ->
NB_GLOBALS_TOP <= Y -> (G0 + 256 <= 0x10000 \/ NB_GLOBALS_TOP <= G0) -> (G1 + 256 <= 0x10000 \/ NB_GLOBALS_TOP <= G1) ->
apart Y (4 * N) lo (bv_unsigned sp - lo) -> apart G0 256 lo (bv_unsigned sp - lo) -> apart G1 256 lo (bv_unsigned sp - lo) ->
apart Y (4 * N) G0 256 -> apart Y (4 * N) G1 256 -> apart G0 256 G1 256 ->
a0 = Z_to_bv 64 Y -> a1 = Z_to_bv 64 (Y + 2 * N) -> a2 = Z_to_bv 64 A_h0 -> a3 = Z_to_bv 64 Y ->
a4 = Z_to_bv 64 N -> a5 = Z_to_bv 64 QMF_ORDER -> a6 = Z_to_bv 64 G0 -> a7 = Z_to_bv 64 G1 ->
mem_inv rsegs m -> frm0 fc ->
Y mod 4 = 0 -> 0 < G0 -> G0 mod 4 = 0 -> 0 < G1 -> G1 mod 4 = 0 ->
evt rsegs (qmf_synth_post Y N G0 G1 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_synth) fc None m (seg_rom rsegs)).

Lemma qmf_synth_of_N : qmf_synth_stmt_N 320 -> qmf_synth_stmt_N 640 -> qmf_synth_stmt.
Proof.
intros H320 H640. unfold qmf_synth_stmt. intros until m. intros X LX HN. destruct HN as [-> | ->]; [eapply H320| eapply H640]; eassumption.
Qed.

Definition h0_bytes : list byte := match image_bytes rsegs 78316 256 with Some bs => bs | None => [] end.
Lemma h0_ro : forall m, mem_inv rsegs m -> u8ro rsegs m 78316 h0_bytes /\ length h0_bytes = 256%nat.
Proof.
intros m MI. assert (L : length h0_bytes = 256%nat) by (vm_compute; reflexivity). split; [|exact L].
unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m 78316 _ (ro_cells_image rsegs m 78316 h0_bytes MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite L; lia))) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

Section Loops.
Context {RCEIL : RunCeiling}.
Variables (ra gp tp s0 : word).

#[using="Type"] Lemma qmf_L1 : forall (k : nat) (i N2 Y X1 : Z) (nx : nat) (ys xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 t3 t4 t5 t6 a0 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = N2 - i -> 0 <= i < N2 -> (N2 = 160 \/ N2 = 320) -> N2 <= Z.of_nat (length ys) -> Z.of_nat nx = N2 + 32 ->
t1 = Z_to_bv 64 (Z.lxor X1 18446744073709551615) -> t2 = Z_to_bv 64 (Z.of_nat nx) -> t4 = Z_to_bv 64 N2 ->
t5 = Z_to_bv 64 (N2 - 1) -> t6 = Z_to_bv 64 1 -> a0 = Z_to_bv 64 Y ->
u32arr rsegs m1 Y ys -> u32arr rsegs m1 X1 xs -> length xs = nx ->
apart Y (4 * Z.of_nat (length ys)) X1 (4 * Z.of_nat nx) -> 0 < Y -> Y mod 4 = 0 -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 ->
munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a2' a4' s1' s2' s3' t3' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1' a0 a1 a2' a3 a4' a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x24210) fc1 None m2 (seg_rom rsegs)
/\ munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X1 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 (Z_to_bv 64 (X1 + 4 * i)) a0 a1 (Z_to_bv 64 (4 * i)) a3 (Z_to_bv 64 i) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x241b0) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i N2 Y X1 nx ys xs W m0 m1 sp' t0 t1 t2 t3 t4 t5 t6 a0 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F1 fc1
Hk Hi HN Hys Hnx E1 E2 E4 E5 E6 E0 YA XA Lxs AP Ypos YAL Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ XA) as BX0.
assert (LX : Z.lxor X1 18446744073709551615 = 18446744073709551615 - X1) by (apply zb_lxor_ones; lia).
rewrite LX in E1. subst t1 t2 t4 t5 t6 a0.
pose proof (u32arr_bound _ _ _ _ YA) as BY. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof AP as AP'. unfold apart in AP'.
bato 0x241f8.
pose proof (u32arr_read_nth rsegs m1 Y ys (N2 - 1 - i) (wa (Y + (N2 - 1 + - i + 0) * 4)) YA ltac:(lia) ltac:(f_equal; lia)) as RD.
zstep. clear RD. zstep.
pose proof (u32arr_store_ok rsegs m1 X1 xs i _ XA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X1 xs i v XA ltac:(lia)) as XA' end.
clear XA. store_done. try clear SOK.
zstep. zstep. zstep.
rewrite (swrap32_small (i + 1)) by lia.
if_cases K; zify_cond K.
- replace (X1 + 4 * i + 4) with (X1 + 4 * (i + 1)) by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
eapply (IH (i + 1) N2 Y X1 nx ys _ W m0); try eassumption; try reflexivity; try lia.
all: try (rewrite LX; reflexivity).
rewrite upd_length. exact Lxs.
- apply evt_done. sf_eexists 9%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.

#[using="Type"] Lemma qmf_L2 : forall (k : nat) (i N2 G X1 : Z) (nx : nat) (gs xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 t3 t4 t5 a0 a1 a2 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 32 - i -> 0 <= i < 32 -> (N2 = 160 \/ N2 = 320) -> Z.of_nat nx = N2 + 32 -> length gs = 64%nat ->
t0 = Z_to_bv 64 X1 -> t1 = Z_to_bv 64 (Z.lxor X1 18446744073709551615) -> t4 = Z_to_bv 64 N2 -> a6 = Z_to_bv 64 G ->
u32arr rsegs m1 G gs -> u32arr rsegs m1 X1 xs -> length xs = nx -> rw_cells rsegs m1 (bv_unsigned s0 + -112) [C8 (Z_to_bv 64 0)] ->
apart G 256 X1 (4 * Z.of_nat nx) -> apart (bv_unsigned s0 + -112) 8 X1 (4 * Z.of_nat nx) ->
0 < G -> G mod 4 = 0 -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 ->
munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a0' a4' s1' s2' s3' t3' t6' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1' a0' a1 a2 a3 a4' a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6')
F2 (Z_to_bv 64 0x24298) fc1 None m2 (seg_rom rsegs)
/\ munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X1 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 (Z_to_bv 64 (32 - i)) a0 a1 a2 a3 (Z_to_bv 64 i) a5 a6 a7 (Z_to_bv 64 (32 - i)) (Z_to_bv 64 (G + 4 + 8 * i))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 (Z_to_bv 64 (G + 4 + 8 * i)))
F1 (Z_to_bv 64 0x24244) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i N2 G X1 nx gs xs W m0 m1 sp' t0 t1 t2 t3 t4 t5 a0 a1 a2 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 F1 fc1
Hk Hi HN Hnx Lgs E0 E1 E4 E6 GA XA Lxs SC AP APS Gpos GAL Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ XA) as BX0.
assert (LX : Z.lxor X1 18446744073709551615 = 18446744073709551615 - X1) by (apply zb_lxor_ones; lia).
rewrite LX in E1. subst t0 t1 t4 a6.
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof (rw_cells_bound _ _ _ _ SC) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof AP as AP'. unfold apart in AP'. pose proof APS as APS'. unfold apart in APS'.
bato 0x24274.
pose proof (u32arr_read_nth rsegs m1 G gs (2 * i + 1) (wa (G + 4 + 8 * i)) GA ltac:(lia) ltac:(f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep. zstep. zstep.
rewrite (Z.mod_small (N2 + i + 0) 18446744073709551616) by lia.
pose proof (u32arr_store_ok rsegs m1 X1 xs (N2 + i) (wa (X1 + (N2 + i + 0) * 4)) XA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X1 xs (N2 + i) v XA ltac:(lia)) as XA' end.
replace (X1 + 4 * (N2 + i)) with (X1 + (N2 + i + 0) * 4) in XA' by lia.
clear XA. store_done. try clear SOK.
zstep. zstep.
rewrite (swrap32_small (i + 1)) by lia.
if_cases K; zify_cond K.
- replace (32 - i + -1) with (32 - (i + 1)) by lia. replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * (i + 1)) by lia.
eapply (IH (i + 1) N2 G X1 nx gs _ W m0); try eassumption; try reflexivity; try lia.
all: try (rewrite LX; reflexivity).
rewrite upd_length. exact Lxs.
- apply evt_done. sf_eexists 10%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.

#[using="Type"] Lemma qmf_L3 : forall (k : nat) (i N2 Y X2 : Z) (nx : nat) (ys xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = N2 - i -> 0 <= i < N2 -> (N2 = 160 \/ N2 = 320) -> 2 * N2 <= Z.of_nat (length ys) -> Z.of_nat nx = N2 + 32 ->
t2 = Z_to_bv 64 (Z.of_nat nx) -> t4 = Z_to_bv 64 N2 -> t5 = Z_to_bv 64 (N2 - 1) -> t6 = Z_to_bv 64 (Z.lxor X2 18446744073709551615) ->
a1 = Z_to_bv 64 (Y + 4 * N2) -> s2 = Z_to_bv 64 1 ->
u32arr rsegs m1 Y ys -> u32arr rsegs m1 X2 xs -> length xs = nx ->
apart Y (4 * Z.of_nat (length ys)) X2 (4 * Z.of_nat nx) -> 0 < Y -> Y mod 4 = 0 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a0' a4' s1' s3' s5' t3' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1' a0' a1 a2 a3 a4' a5 a6 a7 s2 s3' s4 s5' s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x24310) fc1 None m2 (seg_rom rsegs)
/\ munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X2 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 (Z_to_bv 64 i) a0 a1 a2 a3 (Z_to_bv 64 (4 * i)) a5 a6 a7 s2 (Z_to_bv 64 (X2 + 4 * i)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x242b0) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i N2 Y X2 nx ys xs W m0 m1 sp' t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 F1 fc1
Hk Hi HN Hys Hnx E2 E4 E5 E6 E11 Es2 YA XA Lxs AP Ypos YAL Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ XA) as BX0.
assert (LX : Z.lxor X2 18446744073709551615 = 18446744073709551615 - X2) by (apply zb_lxor_ones; lia).
rewrite LX in E6. subst t2 t4 t5 t6 a1 s2.
pose proof (u32arr_bound _ _ _ _ YA) as BY. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof AP as AP'. unfold apart in AP'.
bato 0x242f8.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?ad) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
pose proof (u32arr_read_nth rsegs m1 Y ys (2 * N2 - 1 - i) (wa ad) YA ltac:(lia) ltac:(f_equal; lia)) as RD end.
zstep. clear RD. zstep.
pose proof (u32arr_store_ok rsegs m1 X2 xs i _ XA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X2 xs i v XA ltac:(lia)) as XA' end.
clear XA. store_done. try clear SOK.
zstep. zstep. zstep.
rewrite (swrap32_small (i + 1)) by lia.
if_cases K; zify_cond K.
- replace (X2 + 4 * i + 4) with (X2 + 4 * (i + 1)) by lia. replace (4 * i + 4) with (4 * (i + 1)) by lia.
eapply (IH (i + 1) N2 Y X2 nx ys _ W m0); try eassumption; try reflexivity; try lia.
all: try (rewrite LX; reflexivity).
rewrite upd_length. exact Lxs.
- apply evt_done. sf_eexists 9%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.

#[using="Type"] Lemma qmf_L4 : forall (k : nat) (i N2 G X2 : Z) (nx : nat) (gs xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 t3 t4 t5 t6 a0 a1 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 32 - i -> 0 <= i < 32 -> (N2 = 160 \/ N2 = 320) -> Z.of_nat nx = N2 + 32 -> length gs = 64%nat ->
t4 = Z_to_bv 64 N2 -> t6 = Z_to_bv 64 (Z.lxor X2 18446744073709551615) -> a5 = Z_to_bv 64 X2 -> a7 = Z_to_bv 64 G ->
u32arr rsegs m1 G gs -> u32arr rsegs m1 X2 xs -> length xs = nx -> rw_cells rsegs m1 (bv_unsigned s0 + -120) [C8 (Z_to_bv 64 0)] ->
apart G 256 X2 (4 * Z.of_nat nx) -> apart (bv_unsigned s0 + -120) 8 X2 (4 * Z.of_nat nx) ->
0 < G -> G mod 4 = 0 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a0' a2' a4' s1' s2' s3' t3' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1' a0' a1 a2' a3 a4' a5 a6 a7 s2' s3' s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x24394) fc1 None m2 (seg_rom rsegs)
/\ munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X2 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 (Z_to_bv 64 (32 - i)) a0 a1 (Z_to_bv 64 (G + 4 + 8 * i)) a3 (Z_to_bv 64 i) a5 a6 a7 (Z_to_bv 64 (32 - i)) (Z_to_bv 64 (G + 4 + 8 * i))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x24340) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i N2 G X2 nx gs xs W m0 m1 sp' t0 t1 t2 t3 t4 t5 t6 a0 a1 a3 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 F1 fc1
Hk Hi HN Hnx Lgs E4 E6 E5 E7 GA XA Lxs SC AP APS Gpos GAL Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ XA) as BX0.
assert (LX : Z.lxor X2 18446744073709551615 = 18446744073709551615 - X2) by (apply zb_lxor_ones; lia).
rewrite LX in E6. subst t4 t6 a5 a7.
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof (rw_cells_bound _ _ _ _ SC) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof AP as AP'. unfold apart in AP'. pose proof APS as APS'. unfold apart in APS'.
bato 0x24370.
pose proof (u32arr_read_nth rsegs m1 G gs (2 * i + 1) (wa (G + 4 + 8 * i)) GA ltac:(lia) ltac:(f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep. zstep. zstep.
rewrite (Z.mod_small (N2 + i + 0) 18446744073709551616) by lia.
pose proof (u32arr_store_ok rsegs m1 X2 xs (N2 + i) (wa (X2 + (N2 + i + 0) * 4)) XA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X2 xs (N2 + i) v XA ltac:(lia)) as XA' end.
replace (X2 + 4 * (N2 + i)) with (X2 + (N2 + i + 0) * 4) in XA' by lia.
clear XA. store_done. try clear SOK.
zstep. zstep.
rewrite (swrap32_small (i + 1)) by lia.
if_cases K; zify_cond K.
- replace (32 - i + -1) with (32 - (i + 1)) by lia. replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * (i + 1)) by lia.
eapply (IH (i + 1) N2 G X2 nx gs _ W m0); try eassumption; try reflexivity; try lia.
all: try (rewrite LX; reflexivity).
rewrite upd_length. exact Lxs.
- apply evt_done. sf_eexists 10%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.
End Loops.

Lemma u8ro_read4 : forall m A bs (k : Z) a,
u8ro rsegs m A bs -> (0 <= k)%Z -> (Z.to_nat k + 4 <= length bs)%nat -> a = wa (A + k) ->
ov_read_bytes rsegs m a 4 = Some (firstn 4 (skipn (Z.to_nat k) bs)).
Proof.
intros m A bs k a HB Hk Hlen ->. unfold u8ro in HB.
rewrite <- (bytes_at_ov_read rsegs m A bs (Z.to_nat k) 4 HB) by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Ltac reg_s1 := lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ (Z_to_bv 64 ?ad) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => ad end.
Ltac reg_a1 := lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?ad) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => ad end.
Ltac reg_a2 := lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?ad) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => ad end.
Ltac reg_a4 := lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?ad) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => ad end.
Ltac rd32 ad X xs idx XA :=
let RD := fresh "RD" in
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u32arr_read_nth rsegs mc X xs idx (wa ad) XA ltac:(lia) ltac:(f_equal; lia)) as RD end.
Lemma land_m64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.
Ltac qnorm := repeat match goal with |- context [Z.land ?x 18446744073709551615] => rewrite (land_m64 x) by lia end.
Ltac qato p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then first [ ub_dec | (bnorm; qnorm; bnorm; ub_dec) ] else ub_step));
first [ ub_at_pc p | ub_show_pc_fail p ].

Section Inner.
Context {RCEIL : RunCeiling}.
Variables (sp' gp tp t0 t1 t2 s0 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 t4 t5 t6 : word).

#[using="Type"] Lemma qmf_inner : forall (k : nat) (jj i N2 X1 X2 : Z) (nx : nat) (xs1 xs2 : list word) (hb : list byte) (m1 : mem)
(a1 a4 s1 t3 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 16 - jj -> 0 <= jj < 16 -> 0 <= i -> i + 2 <= N2 -> (N2 = 160 \/ N2 = 320) -> Z.of_nat nx = N2 + 32 ->
t0 = Z_to_bv 64 X1 -> t1 = Z_to_bv 64 (Z.lxor X1 18446744073709551615) -> t2 = Z_to_bv 64 (Z.of_nat nx) -> t4 = Z_to_bv 64 N2 ->
t5 = Z_to_bv 64 (N2 - 1) -> t6 = Z_to_bv 64 (Z.lxor X2 18446744073709551615) -> a0 = Z_to_bv 64 i -> a5 = Z_to_bv 64 X2 ->
s3 = Z_to_bv 64 1 -> s4 = Z_to_bv 64 78316 -> s5 = Z_to_bv 64 (Z.lxor 78316 18446744073709551615) -> s8 = Z_to_bv 64 1 -> s9 = Z_to_bv 64 32 ->
u32arr rsegs m1 X1 xs1 -> length xs1 = nx -> u32arr rsegs m1 X2 xs2 -> length xs2 = nx -> u8ro rsegs m1 78316 hb -> length hb = 256%nat ->
0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (ra' a1' a2' a4' s1' s7' s10' s11' t3' : word) (F2 : bvmap 5 word) (fc2 : bv 32),
ms' = MS (mkR ra' sp' gp tp t0 t1 t2 s0 s1' a0 a1' a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7' s8 s9 s10' s11' t3' t4 t5 t6)
F2 (Z_to_bv 64 0x24544) fc2 None m1 (seg_rom rsegs) /\ frm0 fc2)
(MS (mkR (Z_to_bv 64 (12 + 16 * jj)) sp' gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (78316 + 16 * jj)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
(Z_to_bv 64 (78316 + 8 + 16 * jj)) s8 s9 (Z_to_bv 64 (2 * jj)) (Z_to_bv 64 (2 * jj)) t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2443c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros jj i N2 X1 X2 nx xs1 xs2 hb m1 a1 a4 s1 t3 F1 fc1
Hk Hjj Hi HiN HN Hnx E0 E1 E2 E4 E5 E6 Ea0 Ea5 Es3 Es4 Es5 Es8 Es9 X1A L1 X2A L2 HB LHB X1pos X1hi X2pos X2hi FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ X1A) as B1. pose proof (u32arr_bound _ _ _ _ X2A) as B2. rewrite L1 in B1. rewrite L2 in B2.
pose proof (bytes_at_bound _ _ _ _ HB) as BH. rewrite LHB in BH.
assert (LX1 : Z.lxor X1 18446744073709551615 = 18446744073709551615 - X1) by (apply zb_lxor_ones; lia).
assert (LX2 : Z.lxor X2 18446744073709551615 = 18446744073709551615 - X2) by (apply zb_lxor_ones; lia).
rewrite LX1 in E1. rewrite LX2 in E6. subst t0 t1 t2 t4 t5 t6 a0 a5 s3 s4 s5 s8 s9.
pose proof (u8ro_read4 m1 78316 hb (16 * jj) (wa (78316 + 8 + 16 * jj + -8)) HB ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RA0.
pose proof (u8ro_read4 m1 78316 hb (16 * jj + 4) (wa (78316 + 8 + 16 * jj + -4)) HB ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RA1.
pose proof (u8ro_read4 m1 78316 hb (16 * jj + 8) (wa (78316 + 8 + 16 * jj)) HB ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RA2.
pose proof (u8ro_read4 m1 78316 hb (16 * jj + 12) (wa (78316 + 8 + 16 * jj + 4)) HB ltac:(lia) ltac:(lia) ltac:(f_equal; lia)) as RA3.
qato 0x244e4.
pose proof (u32arr_read_nth rsegs m1 X1 xs1 (N2 - 1 + 2 * jj - i) (wa (X1 + (N2 - 1 + 2 * jj + 0 + - i) * 4)) X1A ltac:(lia) ltac:(f_equal; lia)) as RD1.
pose proof (u32arr_read_nth rsegs m1 X2 xs2 (N2 - 1 + 2 * jj - i) (wa (X2 + (N2 - 1 + 2 * jj + 0 + - i) * 4)) X2A ltac:(lia) ltac:(f_equal; lia)) as RD2.
pose proof (u32arr_read_nth rsegs m1 X1 xs1 (N2 + 2 * jj - i) (wa (X1 + (N2 + 2 * jj + 0 + - i) * 4)) X1A ltac:(lia) ltac:(f_equal; lia)) as RD3.
pose proof (u32arr_read_nth rsegs m1 X2 xs2 (N2 + 2 * jj - i) (wa (X2 + (N2 + 2 * jj + 0 + - i) * 4)) X2A ltac:(lia) ltac:(f_equal; lia)) as RD4.
qato 0x24540.
clear RD1 RD2 RD3 RD4 RA0 RA1 RA2 RA3.
zstep.
if_cases K; zify_cond K; rewrite zb_signed_small in K by lia.
- rewrite (swrap32_small (2 * jj + 2)) by lia.
replace (12 + 16 * jj + 16) with (12 + 16 * (jj + 1)) by lia.
replace (78316 + 16 * jj + 16) with (78316 + 16 * (jj + 1)) by lia.
replace (78324 + 16 * jj + 16) with (78316 + 8 + 16 * (jj + 1)) by lia.
replace (2 * jj + 2) with (2 * (jj + 1)) by lia.
eapply (IH (jj + 1) i N2 X1 X2 nx xs1 xs2 hb m1); try eassumption; try reflexivity; try lia.
all: try (rewrite ?LX1, ?LX2; reflexivity).
- apply evt_done. sf_eexists 11%nat. split; [ms_eq| assumption].
Qed.
End Inner.

Ltac ystore Y idx ad :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with YA : u32arr rsegs mc Y ?l |- _ =>
let SOK := fresh "SOK" in let YA' := fresh "YA" in
pose proof (u32arr_store_ok rsegs mc Y l idx (wa ad) YA ltac:(repeat rewrite upd_length; lia) ltac:(f_equal; lia)) as SOK;
zstep;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs mc Y l idx v YA ltac:(repeat rewrite upd_length; lia)) as YA' end;
replace (Y + 4 * idx) with ad in YA' by lia;
clear YA; store_done; try clear SOK
end end.
Ltac onorm := bnorm; qnorm; bnorm; change (2 ^ 1) with 2 in *; change (2 ^ 3) with 8 in *.
Lemma bytes_at_det : forall m a bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) HL. apply nth_error_ext. intros n.
destruct (Nat.lt_ge_cases n (length bs1)) as [Hn|Hn].
- rewrite <- (H1 n Hn), <- (H2 n ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs1 n) Hn), (proj2 (nth_error_None bs2 n) ltac:(lia)). reflexivity.
Qed.

Section Outer.
Context {RCEIL : RunCeiling}.
Variables (gp tp s0 a6 a7 : word).

#[using="Type"] Lemma qmf_outer : forall (k : nat) (i ii N2 X1 X2 Y : Z) (nx : nat) (xs1 xs2 ys : list word) (hb : list byte) (W : list (Z * Z)) (m0 m1 : mem)
(ra sp' t0 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k * 2 = N2 - i -> 0 <= i -> i + 2 <= N2 -> i = 2 * ii -> (N2 = 160 \/ N2 = 320) -> Z.of_nat nx = N2 + 32 ->
t0 = Z_to_bv 64 X1 -> t1 = Z_to_bv 64 (Z.lxor X1 18446744073709551615) -> t2 = Z_to_bv 64 (Z.of_nat nx) -> t4 = Z_to_bv 64 N2 ->
t5 = Z_to_bv 64 (N2 - 1) -> t6 = Z_to_bv 64 (Z.lxor X2 18446744073709551615) -> a3 = Z_to_bv 64 Y -> a5 = Z_to_bv 64 X2 ->
s2 = Z_to_bv 64 (N2 - 2) -> s3 = Z_to_bv 64 1 -> s4 = Z_to_bv 64 78316 -> s5 = Z_to_bv 64 (Z.lxor 78316 18446744073709551615) ->
s6 = Z_to_bv 64 (Z.lxor Y 18446744073709551615) -> s8 = Z_to_bv 64 1 -> s9 = Z_to_bv 64 32 ->
u32arr rsegs m1 X1 xs1 -> length xs1 = nx -> u32arr rsegs m1 X2 xs2 -> length xs2 = nx ->
u32arr rsegs m1 Y ys -> Z.of_nat (length ys) = 2 * N2 -> u8ro rsegs m1 78316 hb -> length hb = 256%nat ->
rw_cells rsegs m1 (bv_unsigned s0 + -152) [C8 (Z_to_bv 64 (78316 + 8))] -> rw_cells rsegs m1 (bv_unsigned s0 + -144) [C8 (Z_to_bv 64 1)] ->
rw_cells rsegs m1 (bv_unsigned s0 + -136) [C8 (Z_to_bv 64 1)] ->
apart Y (8 * N2) X1 (4 * Z.of_nat nx) -> apart Y (8 * N2) X2 (4 * Z.of_nat nx) -> apart Y (8 * N2) (bv_unsigned s0 + -152) 24 ->
0 < Y -> Y mod 4 = 0 -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((Y, Y + 8 * N2) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (ra' t3' s1' s7' s10' s11' a0' a1' a2' a4' : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (ys' : list word),
ms' = MS (mkR ra' sp' gp tp t0 t1 t2 s0 s1' a0' a1' a2' a3 a4' a5 a6 a7 s2 s3 s4 s5 s6 s7' s8 s9 s10' s11' t3' t4 t5 t6)
F2 (Z_to_bv 64 0x245d0) fc2 None m2 (seg_rom rsegs)
/\ munch ((Y, Y + 8 * N2) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 Y ys' /\ Z.of_nat (length ys') = 2 * N2)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x243dc) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ii N2 X1 X2 Y nx xs1 xs2 ys hb W m0 m1 ra sp' t0 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
a1 a2 a3 a4 a5 F1 fc1 Hk Hi HiN Hii HN Hnx E0 E1 E2 E4 E5 E6 Ea3 Ea5 Es2 Es3 Es4 Es5 Es6 Es8 Es9 X1A L1 X2A L2 YA LY HB LHB
C152 C144 C136 AP1 AP2 AP3 Ypos YAL X1pos X1hi X2pos X2hi MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ X1A) as B1. pose proof (u32arr_bound _ _ _ _ X2A) as B2. rewrite L1 in B1. rewrite L2 in B2.
pose proof (u32arr_bound _ _ _ _ YA) as BY. rewrite LY in BY.
pose proof (bytes_at_bound _ _ _ _ HB) as BH. rewrite LHB in BH.
destruct (h0_ro m1 MI) as [H0R H0L].
assert (Ehb : hb = h0_bytes) by (eapply bytes_at_det; [exact HB | exact H0R | rewrite LHB, H0L; reflexivity]).
subst hb. clear H0R.
pose proof (rw_cells_bound _ _ _ _ C152) as BC. cbn [cells_size csize Nat.add] in BC.
pose proof AP1 as AP1'. pose proof AP2 as AP2'. pose proof AP3 as AP3'. unfold apart in AP1', AP2', AP3'.
assert (LX1 : Z.lxor X1 18446744073709551615 = 18446744073709551615 - X1) by (apply zb_lxor_ones; lia).
assert (LX2 : Z.lxor X2 18446744073709551615 = 18446744073709551615 - X2) by (apply zb_lxor_ones; lia).
assert (LXY : Z.lxor Y 18446744073709551615 = 18446744073709551615 - Y) by (apply zb_lxor_ones; lia).
rewrite LX1 in E1. rewrite LX2 in E6. rewrite LXY in Es6.
subst t0 t1 t2 t4 t5 t6 a3 a5 s2 s3 s4 s5 s6 s8 s9.
pose proof (u32arr_read_nth rsegs m1 X1 xs1 (N2 - 2 - i) (wa (X1 + (N2 - 2 + - i) * 4)) X1A ltac:(lia) ltac:(f_equal; lia)) as RD1.
pose proof (u32arr_read_nth rsegs m1 X2 xs2 (N2 - 2 - i) (wa (X2 + (N2 - 2 + - i) * 4)) X2A ltac:(lia) ltac:(f_equal; lia)) as RD2.
qato 0x2443c.
clear RD1 RD2.
eapply evt_cut.
{ eapply qmf_inner with (k := 16%nat) (jj := 0) (i := i) (N2 := N2) (X1 := X1) (X2 := X2) (nx := nx) (xs1 := xs1) (xs2 := xs2) (hb := h0_bytes);
try eassumption; try reflexivity; try lia. all: try (rewrite ?LX1, ?LX2; reflexivity). }
cbv beta. intros ms' (ra' & a1' & a2' & a4' & s1' & s7' & s10' & s11' & t3' & F2 & fc2 & -> & FRM2). clear FRM.
qato 0x24580.
onorm. ystore Y (2 * i) (Y + i * 8).
qato 0x24598. onorm. ystore Y (2 * i + 1) (Y + (i * 2 + 1) * 4).
qato 0x245b0. onorm. ystore Y (2 * i + 2) (Y + (i * 2 + 2) * 4).
qato 0x245c8. onorm. ystore Y (2 * i + 3) (Y + (i * 2 + 3) * 4).
zstep.
if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
- lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with YA' : u32arr rsegs mc Y ?l |- _ =>
eapply (IH (i + 2) (ii + 1) N2 X1 X2 Y nx xs1 xs2 l h0_bytes W m0 mc) end end; try eassumption; try reflexivity; try lia.
all: try (rewrite ?LX1, ?LX2, ?LXY; reflexivity).
all: try (repeat rewrite upd_length; first [exact LY | lia]).
all: try (eapply proj1, h0_ro; eassumption).
- apply evt_done. sf_eexists 14%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
repeat rewrite upd_length. exact LY.
Qed.
End Outer.

Section CopyBack.
Context {RCEIL : RunCeiling}.
Variables (ra gp tp s0 s10 s11 : word).

#[using="Type"] Lemma qmf_L5 : forall (k : nat) (i X1 G : Z) (nx : nat) (xs gs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 t4 t5 t6 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 32 - i -> 0 <= i < 32 -> (32 <= nx)%nat ->
t0 = Z_to_bv 64 X1 -> t1 = Z_to_bv 64 (Z.lxor X1 18446744073709551615) -> t2 = Z_to_bv 64 128 -> a6 = Z_to_bv 64 G ->
u32arr rsegs m1 X1 xs -> length xs = nx -> u32arr rsegs m1 G gs -> length gs = 64%nat ->
rw_cells rsegs m1 (bv_unsigned s0 + -128) [C8 (Z_to_bv 64 (4 * Z.of_nat nx))] -> rw_cells rsegs m1 (bv_unsigned s0 + -112) [C8 (Z_to_bv 64 0)] ->
apart G 256 X1 (4 * Z.of_nat nx) -> apart G 256 (bv_unsigned s0 + -128) 8 -> apart G 256 (bv_unsigned s0 + -112) 8 ->
0 < G -> G mod 4 = 0 -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 ->
munch ((G, G + 256) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a0' a3' a4' t3' : word) (F2 : bvmap 5 word) (m2 : mem) (gs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x24624) fc1 None m2 (seg_rom rsegs)
/\ munch ((G, G + 256) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 G gs' /\ length gs' = 64%nat)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (G + 4 + 8 * i)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (G + 4 + 8 * i)) t4 t5 t6)
F1 (Z_to_bv 64 0x245e8) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i X1 G nx xs gs W m0 m1 sp' t0 t1 t2 t4 t5 t6 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 F1 fc1
Hk Hi Hnx E0 E1 E2 E6 XA Lxs GA Lgs SC SF AP APS APF Gpos GAL Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
assert (LX : Z.lxor X1 18446744073709551615 = 18446744073709551615 - X1) by (apply zb_lxor_ones; lia).
rewrite LX in E1. subst t0 t1 t2 a6.
pose proof (rw_cells_bound _ _ _ _ SC) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (rw_cells_bound _ _ _ _ SF) as BF. cbn [cells_size csize Nat.add] in BF.
pose proof AP as AP'. unfold apart in AP'. pose proof APS as APS'. unfold apart in APS'. pose proof APF as APF'. unfold apart in APF'.
bato 0x2460c.
pose proof (u32arr_read_nth rsegs m1 X1 xs i (wa (X1 + 4 * i)) XA ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep. zstep.
pose proof (u32arr_store_ok rsegs m1 G gs (2 * i + 1) (wa (G + 4 + 8 * i)) GA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 G gs (2 * i + 1) v GA ltac:(lia)) as GA' end.
replace (G + 4 * (2 * i + 1)) with (G + 4 + 8 * i) in GA' by lia.
clear GA. store_done. try clear SOK.
zstep. zstep.
if_cases K; zify_cond K.
- replace (4 * i + 4) with (4 * (i + 1)) by lia. replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * (i + 1)) by lia.
eapply (IH (i + 1) X1 G nx xs _ W m0); try eassumption; try reflexivity; try lia.
all: try (rewrite LX; reflexivity).
rewrite upd_length. exact Lgs.
- apply evt_done. sf_eexists 7%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lgs.
Qed.

#[using="Type"] Lemma qmf_L6 : forall (k : nat) (i X2 G : Z) (nx : nat) (xs gs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 t3 t4 t5 t6 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 32 - i -> 0 <= i < 32 -> (32 <= nx)%nat ->
t2 = Z_to_bv 64 128 -> t6 = Z_to_bv 64 (Z.lxor X2 18446744073709551615) -> a5 = Z_to_bv 64 X2 -> a7 = Z_to_bv 64 G ->
u32arr rsegs m1 X2 xs -> length xs = nx -> u32arr rsegs m1 G gs -> length gs = 64%nat ->
rw_cells rsegs m1 (bv_unsigned s0 + -128) [C8 (Z_to_bv 64 (4 * Z.of_nat nx))] -> rw_cells rsegs m1 (bv_unsigned s0 + -120) [C8 (Z_to_bv 64 0)] ->
apart G 256 X2 (4 * Z.of_nat nx) -> apart G 256 (bv_unsigned s0 + -128) 8 -> apart G 256 (bv_unsigned s0 + -120) 8 ->
0 < G -> G mod 4 = 0 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((G, G + 256) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a0' a1' a2' a3' : word) (F2 : bvmap 5 word) (m2 : mem) (gs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x24668) fc1 None m2 (seg_rom rsegs)
/\ munch ((G, G + 256) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 G gs' /\ length gs' = 64%nat)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (4 * i)) a1 (Z_to_bv 64 (G + 4 + 8 * i)) (Z_to_bv 64 (G + 4 + 8 * i)) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2462c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i X2 G nx xs gs W m0 m1 sp' t0 t1 t2 t3 t4 t5 t6 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 F1 fc1
Hk Hi Hnx E2 E6 E5 E7 XA Lxs GA Lgs SC SF AP APS APF Gpos GAL Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
assert (LX : Z.lxor X2 18446744073709551615 = 18446744073709551615 - X2) by (apply zb_lxor_ones; lia).
rewrite LX in E6. subst t2 t6 a5 a7.
pose proof (rw_cells_bound _ _ _ _ SC) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (rw_cells_bound _ _ _ _ SF) as BF. cbn [cells_size csize Nat.add] in BF.
pose proof AP as AP'. unfold apart in AP'. pose proof APS as APS'. unfold apart in APS'. pose proof APF as APF'. unfold apart in APF'.
bato 0x24650.
pose proof (u32arr_read_nth rsegs m1 X2 xs i (wa (X2 + 4 * i)) XA ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep. zstep.
pose proof (u32arr_store_ok rsegs m1 G gs (2 * i + 1) (wa (G + 4 + 8 * i)) GA ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 G gs (2 * i + 1) v GA ltac:(lia)) as GA' end.
replace (G + 4 * (2 * i + 1)) with (G + 4 + 8 * i) in GA' by lia.
clear GA. store_done. try clear SOK.
zstep. zstep.
if_cases K; zify_cond K.
- replace (4 * i + 4) with (4 * (i + 1)) by lia. replace (G + 4 + 8 * i + 8) with (G + 4 + 8 * (i + 1)) by lia.
eapply (IH (i + 1) X2 G nx xs _ W m0); try eassumption; try reflexivity; try lia.
all: try (rewrite LX; reflexivity).
rewrite upd_length. exact Lgs.
- apply evt_done. sf_eexists 7%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lgs.
Qed.
End CopyBack.
