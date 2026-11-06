(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1m2 X1nj X1nk X1ho X1hm X1nq X1mc.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
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
evt rsegs (qmf_synth_post Y N G0 G1 lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_qmf_synth) fc None m (seg_rom rsegs)).

Lemma qmf_synth_of_N : qmf_synth_stmt_N 320 -> qmf_synth_stmt_N 640 -> qmf_synth_stmt.
Proof.
intros H320 H640. unfold qmf_synth_stmt. intros until m. intros X LX HN. destruct HN as [-> | ->]; [eapply H320| eapply H640]; eassumption.
Qed.

Definition h0_bytes : list byte := match image_bytes rsegs 78324 256 with Some bs => bs | None => [] end.
Lemma h0_ro : forall m, mem_inv rsegs m -> u8ro rsegs m 78324 h0_bytes /\ length h0_bytes = 256%nat.
Proof.
intros m MI. assert (L : length h0_bytes = 256%nat) by (vm_compute; reflexivity). split; [|exact L].
unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m 78324 _ (ro_cells_image rsegs m 78324 h0_bytes MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite L; lia))) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.

Section Loops.
Context {RCEIL : RunCeiling}.
Variables (ra gp tp s0 : word).

#[using="Type"] Lemma qmf_L1 : forall (k : nat) (i q Y X1 : Z) (nx : nat) (ys xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = q + 1 -> 0 <= q -> 0 <= i ->
q + 1 + i <= Z.of_nat (length ys) -> i + q + 1 <= Z.of_nat nx ->
u32arr rsegs m1 Y ys -> u32arr rsegs m1 X1 xs -> length xs = nx ->
apart Y (4 * Z.of_nat (length ys)) X1 (4 * Z.of_nat nx) -> 4 <= Y -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 ->
munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (t2' t3' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 (Y + -4)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x21248) fc1 None m2 (seg_rom rsegs)
/\ munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X1 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 (Z_to_bv 64 (Y + 4 * q)) s0 s1 (Z_to_bv 64 (Y + -4)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (X1 + 4 * i)) t4 t5 t6)
F1 (Z_to_bv 64 0x21234) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i q Y X1 nx ys xs W m0 m1 sp' t0 t1 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F1 fc1
Hk Hq Hi Hqi Hin YA XA Lxs AP Ypos Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ YA) as BY. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof AP as AP'. unfold apart in AP'.
pose proof (u32arr_read_nth rsegs m1 Y ys q _ YA ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep.
pose proof (u32arr_store_ok rsegs m1 X1 xs i _ XA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X1 xs i v XA ltac:(lia)) as XA' end.
clear XA. store_done. try clear SOK.
zstep. zstep. if_cases K; zify_cond K.
- replace (Y + 4 * q + -4) with (Y + 4 * (q - 1)) by lia. replace (X1 + 4 * i + 4) with (X1 + 4 * (i + 1)) by lia.
eapply (IH (i + 1) (q - 1) Y X1 nx ys _ W m0); try eassumption; try lia. rewrite upd_length. exact Lxs.
- apply evt_done. sf_eexists 5%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.

#[using="Type"] Lemma qmf_L2 : forall (k : nat) (i j G X1 : Z) (nx : nat) (gs xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = Z.of_nat nx - i -> 0 <= i < Z.of_nat nx -> 0 <= j -> j + 2 * (Z.of_nat nx - i) <= Z.of_nat (length gs) + 1 ->
u32arr rsegs m1 G gs -> u32arr rsegs m1 X1 xs -> length xs = nx ->
apart G (4 * Z.of_nat (length gs)) X1 (4 * Z.of_nat nx) -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 ->
munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (t3' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 (Z_to_bv 64 (X1 + 4 * Z.of_nat nx)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'
(Z_to_bv 64 (X1 + 4 * Z.of_nat nx)) t5 t6)
F2 (Z_to_bv 64 0x21274) fc1 None m2 (seg_rom rsegs)
/\ munch ((X1, X1 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X1 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 (Z_to_bv 64 (X1 + 4 * i)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (G + 4 * j)) (Z_to_bv 64 (X1 + 4 * Z.of_nat nx)) t5 t6)
F1 (Z_to_bv 64 0x21260) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i j G X1 nx gs xs W m0 m1 sp' t0 t1 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F1 fc1
Hk Hi Hj Hjn GA XA Lxs AP Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ GA) as BG. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof AP as AP'. unfold apart in AP'.
pose proof (u32arr_read_nth rsegs m1 G gs j _ GA ltac:(lia) eq_refl) as RD.
zstep. clear RD.
pose proof (u32arr_store_ok rsegs m1 X1 xs i _ XA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X1 xs i v XA ltac:(lia)) as XA' end.
clear XA. store_done. try clear SOK.
zstep. zstep. zstep. if_cases K; zify_cond K.
- replace (X1 + 4 * i + 4) with (X1 + 4 * (i + 1)) by lia. replace (G + 4 * j + 8) with (G + 4 * (j + 2)) by lia.
eapply (IH (i + 1) (j + 2) G X1 nx gs _ W m0); try eassumption; try lia. rewrite upd_length. exact Lxs.
- apply evt_done. replace (X1 + 4 * i + 4) with (X1 + 4 * Z.of_nat nx) by lia. sf_eexists 4%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.

#[using="Type"] Lemma qmf_L3 : forall (k : nat) (i q qm Y X2 : Z) (nx : nat) (ys xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = q - qm + 1 -> 0 <= qm <= q -> 0 <= i -> q < Z.of_nat (length ys) -> i + (q - qm) + 1 <= Z.of_nat nx ->
u32arr rsegs m1 Y ys -> u32arr rsegs m1 X2 xs -> length xs = nx ->
apart Y (4 * Z.of_nat (length ys)) X2 (4 * Z.of_nat nx) -> 4 <= Y -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (t2' t3' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2' s0 s1 a0 (Z_to_bv 64 (Y + 4 * qm + -4)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
F2 (Z_to_bv 64 0x21298) fc1 None m2 (seg_rom rsegs)
/\ munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X2 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 (Z_to_bv 64 (Y + 4 * q)) s0 s1 a0 (Z_to_bv 64 (Y + 4 * qm + -4)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (X2 + 4 * i)) t4 t5 t6)
F1 (Z_to_bv 64 0x21284) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i q qm Y X2 nx ys xs W m0 m1 sp' t0 t1 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F1 fc1
Hk Hq Hi Hqi Hin YA XA Lxs AP Ypos Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ YA) as BY. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof AP as AP'. unfold apart in AP'.
pose proof (u32arr_read_nth rsegs m1 Y ys q _ YA ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep.
pose proof (u32arr_store_ok rsegs m1 X2 xs i _ XA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X2 xs i v XA ltac:(lia)) as XA' end.
clear XA. store_done. try clear SOK.
zstep. zstep. if_cases K; zify_cond K.
- replace (Y + 4 * q + -4) with (Y + 4 * (q - 1)) by lia. replace (X2 + 4 * i + 4) with (X2 + 4 * (i + 1)) by lia.
eapply (IH (i + 1) (q - 1) qm Y X2 nx ys _ W m0); try eassumption; try lia. rewrite upd_length. exact Lxs.
- apply evt_done. sf_eexists 5%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lxs.
Qed.

#[using="Type"] Lemma qmf_L4 : forall (k : nat) (i j G X2 : Z) (nx : nat) (gs xs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = Z.of_nat nx - i -> 0 <= i < Z.of_nat nx -> 0 <= j -> j + 2 * (Z.of_nat nx - i) <= Z.of_nat (length gs) + 1 ->
u32arr rsegs m1 G gs -> u32arr rsegs m1 X2 xs -> length xs = nx ->
apart G (4 * Z.of_nat (length gs)) X2 (4 * Z.of_nat nx) -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (t2' : word) (F2 : bvmap 5 word) (m2 : mem) (xs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2' s0 s1 a0 (Z_to_bv 64 (X2 + 4 * Z.of_nat nx)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (X2 + 4 * Z.of_nat nx)) t4 t5 t6)
F2 (Z_to_bv 64 0x212c0) fc1 None m2 (seg_rom rsegs)
/\ munch ((X2, X2 + 4 * Z.of_nat nx) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 X2 xs' /\ length xs' = nx)
(MS (mkR ra sp' gp tp t0 t1 (Z_to_bv 64 (G + 4 * j)) s0 s1 a0 (Z_to_bv 64 (X2 + 4 * i)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (X2 + 4 * Z.of_nat nx)) t4 t5 t6)
F1 (Z_to_bv 64 0x212ac) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i j G X2 nx gs xs W m0 m1 sp' t0 t1 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F1 fc1
Hk Hi Hj Hjn GA XA Lxs AP Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ GA) as BG. pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX.
pose proof AP as AP'. unfold apart in AP'.
pose proof (u32arr_read_nth rsegs m1 G gs j _ GA ltac:(lia) eq_refl) as RD.
zstep. clear RD.
pose proof (u32arr_store_ok rsegs m1 X2 xs i _ XA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 X2 xs i v XA ltac:(lia)) as XA' end.
clear XA. store_done. try clear SOK.
zstep. zstep. zstep. if_cases K; zify_cond K.
- replace (X2 + 4 * i + 4) with (X2 + 4 * (i + 1)) by lia. replace (G + 4 * j + 8) with (G + 4 * (j + 2)) by lia.
eapply (IH (i + 1) (j + 2) G X2 nx gs _ W m0); try eassumption; try lia. rewrite upd_length. exact Lxs.
- apply evt_done. replace (X2 + 4 * i + 4) with (X2 + 4 * Z.of_nat nx) by lia. sf_eexists 4%nat. split; [ms_eq|].
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

Section Inner.
Context {RCEIL : RunCeiling}.
Variables (ra sp' gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s10 s11 t3 t4 t5 t6 : word).

#[using="Type"] Lemma qmf_inner : forall (k : nat) (jj i N2 X1 X2 E p5 p6 p7 p8 p9 : Z) (nx : nat) (xs1 xs2 : list word) (hb : list byte) (m1 : mem)
(F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 16 - jj -> 0 <= jj < 16 -> 0 <= i -> i + 2 <= N2 -> Z.of_nat nx = N2 + 32 ->
E = X2 + 4 * (N2 + 32 - i) ->
p5 = X2 + 4 * (N2 - 1 - i) + 8 * jj -> p6 = X1 + 4 * (N2 - 1 - i) + 8 * jj -> p7 = 78332 + 16 * jj ->
p8 = X1 + 4 * (N2 - i) + 8 * jj -> p9 = X2 + 4 * (N2 - i) + 8 * jj ->
u32arr rsegs m1 X1 xs1 -> length xs1 = nx -> u32arr rsegs m1 X2 xs2 -> length xs2 = nx ->
u8ro rsegs m1 78324 hb -> length hb = 256%nat ->
0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (p5' p6' p7' p8' : word) (F2 : bvmap 5 word) (fc2 : bv 32),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 E) p5' p6' p7' p8' (Z_to_bv 64 E) s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x213d4) fc2 None m1 (seg_rom rsegs) /\ frm0 fc2)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 E) (Z_to_bv 64 p5) (Z_to_bv 64 p6) (Z_to_bv 64 p7)
(Z_to_bv 64 p8) (Z_to_bv 64 p9) s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x21364) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros jj i N2 X1 X2 E p5 p6 p7 p8 p9 nx xs1 xs2 hb m1 F1 fc1
Hk Hjj Hi HiN Hnx HE Hp5 Hp6 Hp7 Hp8 Hp9 X1A L1 X2A L2 HB LHB X1pos X1hi X2pos X2hi FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ X1A) as B1. pose proof (u32arr_bound _ _ _ _ X2A) as B2. rewrite L1 in B1. rewrite L2 in B2.
pose proof (bytes_at_bound _ _ _ _ HB) as BH. rewrite LHB in BH.
subst E p5 p6 p7 p8 p9.
pose proof (u32arr_read_nth rsegs m1 X1 xs1 (N2 - 1 - i + 2 * jj) _ X1A ltac:(lia) eq_refl) as RD6.
pose proof (u32arr_read_nth rsegs m1 X2 xs2 (N2 - 1 - i + 2 * jj) _ X2A ltac:(lia) eq_refl) as RD5.
pose proof (u32arr_read_nth rsegs m1 X1 xs1 (N2 - i + 2 * jj) _ X1A ltac:(lia) eq_refl) as RD8.
pose proof (u32arr_read_nth rsegs m1 X2 xs2 (N2 - i + 2 * jj) _ X2A ltac:(lia) eq_refl) as RD9.
pose proof (u8ro_read4 m1 78324 hb (16 * jj) _ HB ltac:(lia) ltac:(lia) eq_refl) as RA0.
pose proof (u8ro_read4 m1 78324 hb (16 * jj + 4) _ HB ltac:(lia) ltac:(lia) eq_refl) as RA1.
pose proof (u8ro_read4 m1 78324 hb (16 * jj + 8) _ HB ltac:(lia) ltac:(lia) eq_refl) as RA2.
pose proof (u8ro_read4 m1 78324 hb (16 * jj + 12) _ HB ltac:(lia) ltac:(lia) eq_refl) as RA3.

zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
clear RD5 RD6 RD8 RD9 RA0 RA1 RA2 RA3.
zstep. if_cases K; zify_cond K.
- eapply (IH (jj + 1) i N2 X1 X2); try eassumption; try lia.
- replace (X2 + 4 * (N2 - i) + 8 * jj + 8) with (X2 + 4 * (N2 + 32 - i)) by lia.
apply evt_done. sf_eexists 6%nat. split; [ms_eq| assumption].
Qed.
End Inner.

Ltac ystore Y idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with YA : u32arr rsegs mc Y ?l |- _ =>
let SOK := fresh "SOK" in
pose proof (u32arr_store_ok rsegs mc Y l idx _ YA ltac:(repeat rewrite upd_length; lia) eq_refl) as SOK;
zstep;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs mc Y l idx v YA ltac:(repeat rewrite upd_length; lia)) end;
clear YA; store_done; try clear SOK
end end.

Section Outer.
Context {RCEIL : RunCeiling}.
Variables (ra gp tp s0 a6 a7 s10 s11 : word).

#[using="Type"] Lemma qmf_outer : forall (k : nat) (i ii N2 X1 X2 Y q1 q2 q3 q5 q6 : Z) (nx : nat) (xs1 xs2 ys : list word) (hb : list byte) (W : list (Z * Z)) (m0 m1 : mem)
(sp' s4 s5 s6 s7 s8 s9 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k * 2 = N2 - i -> 0 <= i -> i + 2 <= N2 -> i = 2 * ii -> (N2 = 160 \/ N2 = 320) -> Z.of_nat nx = N2 + 32 ->
q1 = X1 + 4 * (N2 - 1 - i) -> q2 = X2 + 4 * (N2 - 1 - i) -> q3 = - i -> q5 = X2 + 4 * (N2 - i) -> q6 = X1 + 4 * (N2 - i) ->
u32arr rsegs m1 X1 xs1 -> length xs1 = nx -> u32arr rsegs m1 X2 xs2 -> length xs2 = nx ->
u32arr rsegs m1 Y ys -> Z.of_nat (length ys) = 2 * N2 -> u8ro rsegs m1 78324 hb -> length hb = 256%nat ->
apart Y (8 * N2) X1 (4 * Z.of_nat nx) -> apart Y (8 * N2) X2 (4 * Z.of_nat nx) ->
421888 <= Y -> Y + 8 * N2 <= 2^64 -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((Y, Y + 8 * N2) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (t2' t3' a1' s1' s2' s4' s5' s6' s7' s8' s9' t5' t6' : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (ys' : list word),
ms' = MS (mkR ra sp' gp tp (Z_to_bv 64 X1) (Z_to_bv 64 N2) t2' s0 s1' (Z_to_bv 64 128) a1'
(Z_to_bv 64 78332) (Z_to_bv 64 Y) (Z_to_bv 64 X2) (Z_to_bv 64 32) a6 a7 s2' (Z_to_bv 64 (4 * N2 + 128))
s4' s5' s6' s7' s8' s9' s10 s11 t3' (Z_to_bv 64 (N2 - 2)) t5' t6')
F2 (Z_to_bv 64 0x2141c) fc2 None m2 (seg_rom rsegs)
/\ munch ((Y, Y + 8 * N2) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 Y ys' /\ Z.of_nat (length ys') = 2 * N2)
(MS (mkR ra sp' gp tp (Z_to_bv 64 X1) (Z_to_bv 64 N2) (Z_to_bv 64 i) s0 (Z_to_bv 64 q1) (Z_to_bv 64 128) (Z_to_bv 64 ii)
(Z_to_bv 64 78332) (Z_to_bv 64 Y) (Z_to_bv 64 X2) (Z_to_bv 64 32) a6 a7 (Z_to_bv 64 q2) (Z_to_bv 64 (4 * N2 + 128))
s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q3) (Z_to_bv 64 (N2 - 2)) (Z_to_bv 64 q5) (Z_to_bv 64 q6))
F1 (Z_to_bv 64 0x21318) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ii N2 X1 X2 Y q1 q2 q3 q5 q6 nx xs1 xs2 ys hb W m0 m1 sp' s4 s5 s6 s7 s8 s9 F1 fc1
Hk Hi HiN Hii HN Hnx Hq1 Hq2 Hq3 Hq5 Hq6 X1A L1 X2A L2 YA LY HB LHB AP1 AP2 Y4 Yhi X1pos X1hi X2pos X2hi MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ X1A) as B1. pose proof (u32arr_bound _ _ _ _ X2A) as B2. rewrite L1 in B1. rewrite L2 in B2.
pose proof (u32arr_bound _ _ _ _ YA) as BY.
pose proof AP1 as AP1'. pose proof AP2 as AP2'. unfold apart in AP1', AP2'.

zstep. if_false_x. zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. zstep. zstep.
pose proof (u32arr_read_nth rsegs m1 X2 xs2 (N2 - 2 - i) _ X2A ltac:(lia) eq_refl) as RD1.
pose proof (u32arr_read_nth rsegs m1 X1 xs1 (N2 - 2 - i) _ X1A ltac:(lia) eq_refl) as RD2.
zstep. zstep. clear RD1 RD2.

zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. zstep. zstep.
do 5 zstep. do 4 zstep.
eapply evt_cut.
{ eapply qmf_inner with (k := 16%nat) (jj := 0) (i := i) (N2 := N2) (X1 := X1) (X2 := X2) (nx := nx) (xs1 := xs1) (xs2 := xs2) (hb := hb);
try eassumption; try lia. }
cbv beta. intros ms' sfH_; first [ sf_destruct 8%nat sfH_ as p5' p6' p7' p8' F2 fc2 -> FRM2 | sf_fb; destruct sfH_ as (p5' & p6' & p7' & p8' & F2 & fc2 & -> & FRM2) ]. clear FRM.

do 4 zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
do 6 zstep. zstep.
ystore Y (2 * i). ystore Y (2 * i + 1). ystore Y (2 * i + 2). ystore Y (2 * i + 3).
zstep. zstep. if_cases K; zify_cond K.
-
do 4 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with YA' : u32arr rsegs mc Y ?l |- _ =>
eapply (IH (i + 2) (ii + 1) N2 X1 X2 Y _ _ _ _ _ nx _ _ l hb W m0 mc) end end; try eassumption; try lia.
all: try (repeat rewrite upd_length; first [exact LY | lia]).
- apply evt_done. sf_eexists 17%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
repeat rewrite upd_length. exact LY.
Qed.
End Outer.

Section CopyBack.
Context {RCEIL : RunCeiling}.
Variables (ra gp tp s0 s10 s11 : word).

#[using="Type"] Lemma qmf_L5 : forall (k : nat) (i X1 G p0 p6 E : Z) (nx : nat) (xs gs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t1 t2 s1 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 32 - i -> 0 <= i < 32 -> p0 = X1 + 4 * i -> p6 = G + 4 * (2 * i + 1) -> E = X1 + 128 ->
u32arr rsegs m1 X1 xs -> length xs = nx -> (32 <= nx)%nat -> u32arr rsegs m1 G gs -> length gs = 64%nat ->
apart G 256 X1 (4 * Z.of_nat nx) -> 0 < X1 -> X1 + 4 * Z.of_nat nx < 2^64 ->
munch ((G, G + 256) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a6' : word) (F2 : bvmap 5 word) (m2 : mem) (gs' : list word),
ms' = MS (mkR ra sp' gp tp (Z_to_bv 64 E) t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x21440) fc1 None m2 (seg_rom rsegs)
/\ munch ((G, G + 256) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 G gs' /\ length gs' = 64%nat)
(MS (mkR ra sp' gp tp (Z_to_bv 64 p0) t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 (Z_to_bv 64 p6) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2142c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i X1 G p0 p6 E nx xs gs W m0 m1 sp' t1 t2 s1 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 F1 fc1
Hk Hi Hp0 Hp6 HE XA Lxs Hnx GA Lgs AP Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX. pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG.
pose proof AP as AP'. unfold apart in AP'. subst p0 p6 E.
pose proof (u32arr_read_nth rsegs m1 X1 xs i _ XA ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep.
pose proof (u32arr_store_ok rsegs m1 G gs (2 * i + 1) _ GA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 G gs (2 * i + 1) v GA ltac:(lia)) as GA' end.
clear GA. store_done. try clear SOK.
zstep. zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) X1 G); try eassumption; try lia. rewrite upd_length. exact Lgs.
- replace (X1 + 4 * i + 4) with (X1 + 128) by lia.
apply evt_done. sf_eexists 4%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lgs.
Qed.

#[using="Type"] Lemma qmf_L6 : forall (k : nat) (i X2 G p4 p7 E : Z) (nx : nat) (xs gs : list word) (W : list (Z * Z)) (m0 m1 : mem)
(sp' t0 t1 t2 s1 a1 a2 a3 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = 32 - i -> 0 <= i < 32 -> p4 = X2 + 4 * i -> p7 = G + 4 * (2 * i + 1) -> E = X2 + 128 ->
u32arr rsegs m1 X2 xs -> length xs = nx -> (32 <= nx)%nat -> u32arr rsegs m1 G gs -> length gs = 64%nat ->
apart G 256 X2 (4 * Z.of_nat nx) -> 0 < X2 -> X2 + 4 * Z.of_nat nx < 2^64 ->
munch ((G, G + 256) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
evt rsegs (fun ms' => exists (a7' : word) (F2 : bvmap 5 word) (m2 : mem) (gs' : list word),
ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 (Z_to_bv 64 E) a5 a6 a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x21460) fc1 None m2 (seg_rom rsegs)
/\ munch ((G, G + 256) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ u32arr rsegs m2 G gs' /\ length gs' = 64%nat)
(MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 (Z_to_bv 64 p4) a5 a6 (Z_to_bv 64 p7) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2144c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i X2 G p4 p7 E nx xs gs W m0 m1 sp' t0 t1 t2 s1 a1 a2 a3 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 F1 fc1
Hk Hi Hp4 Hp7 HE XA Lxs Hnx GA Lgs AP Xpos Xhi MU WM MI; [lia|].
pose proof (u32arr_bound _ _ _ _ XA) as BX. rewrite Lxs in BX. pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG.
pose proof AP as AP'. unfold apart in AP'. subst p4 p7 E.
pose proof (u32arr_read_nth rsegs m1 X2 xs i _ XA ltac:(lia) eq_refl) as RD.
zstep. clear RD. zstep.
pose proof (u32arr_store_ok rsegs m1 G gs (2 * i + 1) _ GA ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 G gs (2 * i + 1) v GA ltac:(lia)) as GA' end.
clear GA. store_done. try clear SOK.
zstep. zstep. if_cases K; zify_cond K.
- eapply (IH (i + 1) X2 G); try eassumption; try lia. rewrite upd_length. exact Lgs.
- replace (X2 + 4 * i + 4) with (X2 + 128) by lia.
apply evt_done. sf_eexists 4%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. rewrite upd_length. exact Lgs.
Qed.
End CopyBack.
