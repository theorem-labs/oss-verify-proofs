(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m5 X1go. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1nq X1mc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1r3 X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.
Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Inductive nl (P : Prop) : Prop := nl_i : P -> nl P.
Lemma nl_e : forall P : Prop, nl P -> P. Proof. intros P [H]; exact H. Qed.

Ltac lost_hint :=
match goal with
| |- (?x + _ <= ?y \/ _ <= _)%Z =>
let bx := nb_base x in let by_ := nb_base y in
first [ match goal with
| H : apart bx _ by_ _ |- _ => unfold apart in H
| H : apart by_ _ bx _ |- _ => unfold apart in H
end
| idtac ]
| |- _ => idtac
end.
Ltac lost_lia := lost_hint; lia.
Ltac lost_conj :=
lazymatch goal with
| |- True => exact I
| |- (_ <= _ /\ _ <= _) \/ _ => first [ left; split; lia | right; lost_conj ]
| |- _ /\ _ => split; [ lost_conj | lost_conj ]
| |- _ => lost_lia
end.

Local Ltac slia ::= nb_unbox_junk; cbv delta [SBSTATE_SIZEOF HOUT_BYTES]; lost_conj.

Lemma sb_ranges {RCEIL : RunCeiling} : forall (s : sbd_state bptr) (S : Z) (a : sb_addrs),
(forall x, In x (sb_blocks s S a) -> rblock_range (blk_addr x) (blk_size x)) ->
rblock_range S 160 /\ rblock_range (a_g0 a) 256 /\ rblock_range (a_g1 a) 256 /\ rblock_range (a_exc a) (4 * sbd_subframeSize s) /\
rblock_range (a_oq a) 32 /\ rblock_range (a_iq a) 32 /\ rblock_range (a_pg a) 16 /\ rblock_range (a_er a) 16 /\ rblock_range (a_msp a) 64.
Proof.
intros s S a H. unfold sb_blocks, SBSTATE_SIZEOF in H.
repeat split; (eapply (fun b (HI : In b _) => H b HI) with (b := (_, _, _)); cbn; tauto).
Qed.

Lemma rbr_al {RCEIL : RunCeiling} : forall A n, rblock_range A n -> A mod 8 = 0 /\ A mod 4 = 0.
Proof. intros A n (_ & H & _). split; Z.div_mod_to_equations; lia. Qed.
Lemma land_m64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.
Lemma sgtz_mask : forall n, 0 < n < 2^31 ->
Z.land (Z.land (bv_swrap 32 (0 - Z.b2z (9223372036854775808 <? Z.lxor n 9223372036854775808))) 18446744073709551615) n = n.
Proof.
intros n Hn. change 9223372036854775808 with (2^63). rewrite (zb_lxor_pow2_small n 63) by lia.
replace (2^63 <? n + 2^63) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
rewrite (swrap32_small (0 - 1)) by lia. change (Z.land (0 - 1) 18446744073709551615) with 18446744073709551615.
rewrite Z.land_comm. apply land_m64. lia.
Qed.

Ltac nd_neq N E := intro E; apply N; rewrite <- E; cbn; tauto.

Lemma sb_pairs_apart : forall (s : sbd_state bptr) (S : Z) (a : sb_addrs),
lbd_apart (sb_blocks s S a) -> List.NoDup (map blk_id (sb_blocks s S a)) ->
apart (S) (160) (a_g0 a) (256) /\
apart (S) (160) (a_g1 a) (256) /\
apart (S) (160) (a_exc a) (4 * sbd_subframeSize s) /\
apart (S) (160) (a_oq a) (32) /\
apart (S) (160) (a_iq a) (32) /\
apart (S) (160) (a_pg a) (16) /\
apart (S) (160) (a_er a) (16) /\
apart (S) (160) (a_msp a) (64) /\
apart (a_g0 a) (256) (a_g1 a) (256) /\
apart (a_g0 a) (256) (a_exc a) (4 * sbd_subframeSize s) /\
apart (a_g0 a) (256) (a_oq a) (32) /\
apart (a_g0 a) (256) (a_iq a) (32) /\
apart (a_g0 a) (256) (a_pg a) (16) /\
apart (a_g0 a) (256) (a_er a) (16) /\
apart (a_g0 a) (256) (a_msp a) (64) /\
apart (a_g1 a) (256) (a_exc a) (4 * sbd_subframeSize s) /\
apart (a_g1 a) (256) (a_oq a) (32) /\
apart (a_g1 a) (256) (a_iq a) (32) /\
apart (a_g1 a) (256) (a_pg a) (16) /\
apart (a_g1 a) (256) (a_er a) (16) /\
apart (a_g1 a) (256) (a_msp a) (64) /\
apart (a_exc a) (4 * sbd_subframeSize s) (a_oq a) (32) /\
apart (a_exc a) (4 * sbd_subframeSize s) (a_iq a) (32) /\
apart (a_exc a) (4 * sbd_subframeSize s) (a_pg a) (16) /\
apart (a_exc a) (4 * sbd_subframeSize s) (a_er a) (16) /\
apart (a_exc a) (4 * sbd_subframeSize s) (a_msp a) (64) /\
apart (a_oq a) (32) (a_iq a) (32) /\
apart (a_oq a) (32) (a_pg a) (16) /\
apart (a_oq a) (32) (a_er a) (16) /\
apart (a_oq a) (32) (a_msp a) (64) /\
apart (a_iq a) (32) (a_pg a) (16) /\
apart (a_iq a) (32) (a_er a) (16) /\
apart (a_iq a) (32) (a_msp a) (64) /\
apart (a_pg a) (16) (a_er a) (16) /\
apart (a_pg a) (16) (a_msp a) (64) /\
apart (a_er a) (16) (a_msp a) (64).
Proof.
intros s S a LAP ND. unfold sb_blocks, SBSTATE_SIZEOF in LAP, ND. cbn [map blk_id fst snd] in ND.
apply NoDup_cons_iff in ND as [N0 ND]. apply NoDup_cons_iff in ND as [N1 ND]. apply NoDup_cons_iff in ND as [N2 ND].
apply NoDup_cons_iff in ND as [N3 ND]. apply NoDup_cons_iff in ND as [N4 ND]. apply NoDup_cons_iff in ND as [N5 ND].
apply NoDup_cons_iff in ND as [N6 ND]. apply NoDup_cons_iff in ND as [N7 ND]. cbn [In] in N0, N1, N2, N3, N4, N5, N6, N7.
unfold apart. repeat match goal with |- _ /\ _ => split end.
- pose proof (LAP (sbd_blk s, S, 160) (sbd_g0_mem s, a_g0 a, 256)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_g1_mem s, a_g1 a, 256)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_old_qlsp s, a_oq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_interp_qlpc s, a_iq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_pi_gain s, a_pg a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_blk s, S, 160) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N0; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_g1_mem s, a_g1 a, 256)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_old_qlsp s, a_oq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_interp_qlpc s, a_iq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_pi_gain s, a_pg a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g0_mem s, a_g0 a, 256) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N1; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g1_mem s, a_g1 a, 256) (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N2; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g1_mem s, a_g1 a, 256) (sbd_old_qlsp s, a_oq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N2; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g1_mem s, a_g1 a, 256) (sbd_interp_qlpc s, a_iq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N2; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g1_mem s, a_g1 a, 256) (sbd_pi_gain s, a_pg a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N2; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g1_mem s, a_g1 a, 256) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N2; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_g1_mem s, a_g1 a, 256) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N2; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) (sbd_old_qlsp s, a_oq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N3; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) (sbd_interp_qlpc s, a_iq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N3; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) (sbd_pi_gain s, a_pg a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N3; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N3; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N3; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_old_qlsp s, a_oq a, 32) (sbd_interp_qlpc s, a_iq a, 32)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N4; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_old_qlsp s, a_oq a, 32) (sbd_pi_gain s, a_pg a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N4; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_old_qlsp s, a_oq a, 32) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N4; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_old_qlsp s, a_oq a, 32) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N4; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_interp_qlpc s, a_iq a, 32) (sbd_pi_gain s, a_pg a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N5; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_interp_qlpc s, a_iq a, 32) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N5; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_interp_qlpc s, a_iq a, 32) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N5; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_pi_gain s, a_pg a, 16) (sbd_exc_rms s, a_er a, 16)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N6; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_pi_gain s, a_pg a, 16) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N6; rewrite E; cbn; auto 20].
- pose proof (LAP (sbd_exc_rms s, a_er a, 16) (sbd_mem_sp s, a_msp a, 64)) as T; cbn [blk_addr blk_size blk_id fst snd] in T; apply T;
[cbn; tauto| cbn; tauto| intro E; apply N7; rewrite E; cbn; auto 20].
Qed.

Section NoiseLoop.
Context {RCEIL : RunCeiling}.
Variables (ra gp tp s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).

#[using="Type"] Lemma lost_noise_loop : forall (k : nat) (i N Y S : Z) (ny : nat) (cur : list word) (le : word) (W : list (Z * Z))
(m0 m1 : mem) (sp' sd t0 t1 t2 : word) (F1 : bvmap 5 word) (fc1 : bv 32),
Z.of_nat k = N - i -> 0 <= i < N -> N <= 320 -> 2 * N <= Z.of_nat ny ->
u32arr rsegs m1 Y cur -> length cur = ny -> Y mod 4 = 0 ->
rw_cells rsegs m1 (S + 128) [C4 le] -> 0 < S -> S + 160 <= Y ->
munch ((Y, Y + 4 * Z.of_nat ny) :: W) m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (sd' t0' t1' t2' : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur' : list word),
ms' = MS (mkR ra sp' gp tp t0' t1' t2' (Z_to_bv 64 S) s1 (Z_to_bv 64 N) sd' (Z_to_bv 64 1065353216) (Z_to_bv 64 N)
(Z_to_bv 64 1664525) (Z_to_bv 64 1013904223) (Z_to_bv 64 N) (Z_to_bv 64 1)
(Z_to_bv 64 Y) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F2 (Z_to_bv 64 0x2fe48) fc2 None m2 (seg_rom rsegs)
/\ munch ((Y, Y + 4 * Z.of_nat ny) :: W) m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2
/\ u32arr rsegs m2 Y cur' /\ length cur' = ny
/\ rw_cells rsegs m2 (S + 128) [C4 le])
(MS (mkR ra sp' gp tp t0 t1 t2 (Z_to_bv 64 S) s1 (Z_to_bv 64 i) sd (Z_to_bv 64 1065353216) (Z_to_bv 64 N)
(Z_to_bv 64 1664525) (Z_to_bv 64 1013904223) (Z_to_bv 64 N) (Z_to_bv 64 1)
(Z_to_bv 64 Y) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x2fdc8) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i N Y S ny cur le W m0 m1 sp' sd t0 t1 t2 F1 fc1
Hk Hi HN HNy ARR Lcur YA SCL Spos SY MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ ARR) as BA. rewrite Lcur in BA.
pose proof (rw_cells_bound _ _ _ _ SCL) as BL. cbn [cells_size csize Nat.add] in BL.
assert (AL : (Y + (i + N + 0) * 4) mod 4 = 0) by (Z.div_mod_to_equations; lia).
bato 0x2fe40.
pose proof (u32arr_store_ok rsegs m1 Y cur (i + N) _ ARR ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 Y cur (i + N) v ARR ltac:(lia)) as ARR' end.
clear ARR. store_done. try clear SOK.
zstep.
rewrite (swrap32_small (i + 1)) by lia.
if_cases K; zify_cond K.
- eapply (IH (i + 1) N Y S ny _ le W m0); try eassumption; try lia. rewrite upd_length. exact Lcur.
- apply evt_done. replace (i + 1) with N by lia.
sf_eexists 8%nat. split; [reflexivity|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. split; [rewrite upd_length; exact Lcur|]. eassumption.
Qed.
End NoiseLoop.

Lemma f32_bytes_length : forall ws, length (cells_bytes (f32 ws)) = (4 * length ws)%nat.
Proof. intros. rewrite cells_bytes_f32. apply u32s_length. Qed.
Lemma u8arr_as_f32 : forall m A bs (n : nat), u8arr rsegs m A bs -> length bs = (4 * n)%nat ->
exists ws, length ws = n /\ rw_cells rsegs m A (f32 ws).
Proof.
intros m A bs n U L. apply (rw_cells_CB_f32 rsegs m A n bs).
destruct U as [B W]. split; [split; [cbn; split; [exact L| exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B] |].
cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, <- L. exact W.
Qed.
Lemma f32_as_u8arr : forall m A ws, rw_cells rsegs m A (f32 ws) ->
u8arr rsegs m A (cells_bytes (f32 ws)) /\ length (cells_bytes (f32 ws)) = (4 * length ws)%nat.
Proof.
intros m A ws H. pose proof (rw_cells_f32_CB _ _ _ _ H) as [[_ B] W]. split; [| apply f32_bytes_length].
unfold u8arr. rewrite f32_bytes_length.
split; [cbn [cells_bytes cbytes] in B; rewrite app_nil_r in B; exact B|].
cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r in W. exact W.
Qed.

Definition sb_decode_lost_stmtX {RCEIL : RunCeiling} : Prop :=
forall (S OUT : Z) (s : sbd_state bptr) (a : sb_addrs) (j : sb_junk) (outb : list byte) (lo : Z) (stk8 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells rsegs m S (SBCELLS s a OUT j) -> sb_junk_ok s j -> sb_inv s -> sb_bufs rsegs m a j ->
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES ->
lbd_apart (sb_blocks s S a) -> List.NoDup (map blk_id (sb_blocks s S a)) ->
(forall x, In x (sb_blocks s S a) -> rblock_range (blk_addr x) (blk_size x)) ->
alloc_ceiling <= OUT -> alloc_ceiling <= lo -> apart OUT HOUT_BYTES lo (bv_unsigned sp - lo) ->
stk rsegs m lo (bv_unsigned sp) -> lo + SBLOST_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^63 ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 OUT -> a2 = Z_to_bv 64 1 -> a3 = stk8 ->
mem_inv rsegs m -> frm0 fc ->
OUT mod 4 = 0 ->
evt rsegs (sb_decode_lost_post S OUT s a lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_sb_decode_lost) fc None m (seg_rom rsegs)).

