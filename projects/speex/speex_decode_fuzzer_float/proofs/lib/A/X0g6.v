(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X02b X0j0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X0ta X19k.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA.X1e9.
Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition alloca_poison_entry : Z := 0x51e24.

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
assert (E2 : Z.ones 64 = Z.lor 18446744073709551584 31) by reflexivity.
rewrite E2, Z.land_lor_distr_r in E1.
pose proof (Z.add_lor_land (Z.land x 18446744073709551584) (Z.land x 31)) as E3.
assert (E4 : Z.land (Z.land x 18446744073709551584) (Z.land x 31) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
assert (B : Z.testbit 18446744073709551584 i && Z.testbit 31 i = false)
by (rewrite <- Z.land_spec; change (Z.land 18446744073709551584 31) with 0; apply Z.bits_0).
destruct (Z.testbit x i), (Z.testbit 18446744073709551584 i), (Z.testbit 31 i); cbn in *; congruence. }
rewrite E4, Z.add_0_r, E1 in E3.
change 31 with (Z.ones 5) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 5) with 32 in E3.
pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

Lemma land_m8a : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
intros x Hx.
assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
assert (E2 : Z.ones 64 = Z.lor 18446744073709551608 7) by reflexivity.
rewrite E2, Z.land_lor_distr_r in E1.
pose proof (Z.add_lor_land (Z.land x 18446744073709551608) (Z.land x 7)) as E3.
assert (E4 : Z.land (Z.land x 18446744073709551608) (Z.land x 7) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
assert (B : Z.testbit 18446744073709551608 i && Z.testbit 7 i = false)
by (rewrite <- Z.land_spec; change (Z.land 18446744073709551608 7) with 0; apply Z.bits_0).
destruct (Z.testbit x i), (Z.testbit 18446744073709551608 i), (Z.testbit 7 i); cbn in *; congruence. }
rewrite E4, Z.add_0_r, E1 in E3.
change 7 with (Z.ones 3) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 3) with 8 in E3.
pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.

Lemma lor3 : forall x, 0 <= x -> Z.lor x 3 = 4 * (x / 4) + 3.
Proof.
intros x Hx. pose proof (Z.add_lor_land x 3) as E.
assert (L : Z.land x 3 = x mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
rewrite L in E. pose proof (Z.div_mod x 4 ltac:(lia)). lia.
Qed.

Lemma ap_stk_window : forall (m : mem) lo hi a n, stk bsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
stk bsegs m lo a /\ (exists junk, rw_cells bsegs m a [CB (Z.to_nat n) junk]) /\ stk bsegs m (a + n) hi.
Proof.
intros m lo hi a n ST H1 H2 H3.
destruct (stk_split bsegs m lo a hi ST ltac:(lia)) as [S1 S23].
destruct (stk_split bsegs m a (a + n) hi S23 ltac:(lia)) as [S2 S3].
split; [exact S1|]. split; [| exact S3].
destruct (stk_carve bsegs m a (a + n) (Z.to_nat n) S2 ltac:(lia)) as [_ (junk & FR)].
exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in FR by lia. exact FR.
Qed.

Definition ap_rr (A n : Z) : Z := (A + n + 31) / 32 * 32.

Lemma ap_count : forall u r, 0 <= u -> 0 <= r < 32 ->
Z.lor ((32 * u + r + 31) ≫ 3) 3 - (if r =? 0 then 32 * u else 32 * u + 32) ≫ 3 + 1 = 4.
Proof.
intros u r Hu Hr. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite lor3 by (apply Z.div_pos; lia).
destruct (Z.eqb_spec r 0) as [->|NZ].
- replace (32 * u + 0 + 31) with (31 + (4 * u) * 8) by lia. rewrite Z.div_add by lia. change (31 / 8) with 3.
replace (3 + 4 * u) with (3 + u * 4) by lia. rewrite Z.div_add by lia. change (3 / 4) with 0.
replace (32 * u) with ((4 * u) * 8) by lia. rewrite Z.div_mul by lia. lia.
- replace (32 * u + r + 31) with ((r + 31) + (4 * u) * 8) by lia. rewrite Z.div_add by lia.
assert (X : 4 <= (r + 31) / 8 <= 7) by (split; [apply Z.div_le_lower_bound; lia| assert ((r + 31) / 8 < 8) by (apply Z.div_lt_upper_bound; lia); lia]).
replace ((r + 31) / 8 + 4 * u) with ((r + 31) / 8 + u * 4) by lia. rewrite Z.div_add by lia.
assert (Y : ((r + 31) / 8) / 4 = 1) by (symmetry; apply Z.div_unique with ((r + 31) / 8 - 4); lia).
rewrite Y. replace (32 * u + 32) with ((4 * u + 4) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma le1_m53 : le1 (Z_to_bv 64 (-53)) = [Z_to_bv 8 203].
Proof. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma le1_small : forall k, 0 <= k < 256 -> le1 (Z_to_bv 64 k) = [Z_to_bv 8 k].
Proof. intros k Hk. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ap_stk_cons : forall (m : mem) a hi (b : byte), rw_cells bsegs m a [C1 b] -> stk bsegs m (a + 1) hi -> a + 1 <= hi -> stk bsegs m a hi.
Proof.
intros m a hi b C S H. pose proof (stk_of_rw_cells bsegs m a [C1 b] C) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 1) with 1 in S1.
apply (stk_merge bsegs m a (a + 1) hi S1 S). lia.
Qed.

Lemma ap_stk_cb4 : forall (m : mem) a (bs : list byte), rw_cells bsegs m a [CB (Z.to_nat 4) bs] -> stk bsegs m a (a + 4).
Proof.
intros m a bs C. pose proof (stk_of_rw_cells bsegs m a _ C) as S1. cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op] in S1.
change (Z.of_nat 4) with 4 in S1. exact S1.
Qed.

Definition alloca_poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [(shad (A - 32), shad (A - 32) + 4); (shad (A + n), shad (ap_rr A n) + 4); (bv_unsigned sp - 64, bv_unsigned sp)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ rw_cells bsegs m' (shad (A - 32)) [CB 4 (repeat (Z_to_bv 8 202) 4)]
/\ stk bsegs m' (shad (A + n)) (shad (ap_rr A n) + 4)
/\ ((A + n) mod 8 <> 0 -> rw_cells bsegs m' (shad (A + n)) [C1 (Z_to_bv 8 ((A + n) mod 8))]).

Lemma alloca_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (A n lo : Z) (j1 : list byte),
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> A mod 32 = 0 -> 0 <= n < 2^40 -> 0x10000 <= A - 32 -> A + n + 64 <= 2^47 ->
m2s_cells m -> setshadow_cells m ->
rw_cells bsegs m 0xfc110 [C8 (Z_to_bv 64 0x1032b8)] -> rw_cells bsegs m (0x1032b8 + 85) [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m (shad (A - 32)) [CB 4 j1] ->
stk bsegs m (shad (A + n)) (shad (ap_rr A n) + 4) ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x65b000 <= lo -> shad (ap_rr A n) + 4 <= lo ->
mem_inv bsegs m ->
evt bsegs (alloca_poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 alloca_poison_entry) fc None m (seg_rom bsegs)).
Proof.
intros until j1. intros -> -> HA Hn HAl HAh M2S SS GF PPF SHL SHR ST LO ILO SHLO MI. unfold alloca_poison_entry.
destruct M2S as (M2a & M2b & M2c). destruct SS as (SS1 & SS2).
unfold g_got_real_memset, g_real_memset, musl_memset_entry in *. change (0x1032b8 + 85) with 1061645 in PPF.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
assert (HQ : exists q, A = 32 * q) by (exists (A / 32); pose proof (Z.div_mod A 32 ltac:(lia)); lia). destruct HQ as (q & ->).

set (P := n + 32 * q) in *.
assert (HP : 0 <= P < 2^47) by (unfold P; lia).
set (u := P / 32). set (r := P mod 32). assert (EP : P = 32 * u + r /\ 0 <= r < 32) by (unfold u, r; pose proof (Z.div_mod P 32 ltac:(lia)); pose proof (Z.mod_pos_bound P 32 ltac:(lia)); lia).
clearbody u r. destruct EP as (EP & Hr).
replace (32 * q + n) with P in * by (unfold P; lia).
assert (ESP : shad P = SHB + 4 * u + r / 8).
{ unfold shad. rewrite EP. replace (32 * u + r) with (r + (4 * u) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (ERRv : ap_rr (32 * q) n = if r =? 0 then 32 * u else 32 * u + 32).
{ unfold ap_rr. replace (32 * q + n + 31) with (P + 31) by (unfold P; lia). rewrite EP. destruct (Z.eqb_spec r 0) as [->|NZ].
- replace (32 * u + 0 + 31) with (31 + u * 32) by lia. rewrite Z.div_add by lia. change (31 / 32) with 0. lia.
- replace (32 * u + r + 31) with ((r + 31) + u * 32) by lia. rewrite Z.div_add by lia.
assert ((r + 31) / 32 = 1) by (symmetry; apply Z.div_unique with (r - 1); lia). lia. }
assert (ESR : shad (ap_rr (32 * q) n) = if r =? 0 then SHB + 4 * u else SHB + 4 * u + 4).
{ rewrite ERRv. unfold shad. destruct (r =? 0).
- replace (32 * u) with ((4 * u) * 8) by lia. rewrite Z.div_mul by lia. lia.
- replace (32 * u + 32) with ((4 * u + 4) * 8) by lia. rewrite Z.div_mul by lia. lia. }
rewrite ESP, ESR in *.
assert (ESL : shad (32 * q - 32) = SHB + (4 * q - 4)) by (unfold shad; replace (32 * q - 32) with ((4 * q - 4) * 8) by lia; rewrite Z.div_mul by lia; lia).
assert (Hqu : q <= u) by (assert (32 * q <= P) by (unfold P; lia); lia).
assert (SHLlo : shad (32 * q - 32) + 4 <= lo) by (rewrite ESL; destruct (r =? 0); lia).
assert (SHLb : 2147450880 <= shad (32 * q - 32) /\ shad (32 * q - 32) + 4 <= 2^47) by (rewrite ESL; unfold SHB; lia).
unfold SHB in *.
pose proof (munch_refl [(shad (32 * q - 32), shad (32 * q - 32) + 4); (SHB + 4 * u + r / 8, (if r =? 0 then SHB + 4 * u else SHB + 4 * u + 4) + 4); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
unfold SHB in MU.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 64%nat ST.
do 8 zstep.
do 18 zstep.
assert (E1 : (32 * q + -8) ≫ 3 = 4 * q - 1) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * q + -8) with ((4 * q - 1) * 8) by lia; apply Z.div_mul; lia).
assert (E2 : (32 * q + -32) ≫ 3 = 4 * q - 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * q + -32) with ((4 * q - 4) * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2. replace (4 * q - 1 - (4 * q - 4) + 1) with 4 by lia.
rewrite <- ESL.
zstep.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (shad (32 * q - 32)) 202 4 j1).
all: try (change (Z.to_nat 4) with 4%nat); try eassumption; try lia.
fold P. replace (n + 32 * q + 31) with (P + 31) by (unfold P; lia).
rewrite (land_m32 (P + 31)) by lia. rewrite (land_m8a P) by lia.
assert (ERR2 : 32 * ((P + 31) / 32) = if r =? 0 then 32 * u else 32 * u + 32).
{ rewrite <- ERRv. unfold ap_rr. replace (32 * q + n + 31) with (P + 31) by (unfold P; lia). lia. }
assert (EPA2 : 8 * (P / 8) = 32 * u + 8 * (r / 8)).
{ rewrite EP. replace (32 * u + r) with (r + (4 * u) * 8) by lia. rewrite Z.div_add by lia. lia. }
rewrite ERR2, EPA2.
assert (EKM : P mod 8 = r mod 8).
{ rewrite EP. replace (32 * u + r) with (r + (4 * u) * 8) by lia. apply Z.mod_add. lia. }
assert (Hu : 0 <= u) by lia.
pose proof (ap_count u r Hu Hr) as CNT.
assert (EP31 : P + 31 = 32 * u + r + 31) by lia.

destruct (Z.eqb_spec r 0) as [R0|RN].
-
subst r. change (0 =? 0) with true in *. cbv iota in *. change (0 / 8) with 0 in *. replace (32 * u + 8 * 0) with (32 * u) in * by lia. rewrite ?Z.add_0_r in *.
zstep. ifT.
do 9 zstep. rewrite EP31, CNT.
do 8 zstep.
assert (E4u : (32 * u) ≫ 3 = 4 * u) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * u) with ((4 * u) * 8) by lia; apply Z.div_mul; lia).
rewrite E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
destruct (ap_stk_window _ _ _ (2147450880 + 4 * u) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (2147450880 + 4 * u) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (2147450880 + 4 * u) [CB (Z.to_nat 4) _] |- _ =>
pose proof (stk_of_rw_cells bsegs mm _ _ H) as SHR'; cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op] in SHR'; change (Z.of_nat 4) with 4 in SHR' end.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SHR'|].
intros NZ. exfalso. apply NZ. rewrite EKM. reflexivity.
-
replace (r =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbv iota in *.
set (e := r / 8) in *. set (k := r mod 8).
assert (Erk : r = 8 * e + k /\ 0 <= k < 8 /\ 0 <= e <= 3) by (unfold e, k; pose proof (Z.div_mod r 8 ltac:(lia)); pose proof (Z.mod_pos_bound r 8 ltac:(lia)); split; [lia|]; split; [lia|]; split; [apply Z.div_pos; lia| assert (r / 8 < 4) by (apply Z.div_lt_upper_bound; lia); lia]).
clearbody e k. destruct Erk as (Erk & Hk & He).
assert (ESH3 : P ≫ 3 = 4 * u + e).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite EP, Erk. replace (32 * u + (8 * e + k)) with (k + (4 * u + e) * 8) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
assert (EL7 : Z.land P 7 = k).
{ change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite EP, Erk.
replace (32 * u + (8 * e + k)) with (k + (4 * u + e) * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (EKr : P mod 8 = k) by (rewrite EKM, Erk; replace (8 * e + k) with (k + e * 8) by lia; rewrite Z.mod_add by lia; apply Z.mod_small; lia).
assert (E4u : (32 * u + 32) ≫ 3 = 4 * u + 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * u + 32) with ((4 * u + 4) * 8) by lia; apply Z.div_mul; lia).
zstep. ifF.
do 8 zstep.
rewrite ?ESH3, ?EL7.
zstep. try ifF.
do 3 zstep.
remember (2147450880 + (4 * u + e)) as D eqn:ED.
replace (2147450880 + 4 * u + e) with D in * by lia.
replace (2147450880 + 4 * u + 4 + 4) with (D + (8 - e)) in * by lia.
assert (HD : 2147450880 <= D /\ D + 8 < 2^47) by lia.

Ltac ap_it_cb Da SHR jb BC :=
zstep; zstep; ifF; zstep; zstep; zstep;
destruct (ap_stk_window _ _ _ Da 1 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jb & BC) & SHR'); clear SHR; rename SHR' into SHR;
change (Z.to_nat 1) with 1%nat in BC;
zstep; rewrite le1_m53; mem_after_store; zstep; zstep.

Ltac ap_it_k Da SHR jb BC :=
zstep; zstep; ifT; zstep;
destruct (ap_stk_window _ _ _ Da 1 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jb & BC) & SHR'); clear SHR; rename SHR' into SHR;
change (Z.to_nat 1) with 1%nat in BC;
zstep; rewrite le1_small by lia; mem_after_store; zstep; zstep.

Ltac ap_tail2 EP31 CNT E4u :=
do 9 zstep; rewrite EP31, CNT; do 8 zstep; rewrite E4u.
assert (He4 : e = 0 \/ e = 1 \/ e = 2 \/ e = 3) by lia.
destruct (Z.eq_dec k 0) as [K0|KN]; destruct He4 as [ -> | [ -> | [ -> | -> ] ] ].
all: try (exfalso; lia).
+
ap_it_cb D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifF.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_it_cb (D + 2) SHR jb2 BC2.
zstep; ifT.
replace (D + 2 + 1) with (D + 3) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 3) by lia.
destruct (ap_stk_window _ _ _ (D + 3) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 3) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 7) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 3) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 3 + 4) with (D + 7) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm (D + 2) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 2) (D + 7) _ H ltac:(replace (D + 2 + 1) with (D + 3) by lia; exact SR) ltac:(lia)) as SR2 end. clear SR. rename SR2 into SR.
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 7) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 7) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros NZ. exfalso. apply NZ. rewrite EKr. exact K0.
+
ap_it_cb D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifT.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 2) by lia.
destruct (ap_stk_window _ _ _ (D + 2) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 2) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 6) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 2) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 2 + 4) with (D + 6) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 6) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 6) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros NZ. exfalso. apply NZ. rewrite EKr. exact K0.
+
ap_it_cb D SHR jb0 BC0.
zstep; ifT.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 1) by lia.
destruct (ap_stk_window _ _ _ (D + 1) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 1) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 5) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 1 + 4) with (D + 5) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 5) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros NZ. exfalso. apply NZ. rewrite EKr. exact K0.
+
ap_it_k D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifF.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_it_cb (D + 2) SHR jb2 BC2.
zstep; ifF.
replace (D + 2 + 1) with (D + 3) in SHR by lia.
ap_it_cb (D + 3) SHR jb3 BC3.
zstep; ifT.
replace (D + 3 + 1) with (D + 4) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 4) by lia.
destruct (ap_stk_window _ _ _ (D + 4) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 4) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 8) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 4) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 4 + 4) with (D + 8) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm (D + 3) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 3) (D + 8) _ H ltac:(replace (D + 3 + 1) with (D + 4) by lia; exact SR) ltac:(lia)) as SR3 end. clear SR. rename SR3 into SR.
lazymatch goal with H : rw_cells bsegs ?mm (D + 2) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 2) (D + 8) _ H ltac:(replace (D + 2 + 1) with (D + 3) by lia; exact SR) ltac:(lia)) as SR2 end. clear SR. rename SR2 into SR.
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 8) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 8) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
+
ap_it_k D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifF.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_it_cb (D + 2) SHR jb2 BC2.
zstep; ifT.
replace (D + 2 + 1) with (D + 3) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 3) by lia.
destruct (ap_stk_window _ _ _ (D + 3) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 3) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 7) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 3) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 3 + 4) with (D + 7) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm (D + 2) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 2) (D + 7) _ H ltac:(replace (D + 2 + 1) with (D + 3) by lia; exact SR) ltac:(lia)) as SR2 end. clear SR. rename SR2 into SR.
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 7) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 7) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
+
ap_it_k D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifT.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 2) by lia.
destruct (ap_stk_window _ _ _ (D + 2) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 2) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 6) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 2) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 2 + 4) with (D + 6) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 6) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 6) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
+
ap_it_k D SHR jb0 BC0.
zstep; ifT.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 1) by lia.
destruct (ap_stk_window _ _ _ (D + 1) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 1) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 5) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells bsegs ?mm (D + 1) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 1 + 4) with (D + 5) in SR by lia.
lazymatch goal with H : rw_cells bsegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 5) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
Qed.
End B_TWIN.

Import ListNotations.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition alloca_poison_entry : Z := 0x51d38.

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
assert (E2 : Z.ones 64 = Z.lor 18446744073709551584 31) by reflexivity.
rewrite E2, Z.land_lor_distr_r in E1.
pose proof (Z.add_lor_land (Z.land x 18446744073709551584) (Z.land x 31)) as E3.
assert (E4 : Z.land (Z.land x 18446744073709551584) (Z.land x 31) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
assert (B : Z.testbit 18446744073709551584 i && Z.testbit 31 i = false)
by (rewrite <- Z.land_spec; change (Z.land 18446744073709551584 31) with 0; apply Z.bits_0).
destruct (Z.testbit x i), (Z.testbit 18446744073709551584 i), (Z.testbit 31 i); cbn in *; congruence. }
rewrite E4, Z.add_0_r, E1 in E3.
change 31 with (Z.ones 5) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 5) with 32 in E3.
pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

Lemma land_m8a : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
intros x Hx.
assert (E1 : Z.land x (Z.ones 64) = x) by (rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
assert (E2 : Z.ones 64 = Z.lor 18446744073709551608 7) by reflexivity.
rewrite E2, Z.land_lor_distr_r in E1.
pose proof (Z.add_lor_land (Z.land x 18446744073709551608) (Z.land x 7)) as E3.
assert (E4 : Z.land (Z.land x 18446744073709551608) (Z.land x 7) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, Z.bits_0.
assert (B : Z.testbit 18446744073709551608 i && Z.testbit 7 i = false)
by (rewrite <- Z.land_spec; change (Z.land 18446744073709551608 7) with 0; apply Z.bits_0).
destruct (Z.testbit x i), (Z.testbit 18446744073709551608 i), (Z.testbit 7 i); cbn in *; congruence. }
rewrite E4, Z.add_0_r, E1 in E3.
change 7 with (Z.ones 3) in E3. rewrite Z.land_ones in E3 by lia. change (2 ^ 3) with 8 in E3.
pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.

Lemma lor3 : forall x, 0 <= x -> Z.lor x 3 = 4 * (x / 4) + 3.
Proof.
intros x Hx. pose proof (Z.add_lor_land x 3) as E.
assert (L : Z.land x 3 = x mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
rewrite L in E. pose proof (Z.div_mod x 4 ltac:(lia)). lia.
Qed.

Lemma ap_stk_window : forall (m : mem) lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
stk asegs m lo a /\ (exists junk, rw_cells asegs m a [CB (Z.to_nat n) junk]) /\ stk asegs m (a + n) hi.
Proof.
intros m lo hi a n ST H1 H2 H3.
destruct (stk_split asegs m lo a hi ST ltac:(lia)) as [S1 S23].
destruct (stk_split asegs m a (a + n) hi S23 ltac:(lia)) as [S2 S3].
split; [exact S1|]. split; [| exact S3].
destruct (stk_carve asegs m a (a + n) (Z.to_nat n) S2 ltac:(lia)) as [_ (junk & FR)].
exists junk. replace (a + n - Z.of_nat (Z.to_nat n)) with a in FR by lia. exact FR.
Qed.

Definition ap_rr (A n : Z) : Z := (A + n + 31) / 32 * 32.

Lemma ap_count : forall u r, 0 <= u -> 0 <= r < 32 ->
Z.lor ((32 * u + r + 31) ≫ 3) 3 - (if r =? 0 then 32 * u else 32 * u + 32) ≫ 3 + 1 = 4.
Proof.
intros u r Hu Hr. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite lor3 by (apply Z.div_pos; lia).
destruct (Z.eqb_spec r 0) as [->|NZ].
- replace (32 * u + 0 + 31) with (31 + (4 * u) * 8) by lia. rewrite Z.div_add by lia. change (31 / 8) with 3.
replace (3 + 4 * u) with (3 + u * 4) by lia. rewrite Z.div_add by lia. change (3 / 4) with 0.
replace (32 * u) with ((4 * u) * 8) by lia. rewrite Z.div_mul by lia. lia.
- replace (32 * u + r + 31) with ((r + 31) + (4 * u) * 8) by lia. rewrite Z.div_add by lia.
assert (X : 4 <= (r + 31) / 8 <= 7) by (split; [apply Z.div_le_lower_bound; lia| assert ((r + 31) / 8 < 8) by (apply Z.div_lt_upper_bound; lia); lia]).
replace ((r + 31) / 8 + 4 * u) with ((r + 31) / 8 + u * 4) by lia. rewrite Z.div_add by lia.
assert (Y : ((r + 31) / 8) / 4 = 1) by (symmetry; apply Z.div_unique with ((r + 31) / 8 - 4); lia).
rewrite Y. replace (32 * u + 32) with ((4 * u + 4) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma le1_m53 : le1 (Z_to_bv 64 (-53)) = [Z_to_bv 8 203].
Proof. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma le1_small : forall k, 0 <= k < 256 -> le1 (Z_to_bv 64 k) = [Z_to_bv 8 k].
Proof. intros k Hk. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ap_stk_cons : forall (m : mem) a hi (b : byte), rw_cells asegs m a [C1 b] -> stk asegs m (a + 1) hi -> a + 1 <= hi -> stk asegs m a hi.
Proof.
intros m a hi b C S H. pose proof (stk_of_rw_cells asegs m a [C1 b] C) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 1) with 1 in S1.
apply (stk_merge asegs m a (a + 1) hi S1 S). lia.
Qed.

Lemma ap_stk_cb4 : forall (m : mem) a (bs : list byte), rw_cells asegs m a [CB (Z.to_nat 4) bs] -> stk asegs m a (a + 4).
Proof.
intros m a bs C. pose proof (stk_of_rw_cells asegs m a _ C) as S1. cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op] in S1.
change (Z.of_nat 4) with 4 in S1. exact S1.
Qed.

Definition alloca_poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(shad (A - 32), shad (A - 32) + 4); (shad (A + n), shad (ap_rr A n) + 4); (bv_unsigned sp - 64, bv_unsigned sp)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (shad (A - 32)) [CB 4 (repeat (Z_to_bv 8 202) 4)]
/\ stk asegs m' (shad (A + n)) (shad (ap_rr A n) + 4)
/\ ((A + n) mod 8 <> 0 -> rw_cells asegs m' (shad (A + n)) [C1 (Z_to_bv 8 ((A + n) mod 8))]).

Lemma alloca_poison_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (A n lo : Z) (j1 : list byte),
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> A mod 32 = 0 -> 0 <= n < 2^40 -> 0x10000 <= A - 32 -> A + n + 64 <= 2^47 ->
m2s_cells m -> setshadow_cells m ->
rw_cells asegs m 0xf3890 [C8 (Z_to_bv 64 0xfaa78)] -> rw_cells asegs m (0xfaa78 + 85) [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m (shad (A - 32)) [CB 4 j1] ->
stk asegs m (shad (A + n)) (shad (ap_rr A n) + 4) ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> 0x652000 <= lo -> shad (ap_rr A n) + 4 <= lo ->
mem_inv asegs m ->
evt asegs (alloca_poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 alloca_poison_entry) fc None m (seg_rom asegs)).
Proof.
intros until j1. intros -> -> HA Hn HAl HAh M2S SS GF PPF SHL SHR ST LO ILO SHLO MI. unfold alloca_poison_entry.
destruct M2S as (M2a & M2b & M2c). destruct SS as (SS1 & SS2).
unfold g_got_real_memset, g_real_memset, musl_memset_entry in *. change (0xfaa78 + 85) with 1026765 in PPF.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
assert (HQ : exists q, A = 32 * q) by (exists (A / 32); pose proof (Z.div_mod A 32 ltac:(lia)); lia). destruct HQ as (q & ->).

set (P := n + 32 * q) in *.
assert (HP : 0 <= P < 2^47) by (unfold P; lia).
set (u := P / 32). set (r := P mod 32). assert (EP : P = 32 * u + r /\ 0 <= r < 32) by (unfold u, r; pose proof (Z.div_mod P 32 ltac:(lia)); pose proof (Z.mod_pos_bound P 32 ltac:(lia)); lia).
clearbody u r. destruct EP as (EP & Hr).
replace (32 * q + n) with P in * by (unfold P; lia).
assert (ESP : shad P = SHB + 4 * u + r / 8).
{ unfold shad. rewrite EP. replace (32 * u + r) with (r + (4 * u) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (ERRv : ap_rr (32 * q) n = if r =? 0 then 32 * u else 32 * u + 32).
{ unfold ap_rr. replace (32 * q + n + 31) with (P + 31) by (unfold P; lia). rewrite EP. destruct (Z.eqb_spec r 0) as [->|NZ].
- replace (32 * u + 0 + 31) with (31 + u * 32) by lia. rewrite Z.div_add by lia. change (31 / 32) with 0. lia.
- replace (32 * u + r + 31) with ((r + 31) + u * 32) by lia. rewrite Z.div_add by lia.
assert ((r + 31) / 32 = 1) by (symmetry; apply Z.div_unique with (r - 1); lia). lia. }
assert (ESR : shad (ap_rr (32 * q) n) = if r =? 0 then SHB + 4 * u else SHB + 4 * u + 4).
{ rewrite ERRv. unfold shad. destruct (r =? 0).
- replace (32 * u) with ((4 * u) * 8) by lia. rewrite Z.div_mul by lia. lia.
- replace (32 * u + 32) with ((4 * u + 4) * 8) by lia. rewrite Z.div_mul by lia. lia. }
rewrite ESP, ESR in *.
assert (ESL : shad (32 * q - 32) = SHB + (4 * q - 4)) by (unfold shad; replace (32 * q - 32) with ((4 * q - 4) * 8) by lia; rewrite Z.div_mul by lia; lia).
assert (Hqu : q <= u) by (assert (32 * q <= P) by (unfold P; lia); lia).
assert (SHLlo : shad (32 * q - 32) + 4 <= lo) by (rewrite ESL; destruct (r =? 0); lia).
assert (SHLb : 2147450880 <= shad (32 * q - 32) /\ shad (32 * q - 32) + 4 <= 2^47) by (rewrite ESL; unfold SHB; lia).
unfold SHB in *.
pose proof (munch_refl [(shad (32 * q - 32), shad (32 * q - 32) + 4); (SHB + 4 * u + r / 8, (if r =? 0 then SHB + 4 * u else SHB + 4 * u + 4) + 4); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
unfold SHB in MU.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST.
do 8 zstep.
do 18 zstep.
assert (E1 : (32 * q + -8) ≫ 3 = 4 * q - 1) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * q + -8) with ((4 * q - 1) * 8) by lia; apply Z.div_mul; lia).
assert (E2 : (32 * q + -32) ≫ 3 = 4 * q - 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * q + -32) with ((4 * q - 4) * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2. replace (4 * q - 1 - (4 * q - 4) + 1) with 4 by lia.
rewrite <- ESL.
zstep.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (shad (32 * q - 32)) 202 4 j1).
all: try (change (Z.to_nat 4) with 4%nat); try eassumption; try lia.
fold P. replace (n + 32 * q + 31) with (P + 31) by (unfold P; lia).
rewrite (land_m32 (P + 31)) by lia. rewrite (land_m8a P) by lia.
assert (ERR2 : 32 * ((P + 31) / 32) = if r =? 0 then 32 * u else 32 * u + 32).
{ rewrite <- ERRv. unfold ap_rr. replace (32 * q + n + 31) with (P + 31) by (unfold P; lia). lia. }
assert (EPA2 : 8 * (P / 8) = 32 * u + 8 * (r / 8)).
{ rewrite EP. replace (32 * u + r) with (r + (4 * u) * 8) by lia. rewrite Z.div_add by lia. lia. }
rewrite ERR2, EPA2.
assert (EKM : P mod 8 = r mod 8).
{ rewrite EP. replace (32 * u + r) with (r + (4 * u) * 8) by lia. apply Z.mod_add. lia. }
assert (Hu : 0 <= u) by lia.
pose proof (ap_count u r Hu Hr) as CNT.
assert (EP31 : P + 31 = 32 * u + r + 31) by lia.

destruct (Z.eqb_spec r 0) as [R0|RN].
-
subst r. change (0 =? 0) with true in *. cbv iota in *. change (0 / 8) with 0 in *. replace (32 * u + 8 * 0) with (32 * u) in * by lia. rewrite ?Z.add_0_r in *.
zstep. ifT.
do 9 zstep. rewrite EP31, CNT.
do 8 zstep.
assert (E4u : (32 * u) ≫ 3 = 4 * u) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * u) with ((4 * u) * 8) by lia; apply Z.div_mul; lia).
rewrite E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
destruct (ap_stk_window _ _ _ (2147450880 + 4 * u) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (2147450880 + 4 * u) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (2147450880 + 4 * u) [CB (Z.to_nat 4) _] |- _ =>
pose proof (stk_of_rw_cells asegs mm _ _ H) as SHR'; cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op] in SHR'; change (Z.of_nat 4) with 4 in SHR' end.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SHR'|].
intros NZ. exfalso. apply NZ. rewrite EKM. reflexivity.
-
replace (r =? 0) with false in * by (symmetry; apply Z.eqb_neq; lia). cbv iota in *.
set (e := r / 8) in *. set (k := r mod 8).
assert (Erk : r = 8 * e + k /\ 0 <= k < 8 /\ 0 <= e <= 3) by (unfold e, k; pose proof (Z.div_mod r 8 ltac:(lia)); pose proof (Z.mod_pos_bound r 8 ltac:(lia)); split; [lia|]; split; [lia|]; split; [apply Z.div_pos; lia| assert (r / 8 < 4) by (apply Z.div_lt_upper_bound; lia); lia]).
clearbody e k. destruct Erk as (Erk & Hk & He).
assert (ESH3 : P ≫ 3 = 4 * u + e).
{ rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite EP, Erk. replace (32 * u + (8 * e + k)) with (k + (4 * u + e) * 8) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
assert (EL7 : Z.land P 7 = k).
{ change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite EP, Erk.
replace (32 * u + (8 * e + k)) with (k + (4 * u + e) * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (EKr : P mod 8 = k) by (rewrite EKM, Erk; replace (8 * e + k) with (k + e * 8) by lia; rewrite Z.mod_add by lia; apply Z.mod_small; lia).
assert (E4u : (32 * u + 32) ≫ 3 = 4 * u + 4) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; replace (32 * u + 32) with ((4 * u + 4) * 8) by lia; apply Z.div_mul; lia).
zstep. ifF.
do 8 zstep.
rewrite ?ESH3, ?EL7.
zstep. try ifF.
do 3 zstep.
remember (2147450880 + (4 * u + e)) as D eqn:ED.
replace (2147450880 + 4 * u + e) with D in * by lia.
replace (2147450880 + 4 * u + 4 + 4) with (D + (8 - e)) in * by lia.
assert (HD : 2147450880 <= D /\ D + 8 < 2^47) by lia.

Ltac ap_it_cb Da SHR jb BC :=
zstep; zstep; ifF; zstep; zstep; zstep;
destruct (ap_stk_window _ _ _ Da 1 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jb & BC) & SHR'); clear SHR; rename SHR' into SHR;
change (Z.to_nat 1) with 1%nat in BC;
zstep; rewrite le1_m53; mem_after_store; zstep; zstep.

Ltac ap_it_k Da SHR jb BC :=
zstep; zstep; ifT; zstep;
destruct (ap_stk_window _ _ _ Da 1 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jb & BC) & SHR'); clear SHR; rename SHR' into SHR;
change (Z.to_nat 1) with 1%nat in BC;
zstep; rewrite le1_small by lia; mem_after_store; zstep; zstep.

Ltac ap_tail2 EP31 CNT E4u :=
do 9 zstep; rewrite EP31, CNT; do 8 zstep; rewrite E4u.
assert (He4 : e = 0 \/ e = 1 \/ e = 2 \/ e = 3) by lia.
destruct (Z.eq_dec k 0) as [K0|KN]; destruct He4 as [ -> | [ -> | [ -> | -> ] ] ].
all: try (exfalso; lia).
+
ap_it_cb D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifF.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_it_cb (D + 2) SHR jb2 BC2.
zstep; ifT.
replace (D + 2 + 1) with (D + 3) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 3) by lia.
destruct (ap_stk_window _ _ _ (D + 3) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 3) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 7) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 3) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 3 + 4) with (D + 7) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm (D + 2) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 2) (D + 7) _ H ltac:(replace (D + 2 + 1) with (D + 3) by lia; exact SR) ltac:(lia)) as SR2 end. clear SR. rename SR2 into SR.
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 7) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 7) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros NZ. exfalso. apply NZ. rewrite EKr. exact K0.
+
ap_it_cb D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifT.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 2) by lia.
destruct (ap_stk_window _ _ _ (D + 2) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 2) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 6) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 2) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 2 + 4) with (D + 6) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 6) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 6) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros NZ. exfalso. apply NZ. rewrite EKr. exact K0.
+
ap_it_cb D SHR jb0 BC0.
zstep; ifT.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 1) by lia.
destruct (ap_stk_window _ _ _ (D + 1) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 1) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 5) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 1 + 4) with (D + 5) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 5) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros NZ. exfalso. apply NZ. rewrite EKr. exact K0.
+
ap_it_k D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifF.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_it_cb (D + 2) SHR jb2 BC2.
zstep; ifF.
replace (D + 2 + 1) with (D + 3) in SHR by lia.
ap_it_cb (D + 3) SHR jb3 BC3.
zstep; ifT.
replace (D + 3 + 1) with (D + 4) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 4) by lia.
destruct (ap_stk_window _ _ _ (D + 4) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 4) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 8) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 4) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 4 + 4) with (D + 8) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm (D + 3) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 3) (D + 8) _ H ltac:(replace (D + 3 + 1) with (D + 4) by lia; exact SR) ltac:(lia)) as SR3 end. clear SR. rename SR3 into SR.
lazymatch goal with H : rw_cells asegs ?mm (D + 2) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 2) (D + 8) _ H ltac:(replace (D + 2 + 1) with (D + 3) by lia; exact SR) ltac:(lia)) as SR2 end. clear SR. rename SR2 into SR.
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 8) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 8) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
+
ap_it_k D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifF.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_it_cb (D + 2) SHR jb2 BC2.
zstep; ifT.
replace (D + 2 + 1) with (D + 3) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 3) by lia.
destruct (ap_stk_window _ _ _ (D + 3) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 3) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 7) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 3) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 3 + 4) with (D + 7) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm (D + 2) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 2) (D + 7) _ H ltac:(replace (D + 2 + 1) with (D + 3) by lia; exact SR) ltac:(lia)) as SR2 end. clear SR. rename SR2 into SR.
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 7) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 7) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
+
ap_it_k D SHR jb0 BC0.
zstep; ifF.
ap_it_cb (D + 1) SHR jb1 BC1.
zstep; ifT.
replace (D + 1 + 1) with (D + 2) in SHR by lia.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 2) by lia.
destruct (ap_stk_window _ _ _ (D + 2) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 2) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 6) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 2) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 2 + 4) with (D + 6) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [C1 _] |- _ => pose proof (ap_stk_cons mm (D + 1) (D + 6) _ H ltac:(replace (D + 1 + 1) with (D + 2) by lia; exact SR) ltac:(lia)) as SR1 end. clear SR. rename SR1 into SR.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 6) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
+
ap_it_k D SHR jb0 BC0.
zstep; ifT.
ap_tail2 EP31 CNT E4u.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (2147450880 + (4 * u + 4)) with (D + 1) by lia.
destruct (ap_stk_window _ _ _ (D + 1) 4 SHR ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & (jR & RC) & _). clear SHR.
call (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (D + 1) 203 4 jR).
all: try eassumption; try lia.
apply evt_done. unfold alloca_poison_post. replace (32 * q + n) with P by (unfold P; lia). rewrite ESP, ESR.
replace (2147450880 + 4 * u + 4 + 4) with (D + 5) by lia.
do 16 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells asegs ?mm (D + 1) [CB (Z.to_nat 4) _] |- _ => pose proof (ap_stk_cb4 mm _ _ H) as SR end.
replace (D + 1 + 4) with (D + 5) in SR by lia.
lazymatch goal with H : rw_cells asegs ?mm D [C1 _] |- _ => pose proof (ap_stk_cons mm D (D + 5) _ H ltac:(exact SR) ltac:(lia)) as SR0 end. clear SR. rename SR0 into SR.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
split; [change 4%nat with (Z.to_nat 4); assumption|].
split; [exact SR|].
intros _. rewrite EKr. assumption.
Qed.
