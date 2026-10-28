(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hu X1nq. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g7 X1ff.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac ms_eq := cbv [mkR]; repeat first [ reflexivity | apply (f_equal (Z_to_bv 64)); lia | progress f_equal ].

Lemma swrap32_mod64_small : forall x c, -2^31 <= x + c < 2^31 ->
bv_swrap 32 (x mod 18446744073709551616 + c) = x + c.
Proof.
intros x c H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 / 2)%Z with 2147483648%Z.
replace (x mod 18446744073709551616) with (x - 18446744073709551616 * (x / 18446744073709551616))
by (pose proof (Z.div_mod x 18446744073709551616 ltac:(lia)); lia).
replace (x - 18446744073709551616 * (x / 18446744073709551616) + c + 2147483648)
with ((x + c + 2147483648) + (- 4294967296 * (x / 18446744073709551616)) * 4294967296) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma zbv_add_shl2m : forall a x y, a + 4 * x = y -> Z_to_bv 64 (a + Z.shiftl (x mod 18446744073709551616) 2) = Z_to_bv 64 y.
Proof.
intros a x y <-. change 18446744073709551616 with (2^64).
apply zbv_eqm. rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mod_eq x (2^64)) by lia.
replace (a + (x - 2^64 * (x / 2^64)) * 2^2) with ((a + 4 * x) + (- (4 * (x / 2^64))) * 2^64) by ring.
apply Z_mod_plus_full.
Qed.
Lemma lxs64_l : forall x, -2^63 <= x < 2^63 -> Z.lxor (x mod 18446744073709551616) 9223372036854775808 = x + 9223372036854775808.
Proof.
intros p Hp. change 9223372036854775808 with (2^63).
rewrite zb_lxor_sign by (split; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; lia).
change 18446744073709551616 with (2^64). rewrite Zplus_mod_idemp_l. apply Z.mod_small. lia.
Qed.
Lemma lxs64_nn : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof. intros x Hx. rewrite <- (lxs64_l x) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma swrap32_mod64_sub : forall x c, -2^31 <= x - c < 2^31 -> bv_swrap 32 (x mod 18446744073709551616 - c) = x - c.
Proof.
intros x c H. replace (x mod 18446744073709551616 - c) with (x mod 18446744073709551616 + (- c)) by ring.
rewrite swrap32_mod64_small by lia. ring.
Qed.
Lemma zbv_mod64_sub : forall x c, Z_to_bv 64 (x mod 18446744073709551616 - c) = Z_to_bv 64 (x - c).
Proof. intros. change 18446744073709551616 with (2^64). apply zbv_eqm. apply Zminus_mod_idemp_l. Qed.
Ltac sw32 := repeat first
[ match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 + ?c)] => rewrite (swrap32_mod64_small x c) by lia end
| match goal with |- context [bv_swrap 32 (?x mod 18446744073709551616 - ?c)] => rewrite (swrap32_mod64_sub x c) by lia end
| match goal with |- context [bv_swrap 32 ?x] => rewrite (swrap32_small x) by lia end
| match goal with |- context [Z_to_bv 64 (?x mod 18446744073709551616 - ?c)] => rewrite (zbv_mod64_sub x c) end ].

Ltac br_split K :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:K; [ | ]
end;
zify_cond K; rewrite ?signed_lit_small in K by lia.
Ltac brT := let K := fresh "Kbr" in br_split K; [ try clear K | exfalso; lia ].
Ltac brF := let K := fresh "Kbr" in br_split K; [ exfalso; lia | try clear K ].

Ltac shw := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC=" pc; idtac "REGS=" R | |- ?g => idtac "GOAL=" g end.

Section F.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

#[using="Type"] Lemma unpack_pair : forall b n, speex_bits_unpack_unsigned b n = (uv b n, ub b n).
Proof. intros. unfold uv, ub. destruct (speex_bits_unpack_unsigned b n); reflexivity. Qed.

#[using="Type"] Lemma p3_loop1 : forall (k : nat) (j EB e0 exc e32 pp tmp1 G gk ga cnt pa1 pa2 jv : Z) (neb : nat) (cur cur32 gs : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a3 a4 a7 s6 s7 s8 s9 s10 s11 t4 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = tmp1 - j -> 0 <= j < tmp1 -> tmp1 <= 40 -> tmp1 <= pp <= 145 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb -> 0 <= gk < 3 ->
0 < e32 -> e32 mod 4 = 0 -> EB mod 4 = 0 ->
ga = G + 4 * gk -> cnt = tmp1 - j -> pa1 = e32 + 4 * j -> pa2 = e32 + 4 * j -> jv = j ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
u32arr rsegs m1 G gs -> length gs = 3%nat ->
apart EB (4 * Z.of_nat neb) e32 160 -> apart G 12 e32 160 ->
munch [(e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xs6 xs7 xs9 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur32' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e32) a0 a1 (Z_to_bv 64 1) a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 1) a7
(Z_to_bv 64 exc) (Z_to_bv 64 0) (Z_to_bv 64 (e32 + 4 * tmp1)) (Z_to_bv 64 (e32 + 4 * tmp1)) xs6 xs7 s8 xs9 s10 s11
(Z_to_bv 64 pp) t4 (Z_to_bv 64 tmp1) (Z_to_bv 64 ga))
F2 (Z_to_bv 64 0x26e18) fc2 None m2 (seg_rom rsegs)
/\ munch [(e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 e32) a0 a1 (Z_to_bv 64 1) a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 1) a7
(Z_to_bv 64 exc) (Z_to_bv 64 cnt) (Z_to_bv 64 pa1) (Z_to_bv 64 pa2) s6 s7 s8 s9 s10 s11
(Z_to_bv 64 pp) t4 (Z_to_bv 64 jv) (Z_to_bv 64 ga))
F1 (Z_to_bv 64 0x26d9c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j EB e0 exc e32 pp tmp1 G gk ga cnt pa1 pa2 jv neb cur cur32 gs m0
ra sp gp tp t0 t1 t2 s0 a0 a1 a3 a4 a7 s6 s7 s8 s9 s10 s11 t4 F1 fc1 m1
Hk Hj Htmp Hpp He0 E0lo E0hi Hgk E32p E32m EBm -> -> -> -> -> EBA Lcur E32A L32 GA Lgs AP APG MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG.
unfold apart in AP, APG. subst exc.
zstep. if_false_z.
zstep. zstep. zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. zstep. rewrite (swrap32_small (j - pp)) by lia. if_false_z.
zstep. zstep. zstep.
rewrite !(swrap32_mod64_small (j - pp) 0) by lia.
rewrite (zbv_add_shl2m (EB + 4 * e0) (j - pp + 0) (EB + 4 * (e0 + j - pp))) by lia.
replace (Z_to_bv 64 (j - pp + 0)) with (Z_to_bv 64 (j - pp)) by (f_equal; lia).
zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. rewrite (lxs64_l (j - pp)) by lia. if_false_z.
zstep. if_false_z.
zstep. zstep. if_false_z.
pose proof (u32arr_read_nth rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as RD.
pose proof (u32arr_read_nth rsegs m1 G gs gk _ GA ltac:(lia) eq_refl) as RD'.
pose proof (u32arr_read_nth rsegs m1 EB cur (e0 + j - pp) _ EBA ltac:(lia) eq_refl) as RD''.
zstep. zstep. zstep. clear RD RD' RD''.
zstep. rewrite (swrap32_small (j + 1)) by lia.
zstep. zstep. zstep.
pose proof (u32arr_store_ok rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 e32 cur32 j v E32A ltac:(lia)) as E32A' end.
clear E32A. store_done. try clear SOK.
zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (j + 1) EB e0 (EB + 4 * e0) e32 pp tmp1 G gk _ _ _ _ _ neb _ _ gs m0); try eassumption; try lia.
rewrite upd_length; exact L32.
- apply evt_done.
sf_eexists 7%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact L32.
Qed.

#[using="Type"] Lemma p3_loop2 : forall (k : nat) (j EB e0 exc e32 pp pitch tmp3 G gk ga j1 j2 pa pb : Z) (neb : nat) (cur cur32 gs : list word) (m0 : mem)
(ra sp gp tp t0 s0 a0 a1 a3 a4 a7 s4 s5 s6 s7 s9 s10 s11 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = tmp3 - j -> 0 <= j < tmp3 -> tmp3 <= 40 -> tmp3 <= pp + pitch -> 0 <= pp <= 145 -> 0 <= pitch <= 144 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb -> 0 <= gk < 3 ->
0 < e32 -> e32 mod 4 = 0 -> EB mod 4 = 0 ->
ga = G + 4 * gk -> j1 = j -> j2 = j -> pa = e32 + 4 * j -> pb = e32 + 4 * j ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
u32arr rsegs m1 G gs -> length gs = 3%nat ->
apart EB (4 * Z.of_nat neb) e32 160 -> apart G 12 e32 160 ->
munch [(e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xs4 xs5 xs6 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur32' : list word),
ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 tmp3) (Z_to_bv 64 tmp3) s0 (Z_to_bv 64 e32) a0 a1 (Z_to_bv 64 1) a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 1) a7
(Z_to_bv 64 exc) (Z_to_bv 64 (e32 + 4 * tmp3)) xs4 xs5 xs6 s7 (Z_to_bv 64 pitch) s9 s10 s11
(Z_to_bv 64 pp) (Z_to_bv 64 ga) (Z_to_bv 64 tmp3) (Z_to_bv 64 (e32 + 4 * tmp3)))
F2 (Z_to_bv 64 0x26ee4) fc2 None m2 (seg_rom rsegs)
/\ munch [(e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp t0 (Z_to_bv 64 j1) (Z_to_bv 64 j2) s0 (Z_to_bv 64 e32) a0 a1 (Z_to_bv 64 1) a3 a4 (Z_to_bv 64 1) (Z_to_bv 64 1) a7
(Z_to_bv 64 exc) (Z_to_bv 64 pb) s4 s5 s6 s7 (Z_to_bv 64 pitch) s9 s10 s11
(Z_to_bv 64 pp) (Z_to_bv 64 ga) (Z_to_bv 64 tmp3) (Z_to_bv 64 pa))
F1 (Z_to_bv 64 0x26e4c) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j EB e0 exc e32 pp pitch tmp3 G gk ga j1 j2 pa pb neb cur cur32 gs m0
ra sp gp tp t0 s0 a0 a1 a3 a4 a7 s4 s5 s6 s7 s9 s10 s11 F1 fc1 m1
Hk Hj Htmp Htp Hpp Hpi He0 E0lo E0hi Hgk E32p E32m EBm -> -> -> -> -> EBA Lcur E32A L32 GA Lgs AP APG MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG.
unfold apart in AP, APG. subst exc.
zstep. zstep. if_false_z.
zstep. zstep. rewrite (lxs64_nn j) by lia. zstep. zstep. zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. zstep. sw32. if_false_z.
zstep. sw32.
zstep. zstep. zstep. sw32. if_false_z.
zstep. sw32. zstep. zstep.
lazymatch goal with |- context [Z_to_bv 64 (EB + 4 * e0 + Z.shiftl (?x mod 18446744073709551616) 2)] =>
rewrite (zbv_add_shl2m (EB + 4 * e0) x (EB + 4 * (e0 + j - pp - pitch))) by lia end.
zstep. zstep. if_false_z.
zstep. zstep. rewrite lxs64_l by lia. zstep. zstep. zstep. if_false_z.
zstep. if_false_z.
zstep. zstep. if_false_z.
pose proof (u32arr_read_nth rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as RD.
pose proof (u32arr_read_nth rsegs m1 G gs gk _ GA ltac:(lia) eq_refl) as RD'.
pose proof (u32arr_read_nth rsegs m1 EB cur (e0 + j - pp - pitch) _ EBA ltac:(lia) eq_refl) as RD''.
zstep. zstep. zstep. clear RD RD' RD''.
zstep. zstep. sw32. zstep.
pose proof (u32arr_store_ok rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 e32 cur32 j v E32A ltac:(lia)) as E32A' end.
clear E32A. store_done. try clear SOK.
zstep. zstep.
zstep. if_cases K; zify_cond K; rewrite ?signed_lit_small in K by lia.
- eapply (IH (j + 1) EB e0 (EB + 4 * e0) e32 pp pitch tmp3 G gk _ _ _ _ _ neb _ _ gs m0); try eassumption; try lia.
rewrite upd_length; exact L32.
- apply evt_done.
sf_eexists 7%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact L32.
Qed.

#[using="Type"] Lemma zext32_x4 : forall x, 0 <= x < 2^30 -> Z.shiftr (Z.shiftl x 32) 30 = x * 4.
Proof.
intros x Hx. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
replace (2^32) with (4 * 2^30) by reflexivity. rewrite Z.mul_assoc. apply Z.div_mul. lia.
Qed.
#[using="Type"] Lemma zext32_x4_mod : forall x, 0 <= x < 2^30 -> Z.shiftr ((Z.shiftl x 32) mod 2^64) 30 = x * 4.
Proof. intros x Hx. rewrite Z.mod_small; [apply zext32_x4; lia|]. rewrite Z.shiftl_mul_pow2 by lia.
change (2^64) with (2^32 * 2^32). change (2^30) with 1073741824 in Hx. change (2^32) with 4294967296. lia. Qed.
#[using="Type"] Lemma zext32_id : forall x, 0 <= x < 2^32 -> Z.shiftr (Z.shiftl x 32) 32 = x.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. apply Z.div_mul. lia. Qed.
#[using="Type"] Lemma zext32_id_mod : forall x, 0 <= x < 2^32 -> Z.shiftr ((Z.shiftl x 32) mod 2^64) 32 = x.
Proof. intros x Hx. rewrite zb_shl_shr by lia. change (64 - 32) with 32. apply Z.mod_small. lia. Qed.

#[using="Type"] Lemma zext32_x4_mul : forall x, 0 <= x -> Z.shiftr (x * 4294967296) 30 = x * 4.
Proof.
intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change 4294967296 with (4 * 2^30).
rewrite Z.mul_assoc. apply Z.div_mul. lia.
Qed.
#[using="Type"] Lemma zext32_x4_mul_mod : forall x, 0 <= x < 2^30 -> Z.shiftr ((x * 4294967296) mod 18446744073709551616) 30 = x * 4.
Proof.
intros x Hx. rewrite Z.mod_small; [apply zext32_x4_mul; lia|].
change (2^30) with 1073741824 in Hx. lia.
Qed.
Ltac zx4 := first [ rewrite zext32_x4_mul by lia | rewrite zext32_x4_mul_mod by lia | rewrite zext32_x4 by lia | rewrite zext32_x4_mod by lia ].
Ltac shl2 := rewrite ?Z.shiftl_mul_pow2 by lia; change (2^2) with 4.

#[using="Type"] Lemma p3_iter : forall (i EB e0 exc e32 G pitch pp na0 : Z) (neb : nat) (cur cur32 gs : list word) (m0 : mem)
(ra sp gp tp t1 t2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
0 <= i < 3 -> 17 <= pitch <= 144 -> pp = pitch + 1 - i -> na0 = pitch + 1 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb ->
0 < e32 -> e32 mod 4 = 0 -> EB mod 4 = 0 ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
u32arr rsegs m1 G gs -> length gs = 3%nat ->
apart EB (4 * Z.of_nat neb) e32 160 -> apart G 12 e32 160 ->
munch [(e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xt1 xt2 xs3 xs4 xs5 xs6 xs7 xs9 xt3 xt4 xt5 xt6 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur32' : list word),
ms' = MS (mkR ra sp gp tp (Z_to_bv 64 pp) xt1 xt2 (Z_to_bv 64 40) (Z_to_bv 64 e32) (Z_to_bv 64 na0) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2)
(Z_to_bv 64 G) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 3)
(Z_to_bv 64 exc) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 pitch) xs9 s10 s11 xt3 xt4 xt5 xt6)
F2 (Z_to_bv 64 0x26ee4) fc2 None m2 (seg_rom rsegs)
/\ munch [(e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp (Z_to_bv 64 pp) t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) (Z_to_bv 64 na0) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 2)
(Z_to_bv 64 G) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 3)
(Z_to_bv 64 exc) s3 s4 s5 s6 s7 (Z_to_bv 64 pitch) s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x26d48) fc1 None m1 (seg_rom rsegs)).
Proof.
intros until m1. intros Hi Hp -> -> He0 E0lo E0hi E32p E32m EBm EBA Lcur E32A L32 GA Lgs AP1 AP2 MU WM MI FRM.
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG.
pose proof AP1 as AP1u. pose proof AP2 as AP2u. unfold apart in AP1u, AP2u. subst exc.
destruct (Z_lt_le_dec 40 (pitch + 1 - i)) as [LT|GE].
- zstep. zstep. brT. zstep. zstep. brT.
zstep. sw32. zstep. sw32. zstep. zstep. sw32. if_false_z.
zstep. zstep. brT. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. zstep. shl2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_loop1 40%nat 0 EB e0 _ e32 _ 40 G (2 - i) _ _ _ _ _ neb cur cur32 gs mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32B; rename L into L32B end.
zstep. zstep. sw32. zstep. if_false_z. zstep. sw32. zstep. zstep. brT. zstep. brT.
apply evt_done. sf_eexists 16%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
- zstep. zstep. brF. zstep. zstep. zstep. brF. zstep.
zstep. sw32. zstep. sw32. zstep. zstep. sw32. if_false_z.
zstep. zstep. brF. zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. zstep. shl2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_loop1 (Z.to_nat (pitch + 1 - i)) 0 EB e0 _ e32 _ (pitch + 1 - i) G (2 - i) _ _ _ _ _ neb cur cur32 gs mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32B; rename L into L32B end.
zstep. zstep. sw32. zstep. if_false_z. zstep. sw32. zstep. zstep.
assert (CS : pitch + 1 - i = 40 \/ (pitch + 1 - i < 40 /\ 40 < 2 * pitch + 1 - i) \/ 2 * pitch + 1 - i <= 40) by lia.
destruct CS as [CE | [CC | CD]].
+ brT. zstep. brT.
apply evt_done. sf_eexists 16%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
+ brT. zstep. brF.
zstep. zstep. zstep. zstep. zstep. shl2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL2; pose proof (wmono_refl rsegs mc) as WML2;
call (p3_loop2 (Z.to_nat (40 - (pitch + 1 - i))) (pitch + 1 - i) EB e0 _ e32 _ _ 40 G (2 - i) _ _ _ _ _ neb cur _ gs mc) end.
all: try lia. all: try exact MUL2. all: try exact WML2. all: try eassumption.
clear MUL2 WML2. try rename MI0 into MI.
apply evt_done. sf_eexists 16%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
+ brF. zstep. zstep. brF.
zstep. zstep. zstep. zstep. zstep. shl2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL2; pose proof (wmono_refl rsegs mc) as WML2;
call (p3_loop2 (Z.to_nat pitch) (pitch + 1 - i) EB e0 _ e32 _ _ (pitch + 1 - i + pitch) G (2 - i) _ _ _ _ _ neb cur _ gs mc) end.
all: try lia. all: try exact MUL2. all: try exact WML2. all: try eassumption.
clear MUL2 WML2. try rename MI0 into MI.
apply evt_done. sf_eexists 16%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
Qed.

Definition cdbk_bytes (base : Z) (n : nat) : list byte :=
match image_bytes rsegs base n with Some bs => bs | None => [] end.
#[using="Type"] Lemma cdbk_ro : forall m base n, mem_inv rsegs m ->
ro_bytes_b rsegs base (cdbk_bytes base n) = true -> 0 <= base -> base + Z.of_nat (length (cdbk_bytes base n)) <= 2^64 ->
u8ro rsegs m base (cdbk_bytes base n).
Proof.
intros m base n MI RB H0 HL. unfold u8ro.
pose proof (ro_cells_bytes_at rsegs m base _ (ro_cells_image rsegs m base _ MI RB H0 HL)) as BY.
cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. exact BY.
Qed.
#[using="Type"] Lemma gain_cdbk_ro : forall g m, mem_inv rsegs m ->
exists CD, u8ro rsegs m (gain_cdbk_addr g) CD /\ Z.of_nat (length CD) = gain_cdbk_size g.
Proof.
intros [|] m MI; cbn [gain_cdbk_addr gain_cdbk_size].
- exists (cdbk_bytes 0x12588 512). assert (L : length (cdbk_bytes 0x12588 512) = 512%nat) by (vm_compute; reflexivity).
split; [| rewrite L; reflexivity]. apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].
- exists (cdbk_bytes 0x11f28 128). assert (L : length (cdbk_bytes 0x11f28 128) = 128%nat) by (vm_compute; reflexivity).
split; [| rewrite L; reflexivity]. apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].
Qed.
#[using="Type"] Lemma gain_cdbk_addr_range : forall g, 0x10000 <= gain_cdbk_addr g /\ gain_cdbk_addr g + gain_cdbk_size g <= 0x1b000.
Proof. intros [|]; cbn; lia. Qed.

Definition pmemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A n c : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(A, A + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
#[using="Type"] Lemma pmemset_specZ : forall (A n c : Z) (junk : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
rw_cells rsegs m A [CB (Z.to_nat n) junk] ->
mem_inv rsegs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
(0 <= c < 256)%Z -> (0 <= n < 2^64)%Z -> (A < 2^64)%Z ->
evt rsegs (pmemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n c m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3a1dc) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros DST MI -> -> -> Hc Hn Hl.
pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
assert (Ec : (bv_unsigned (Z_to_bv 64 c) mod 256 = c)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
eapply evt_mono. { eapply memset_spec; [|exact MI]. rewrite EA, En. exact DST. }
intros ms' PO. unfold memset_post in PO. rewrite EA, En, Ec in PO. exact PO.
Qed.

#[using="Type"] Lemma u32s_zero40 : repeat (Z_to_bv 8 0) (Z.to_nat 160) = u32s (repeat (Z_to_bv 64 0) 40).
Proof. vm_compute. reflexivity. Qed.

Ltac rebits R A D bb rj Lrj OBJ bs DAT Hbs SIDE :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (R : bits_rep rsegs mc A D bb)
by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE]]);
clear OBJ DAT
end.
Ltac after_unpack b0 bb n rj Lrj OBJ bs DAT Hbs SIDE OKp OKn Hv Lbs :=
try rename MI0 into MI; rewrite (unpack_pair bb n) in *; cbn [fst snd] in *;
lazymatch goal with H : bits_rep _ _ _ _ (ub bb n) |- _ =>
destruct H as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE); unfold bits_cells in OBJ end;
lazymatch goal with H : ?v = Z_to_bv 64 (uv bb n) |- _ => subst v end;
pose proof (speex_bits_unpack_unsigned_ok bb n _ _ OKp ltac:(lia) (unpack_pair bb n)) as (OKn & Hv & _);
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b0)
by (let X := fresh in pose proof OKn as X; unfold bits_ok in X; rewrite Hbs, zlength_map_unsigned, ?ub_size in X; lia).

End F.
