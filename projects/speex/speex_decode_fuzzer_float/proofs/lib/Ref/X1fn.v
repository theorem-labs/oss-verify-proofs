(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hu X1nq X1nr X1g7 X1ff.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
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

#[using="Type"] Lemma p3_loop1 : forall (k : nat) (j EB e0 exc e32 pp tmp1 p5 p6 pend : Z) (neb : nat) (cur cur32 : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = tmp1 - j -> 0 <= j < tmp1 -> tmp1 <= 40 -> 1 <= pp <= 290 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb ->
p5 = exc - 4 * pp + 4 * j -> p6 = e32 + 4 * j -> pend = exc - 4 * pp + 4 * tmp1 ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
apart EB (4 * Z.of_nat neb) e32 160 ->
munch [(e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur32' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
(Z_to_bv 64 pend) (Z_to_bv 64 pend) (Z_to_bv 64 (e32 + 4 * tmp1)))
F2 (Z_to_bv 64 0x22e14) fc2 None m2 (seg_rom rsegs)
/\ munch [(e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3
(Z_to_bv 64 pend) (Z_to_bv 64 p5) (Z_to_bv 64 p6))
F1 (Z_to_bv 64 0x22df8) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j EB e0 exc e32 pp tmp1 p5 p6 pend neb cur cur32 m0
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 F1 fc1 m1
Hk Hj Htmp Hpp He0 E0lo E0hi -> -> -> EBA Lcur E32A L32 AP MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
unfold apart in AP. subst exc.
pose proof (u32arr_read_nth rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as RD.
pose proof (u32arr_read_nth rsegs m1 EB cur (e0 - pp + j) _ EBA ltac:(lia) ltac:(f_equal; lia)) as RD'.
zstep. zstep. clear RD RD'.
zstep. zstep.
pose proof (u32arr_store_ok rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 e32 cur32 j v E32A ltac:(lia)) as E32A' end.
clear E32A. store_done. try clear SOK.
zstep.
zstep. if_cases K; zify_cond K.
- eapply (IH (j + 1) EB e0 (EB + 4 * e0) e32 pp tmp1 _ _ _ neb _ _ m0); try eassumption; try lia.
rewrite upd_length; exact L32.
- apply evt_done.
sf_eexists 4%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. rewrite upd_length; exact L32.
Qed.

#[using="Type"] Lemma p3_loop2 : forall (k : nat) (j EB e0 exc e32 ppp tmp3 q p2 pend : Z) (neb : nat) (cur cur32 : list word) (m0 : mem)
(ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
Z.of_nat k = tmp3 - j -> 0 <= j < tmp3 -> tmp3 <= 40 -> tmp3 <= ppp <= 290 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb ->
q = j - ppp -> p2 = e32 + 4 * j -> pend = e32 + 4 * tmp3 ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
apart EB (4 * Z.of_nat neb) e32 160 ->
munch [(e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xt0 xt3 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur32' : list word),
ms' = MS (mkR ra sp gp tp xt0 (Z_to_bv 64 pend) (Z_to_bv 64 pend) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 exc) s3 s4 s5 s6 s7 s8 s9 s10 s11
xt3 t4 t5 t6)
F2 (Z_to_bv 64 0x22e6c) fc2 None m2 (seg_rom rsegs)
/\ munch [(e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp (Z_to_bv 64 q) (Z_to_bv 64 pend) (Z_to_bv 64 p2) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 exc) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x22e48) fc1 None m1 (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros j EB e0 exc e32 ppp tmp3 q p2 pend neb cur cur32 m0
ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F1 fc1 m1
Hk Hj Htmp Hppp He0 E0lo E0hi -> -> -> EBA Lcur E32A L32 AP MU WM MI FRM; [lia|].
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
unfold apart in AP. subst exc.
pose proof (u32arr_read_nth rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as RD.
zstep. clear RD.
zstep. rewrite zbv_shl2_mod64.
zstep. rewrite ?zbv_add_mod64_r, ?zbv_add_mod64_l.
replace (Z_to_bv 64 (EB + 4 * e0 + (j - ppp) * 4)) with (Z_to_bv 64 (EB + 4 * (e0 + j - ppp))) by (f_equal; lia).
pose proof (u32arr_read_nth rsegs m1 EB cur (e0 + j - ppp) _ EBA ltac:(lia) eq_refl) as RD'.
zstep. clear RD'.
zstep.
pose proof (u32arr_store_ok rsegs m1 e32 cur32 j _ E32A ltac:(lia) eq_refl) as SOK.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?v)) _) =>
pose proof (u32arr_write rsegs m1 e32 cur32 j v E32A ltac:(lia)) as E32A' end.
clear E32A. store_done. try clear SOK.
zstep.
zstep. first [ rewrite (swrap32_mod64_small (j - ppp) 1) by lia | rewrite swrap32_small by lia ].
zstep. if_cases K; zify_cond K.
- eapply (IH (j + 1) EB e0 (EB + 4 * e0) e32 ppp tmp3 _ _ _ neb _ _ m0); try eassumption; try lia.
rewrite upd_length; exact L32.
- apply evt_done.
sf_eexists 6%nat. split; [ms_eq|].
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

#[using="Type"] Lemma p3_iter : forall (i EB e0 exc e32 G pitch na1 na4 na5 pp : Z) (neb : nat) (cur cur32 gs : list word) (m0 : mem)
(ra sp gp tp t0 t1 t2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
(F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
0 <= i < 3 -> 17 <= pitch <= 144 -> na4 = i - 2 * pitch - 1 -> pp = pitch + 1 - i -> na1 = pitch + 1 -> na5 = 2 * pitch + 1 ->
exc = EB + 4 * e0 -> 290 <= e0 -> e0 + 40 <= Z.of_nat neb ->
u32arr rsegs m1 EB cur -> length cur = neb -> u32arr rsegs m1 e32 cur32 -> length cur32 = 40%nat ->
u32arr rsegs m1 G gs -> length gs = 3%nat ->
apart EB (4 * Z.of_nat neb) e32 160 -> apart G 12 e32 160 ->
munch [(e32, e32 + 160)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> frm0 fc1 ->
evt rsegs (fun ms' => exists (xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (F2 : bvmap 5 word) (fc2 : bv 32) (m2 : mem) (cur32' : list word),
ms' = MS (mkR ra sp gp tp xt0 xt1 xt2 (Z_to_bv 64 40) (Z_to_bv 64 e32) (Z_to_bv 64 i) (Z_to_bv 64 na1) (Z_to_bv 64 2)
(Z_to_bv 64 G) (Z_to_bv 64 na4) (Z_to_bv 64 na5) (Z_to_bv 64 3) (Z_to_bv 64 pp)
(Z_to_bv 64 exc) s3 s4 s5 s6 s7 (Z_to_bv 64 pitch) s9 s10 s11 xt3 xt4 xt5 xt6)
F2 (Z_to_bv 64 0x22e6c) fc2 None m2 (seg_rom rsegs)
/\ munch [(e32, e32 + 160)] m0 m2 /\ wmono rsegs m0 m2 /\ mem_inv rsegs m2
/\ frm0 fc2 /\ u32arr rsegs m2 e32 cur32' /\ length cur32' = 40%nat)
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 40) (Z_to_bv 64 e32) (Z_to_bv 64 i) (Z_to_bv 64 na1) (Z_to_bv 64 2)
(Z_to_bv 64 G) (Z_to_bv 64 na4) (Z_to_bv 64 na5) (Z_to_bv 64 3) (Z_to_bv 64 pp)
(Z_to_bv 64 exc) s3 s4 s5 s6 s7 (Z_to_bv 64 pitch) s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x22d90) fc1 None m1 (seg_rom rsegs)).
Proof.
intros until m1. intros Hi Hp -> -> -> -> He0 E0lo E0hi EBA Lcur E32A L32 GA Lgs AP1 AP2 MU WM MI FRM.
pose proof (u32arr_bound _ _ _ _ EBA) as BE. rewrite Lcur in BE.
pose proof (u32arr_bound _ _ _ _ E32A) as B32. rewrite L32 in B32.
pose proof (u32arr_bound _ _ _ _ GA) as BG. rewrite Lgs in BG.
pose proof E32A as E32A0. pose proof GA as GA0. unfold apart in AP2.

assert (CASES : 40 < pitch + 1 - i \/ pitch + 1 - i = 40 \/ (pitch + 1 - i < 40 /\ 40 < 2 * pitch + 1 - i) \/ 2 * pitch + 1 - i <= 40) by lia.

destruct CASES as [CA | [CB1 | [CB2 | CC]]].
-
zstep. nswrap. zstep. zstep. brT.
zstep. zstep. brT.
zstep. zstep. brT.
zstep. nswrap. zstep. zstep. brT.
zstep. zstep. if_false_x.
zstep. zstep. shl2. zstep. shl2. zstep. try zx4. zstep.
pose proof (u32arr_read_nth rsegs m1 G gs (2 - i) _ GA ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD.
zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_loop1 40%nat 0 EB e0 exc e32 (pitch + 1 - i) (40) _ _ _ neb cur cur32 mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32B; rename L into L32B end.

zstep. nswrap. zstep. zstep. brT. zstep. brT.
apply evt_done. sf_eexists 11%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
-
zstep. nswrap. zstep. zstep. brT.
zstep. zstep. brF. zstep.
zstep. zstep. brF. zstep.
zstep. nswrap. zstep. zstep. brF. zstep.
zstep. zstep. if_false_x.
zstep. zstep. shl2. zstep. shl2. zstep. try zx4. zstep.
pose proof (u32arr_read_nth rsegs m1 G gs (2 - i) _ GA ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD.
zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_loop1 (Z.to_nat (pitch + 1 - i)) 0 EB e0 exc e32 (pitch + 1 - i) (pitch + 1 - i) _ _ _ neb cur cur32 mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32B; rename L into L32B end.
zstep. nswrap. zstep. zstep. brT. zstep. brT.
apply evt_done. sf_eexists 11%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
-
destruct CB2 as [CB2 CB3].
zstep. nswrap. zstep. zstep. brT.
zstep. zstep. brF. zstep.
zstep. zstep. brF. zstep.
zstep. nswrap. zstep. zstep. brF. zstep.
zstep. zstep. if_false_x.
zstep. zstep. shl2. zstep. shl2. zstep. try zx4. zstep.
pose proof (u32arr_read_nth rsegs m1 G gs (2 - i) _ GA ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD.
zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_loop1 (Z.to_nat (pitch + 1 - i)) 0 EB e0 exc e32 (pitch + 1 - i) (pitch + 1 - i) _ _ _ neb cur cur32 mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32B; rename L into L32B end.
zstep. nswrap. zstep. zstep. brT. zstep. brF.

zstep. try shl2. zstep. shl2. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u32arr_read_nth rsegs mc G gs (2 - i) _ GA ltac:(lia) ltac:(f_equal; lia)) as RD end.
zstep. clear RD.
zstep. shl2. zstep.
zstep. first [ rewrite (swrap32_mod64_small (i - 2 * pitch - 1)) by lia | nswrap ].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL2; pose proof (wmono_refl rsegs mc) as WML2;
call (p3_loop2 (Z.to_nat (40 - (pitch + 1 - i))) (pitch + 1 - i) EB e0 exc e32 (pitch + 1 - i + pitch) (40) _ _ _ neb cur _ mc) end.
all: try lia. all: try exact MUL2. all: try exact WML2. all: try eassumption.
clear MUL2 WML2. try rename MI0 into MI.
apply evt_done. sf_eexists 11%nat. split; [ms_eq|].
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eassumption|]. assumption.
-
zstep. nswrap. zstep. zstep. brF. zstep.
zstep. zstep. brF. zstep.
zstep. zstep. brF. zstep.
zstep. nswrap. zstep. zstep. brF. zstep.
zstep. zstep. if_false_x.
zstep. zstep. shl2. zstep. shl2. zstep. try zx4. zstep.
pose proof (u32arr_read_nth rsegs m1 G gs (2 - i) _ GA ltac:(lia) ltac:(f_equal; lia)) as RD. zstep. clear RD.
zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (p3_loop1 (Z.to_nat (pitch + 1 - i)) 0 EB e0 exc e32 (pitch + 1 - i) (pitch + 1 - i) _ _ _ neb cur cur32 mc) end.
all: try lia. all: try exact MUL. all: try exact WML. all: try eassumption.
clear MUL WML. try rename MI0 into MI.
match goal with H : u32arr rsegs _ e32 ?c, L : length ?c = 40%nat |- _ => rename H into E32B; rename L into L32B end.
zstep. nswrap. zstep. zstep. brF. zstep. zstep. brF.

zstep. try shl2. zstep. shl2. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u32arr_read_nth rsegs mc G gs (2 - i) _ GA ltac:(lia) ltac:(f_equal; lia)) as RD end.
zstep. clear RD.
zstep. shl2. zstep.
zstep. first [ rewrite (swrap32_mod64_small (i - 2 * pitch - 1)) by lia | nswrap ].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(e32, e32 + 160)] mc) as MUL2; pose proof (wmono_refl rsegs mc) as WML2;
call (p3_loop2 (Z.to_nat pitch) (pitch + 1 - i) EB e0 exc e32 (pitch + 1 - i + pitch) (pitch + 1 - i + pitch) _ _ _ neb cur _ mc) end.
all: try lia. all: try exact MUL2. all: try exact WML2. all: try eassumption.
clear MUL2 WML2. try rename MI0 into MI.
apply evt_done. sf_eexists 11%nat. split; [ms_eq|].
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
- exists (cdbk_bytes 0x12590 512). assert (L : length (cdbk_bytes 0x12590 512) = 512%nat) by (vm_compute; reflexivity).
split; [| rewrite L; reflexivity]. apply cdbk_ro; [exact MI| vm_compute; reflexivity| lia| rewrite L; lia].
- exists (cdbk_bytes 0x11f30 128). assert (L : length (cdbk_bytes 0x11f30 128) = 128%nat) by (vm_compute; reflexivity).
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
F (Z_to_bv 64 0x32ccc) fc None m (seg_rom rsegs)).
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
