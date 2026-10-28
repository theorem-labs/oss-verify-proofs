(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFHW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFHW.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAa.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.

Module GwI.
Definition segs := rsegs.
Definition base := 0x58050%Z.
Definition w_17 := 0xfffbb517%Z.
Definition w_18 := 0x3ec53507%Z.
Definition hi_17 := (Z_to_bv 20 1048507).
Definition lo_18 := (Z_to_bv 12 1004).
Definition lo_20 := (Z_to_bv 12 0).
Definition G_107d0 := 0x13480%Z.
Definition G_10d38 := 0x132a6%Z.
Lemma CODE : CodeAt.code_at rsegs 0x58050 (QQLG.Mq6.frexpl_code 0xfffbb517%Z 0x3ec53507%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x58050 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x58050 /\ 0x58050 + 216 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition lo64_words := @lo64_words.
Definition hi64_words := @hi64_words.
Definition letf2_spec := @letf2_spec.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_2 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_3 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_4 := zsimp_fast.

Definition frexpl_entry := 0x58050%Z.
Lemma gw_eq_frexpl_entry : @frexpl_entry = ltac:(GwInst.gw_term (@QQLG.Mq6.frexpl_entry 0x58050) (@frexpl_entry)). Proof. unfold frexpl_entry, QQLG.Mq6.frexpl_entry; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_frexpl_entry : gw_eqs.

Lemma frexpl_unfold : forall n x e,
frexpl (S n) x e =
(let hi := hi64 x in
let se := Z.shiftr hi 48 in
let ee := Z.land se 0x7fff in
if ee =? 0 then
if negb (f128_le x F128_ZERO =? 0) then
let k := f128_of_d D_0x1p120 in
match frexpl n (f128_mul x k) e with Some (x, e) => Some (x, e - 120) | None => None end
else Some (x, 0)
else if ee =? 0x7fff then Some (x, e)
else
let e := ee - 0x3ffe in
let hi := Z.lor (Z.lor (Z.land hi 0x8000000000000000) (Z.land hi 0x0000ffffffffffff)) 0x3ffe000000000000 in
Some (mk128 hi (lo64 x), e))%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq6.frexpl_unfold). Qed.

Definition frexpl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P x E : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (P, P + 4)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 32) (bv_unsigned sp)
/\ rw_cells rsegs m' P [C4 (Z_to_bv 64 e')]
/\ frexpl FREXPL_FUEL x E = Some (x', e').
Lemma gw_eq_frexpl_post : @frexpl_post = ltac:(GwInst.gw_term (@QQLG.Mq6.frexpl_post rsegs) (@frexpl_post)). Proof. unfold frexpl_post, QQLG.Mq6.frexpl_post; autorewrite with gw_eqs; reflexivity. Qed.
#[export] Hint Rewrite gw_eq_frexpl_post : gw_eqs.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
Lemma frx_mant : ltac2:(Q6nq.tyx '(@QQLG.Mq6.frx_mant) [[@gw_eq_frexpl_entry__3; @gw_eq_frexpl_entry__2; @gw_eq_frexpl_entry]; [@gw_eq_frexpl_post__3; @gw_eq_frexpl_post__2; @gw_eq_frexpl_post]] '([18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) gwt_X))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq6.frx_mant). Qed.
Lemma frx_sign : ltac2:(Q6nq.tyx '(@QQLG.Mq6.frx_sign) [[@gw_eq_frexpl_entry__3; @gw_eq_frexpl_entry__2; @gw_eq_frexpl_entry]; [@gw_eq_frexpl_post__3; @gw_eq_frexpl_post__2; @gw_eq_frexpl_post]] '([32768; 18446744073709551615]%Z : list Z) '(Q6nq.gwt_unf (@ONES64) (Q6nq.gwt_unf (@MASKLO) gwt_X))).
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq6.frx_sign). Qed.

Ltac frx_finish X E' :=
apply evt_done; unfold frexpl_post; exists X, E';
repeat (lazymatch goal with |- ex _ => eexists end);
split; [ rewrite ?lo64_mk128, ?hi64_mk128 by zrange; rewrite ?lo64_words, ?hi64_words by lia; ms_eq
| repeat match goal with |- _ /\ _ => split end; try assumption ].

Lemma f128_le_cases : forall a b, (f128_le a b = -1 \/ f128_le a b = 0 \/ f128_le a b = 1)%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq6.f128_le_cases). Qed.
Lemma f128_le_land64_zero : forall a b, Z.land (f128_le a b) 18446744073709551615 = 0%Z <-> f128_le a b = 0%Z.
Proof. autorewrite with gw_eqs; GwInst.gw_exact (@QQLG.Mq6.f128_le_land64_zero). Qed.

Lemma frexpl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (E : Z),
stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp) ->
mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned a2) [C4 (Z_to_bv 64 E)] ->
(bv_unsigned a2 + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
(32 <= bv_unsigned sp)%Z ->
(let x := (bv_unsigned a0 + 2^64 * bv_unsigned a1)%Z in
Z.land (Z.shiftr (hi64 x) 48) 0x7fff <> 0%Z \/ f128_le x F128_ZERO = 0%Z) ->
evt rsegs (frexpl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a2) (bv_unsigned a0 + 2^64 * bv_unsigned a1) E m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x58050) fc None m (seg_rom rsegs)).
Proof. autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QQLG.Mq6.frexpl_spec). Qed.
