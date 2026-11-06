(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg Lib.SepCache QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QgoP Q7UD Qwm6 QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QgoP.
Import Q7UD Qwm6.
Import Qwm6.Mq0 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Section Models.
Variable stop : byte -> byte -> bool.
Variable value : byte -> byte -> Z.

Fixpoint icmp_walk (l r : list byte) (k : nat) {struct k} : option (nat * Z) :=
match k with
| O => Some (O, 0)
| S k' =>
match l, r with
| a :: l', b :: r' =>
if stop a b then Some (1%nat, value a b)
else match icmp_walk l' r' k' with
| Some (j, v) => Some (S j, v)
| None => None
end
| _, _ => None
end
end.

Lemma icmp_walk_nread : forall l r k j v, icmp_walk l r k = Some (j, v) ->
(j <= k)%nat /\ (j <= length l)%nat /\ (j <= length r)%nat.
Proof.
intros l r k. revert l r.
induction k as [|k IH]; intros l r j v H; cbn in H.
- injection H as <- <-. cbn. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b).
+ injection H as <- <-. cbn. lia.
+ destruct (icmp_walk l r k) as [[j' v']|] eqn:E; [|discriminate].
injection H as <- <-. apply IH in E. cbn. lia.
Qed.
End Models.

Definition cmp_stop (a b : byte) : bool := (negb (bv_unsigned a =? bv_unsigned b) || (bv_unsigned a =? 0))%bool.
Definition cmp_sign (a b : byte) : Z := Z.sgn (bv_unsigned a - bv_unsigned b).

Definition casecmp_stop (a b : byte) : bool := (negb (lower8 (bv_unsigned a) =? lower8 (bv_unsigned b)) || (bv_unsigned a =? 0))%bool.
Definition casecmp_val (a b : byte) : Z := lower8 (bv_unsigned a) - lower8 (bv_unsigned b).

Definition istrncmp_model (l r : list byte) (n : Z) : option (nat * Z) := icmp_walk cmp_stop cmp_sign l r (Z.to_nat n).
Definition istrncasecmp_model (l r : list byte) (n : Z) : option (nat * Z) := icmp_walk casecmp_stop casecmp_val l r (Z.to_nat n).

Definition istrcmp_model (ls rs : list byte) : option (nat * Z) :=
icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) (S (length ls)).

Section WalkFacts.
Variable stop : byte -> byte -> bool.
Variable value : byte -> byte -> Z.
Notation walk := (icmp_walk stop value).

Lemma icmp_walk_zero : forall fuel l r v, walk l r fuel = Some (0%nat, v) -> fuel = 0%nat /\ v = 0.
Proof.
intros [|fuel] l r v H; cbn in H.
- injection H as <-. auto.
- destruct l; [discriminate|]. destruct r; [discriminate|]. destruct (stop _ _); [discriminate|].
destruct (icmp_walk stop value _ _ _) as [[? ?]|]; discriminate.
Qed.

Lemma icmp_walk_before : forall fuel l r j v i, walk l r fuel = Some (j, v) -> (S i < j)%nat ->
exists a b, nth_error l i = Some a /\ nth_error r i = Some b /\ stop a b = false.
Proof.
induction fuel as [|fuel IH]; intros l r j v i H Hi; cbn in H.
- injection H as <- <-. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b) eqn:Hs.
+ injection H as <- <-. lia.
+ destruct (icmp_walk stop value l r fuel) as [[j' v']|] eqn:E; [|discriminate]. injection H as <- <-.
destruct i as [|i].
* exists a, b. cbn. auto.
* destruct (IH l r j' v' i E ltac:(lia)) as (a' & b' & Ha & Hb & Hs'). exists a', b'. cbn. auto.
Qed.

Lemma icmp_walk_last : forall fuel l r j v, walk l r fuel = Some (j, v) -> (1 <= j)%nat ->
exists a b, nth_error l (j - 1) = Some a /\ nth_error r (j - 1) = Some b /\
((stop a b = true /\ v = value a b) \/ (stop a b = false /\ j = fuel /\ v = 0)).
Proof.
induction fuel as [|fuel IH]; intros l r j v H Hj; cbn in H.
- injection H as <- <-. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b) eqn:Hs.
+ injection H as <- <-. exists a, b. cbn. auto.
+ destruct (icmp_walk stop value l r fuel) as [[j' v']|] eqn:E; [|discriminate]. injection H as <- <-.
destruct j' as [|j''].
* destruct (icmp_walk_zero _ _ _ _ E) as [-> ->]. exists a, b. cbn. split; [reflexivity|]. split; [reflexivity|]. right. auto.
* destruct (IH l r (S j'') v' E ltac:(lia)) as (a' & b' & Ha & Hb & Hc).
exists a', b'. replace (S (S j'') - 1)%nat with (S j'') by lia. replace (S j'' - 1)%nat with j'' in Ha, Hb by lia.
cbn [nth_error]. split; [exact Ha|]. split; [exact Hb|].
destruct Hc as [Hc | (Hs' & Hf & Hv)]; [left; exact Hc | right]. subst. auto.
Qed.

Lemma icmp_walk_pos : forall fuel l r j v, walk l r fuel = Some (j, v) -> (1 <= fuel)%nat -> (1 <= j)%nat.
Proof.
intros fuel l r j v H Hf. destruct j; [|lia]. destruct (icmp_walk_zero _ _ _ _ H) as [-> _]. lia.
Qed.
End WalkFacts.

Lemma cstr_nth_zero : forall (s : list byte) i c, ~ In b0 s -> nth_error (s ++ [b0]) i = Some c ->
(bv_unsigned c = 0 <-> i = length s).
Proof.
intros s i c Hn Hc. destruct (Nat.lt_ge_cases i (length s)) as [Hlt | Hge].
- rewrite nth_error_app1 in Hc by lia. split; [| lia]. intros Hz. exfalso. exact (notin0_nth s i c Hn Hc Hz).
- rewrite nth_error_app2 in Hc by lia. pose proof (nth_error_lt _ _ _ Hc) as L. cbn in L.
replace (i - length s)%nat with 0%nat in Hc by lia. cbn in Hc. injection Hc as <-. split; [lia | reflexivity].
Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_ISTRCMP : Z := 0x4f958.
Definition istrcmp_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b lo : Z) (ls rs : list byte) (k : nat) (v : Z)
(Q : machine_state -> Prop),
istrcmp_model ls rs = Some (k, v) ->
unpoisoned asegs m A_SB a (Z.of_nat k) -> unpoisoned asegs m A_SB b (Z.of_nat k) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length ls) + 1 <= 2^47 -> Z.of_nat (length ls) + 1 < 2^40 -> 0 <= b -> b + Z.of_nat (length rs) + 1 <= 2^47 ->
(64 < Z.of_nat k -> app_mem a (Z.of_nat k) /\ app_mem b (Z.of_nat k)) ->
(a + Z.of_nat (length ls) + 1 <= lo \/ bv_unsigned sp <= a) -> (b + Z.of_nat (length rs) + 1 <= lo \/ bv_unsigned sp <= b) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 b -> ~ In b0 ls -> ~ In b0 rs ->
bytes_at asegs m a (ls ++ [b0]) -> bytes_at asegs m b (rs ++ [b0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' a (ls ++ [b0]) -> bytes_at asegs m' b (rs ++ [b0]) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ISTRCMP) fc None m (seg_rom asegs)).

Definition A_ISTRNCMP : Z := 0x4f95c.
Definition A_ISTRNCASECMP : Z := 0x4f960.
Definition istrn_spec_U (entry : Z) (model : list byte -> list byte -> Z -> option (nat * Z)) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b n lo : Z) (la lb : list byte) (k : nat) (v : Z)
(Q : machine_state -> Prop),
model la lb n = Some (k, v) ->
unpoisoned asegs m A_SB a (Z.of_nat k) -> unpoisoned asegs m A_SB b (Z.of_nat k) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length la) <= 2^47 -> 0 <= b -> b + Z.of_nat (length lb) <= 2^47 ->
(a + Z.of_nat (length la) <= lo \/ bv_unsigned sp <= a) -> (b + Z.of_nat (length lb) <= lo \/ bv_unsigned sp <= b) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n -> 0 < n <= 64 ->
bytes_at asegs m a la -> bytes_at asegs m b lb ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' a la -> bytes_at asegs m' b lb ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Definition istrncmp_spec_U : Prop := istrn_spec_U A_ISTRNCMP istrncmp_model.
Definition istrncasecmp_spec_U : Prop := istrn_spec_U A_ISTRNCASECMP istrncasecmp_model.

Definition A_ISTRTOLL : Z := 0x4fa04.
Definition A_GOT_GUARD : Z := 0xe6b80.
Definition A_GUARD : Z := 0x642ea0.
Definition istrtoll_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A E lo : Z) (str : list byte) (e g ej : word)
(Q : machine_state -> Prop),
unpoisoned asegs m A_SB A (Z.of_nat (length str) + 1) -> unpoisoned asegs m A_SB E 8 -> asan_rt_ok m ->
(64 < Z.of_nat (length str) + 1 -> app_mem A (Z.of_nat (length str) + 1)) -> app_mem E 8 ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 E -> a2 = Z_to_bv 64 10 -> tp = Z_to_bv 64 A_TP ->
0 <= A -> A + Z.of_nat (length str) + 2 <= 2^47 -> Z.of_nat (length str) + 1 < 2^40 -> 0x645000 <= E -> E + 8 <= 2^47 ->
bytes_at asegs m A (str ++ [b0]) -> ~ In b0 str ->
rw_cells asegs m E [C8 ej] -> rw_cells asegs m (A_TP - 164) [C4 e] ->
bytes_at asegs m A_GOT_GUARD (le8 (Z_to_bv 64 A_GUARD)) -> bytes_at asegs m A_GUARD (le8 g) ->
(E + 8 <= lo \/ bv_unsigned sp <= E) ->
(A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A) ->
(A + Z.of_nat (length str) + 1 <= A_TP - 164 \/ A_TP - 160 <= A) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (j : Z) (e' : word),
munch [(E, E + 8); (A_TP - 164, A_TP - 160); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' E [C8 (Z_to_bv 64 (A + j))] -> 0 <= j <= Z.of_nat (length str) ->
bytes_at asegs m' A (str ++ [b0]) -> rw_cells asegs m' (A_TP - 164) [C4 e'] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ISTRTOLL) fc None m (seg_rom asegs)).

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw QZsi Qhd4 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Q7UD Qwm6.
Import QZsi.Mq0 Qhd4.Mq0.
Import Qwm6.Mq0 QlKV.Mqa.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Lemma lxor_ones64 : forall d, 0 <= d < 2^64 -> Z.lxor d 18446744073709551615 = 18446744073709551615 - d.
Proof.
intros d Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
assert (E : 18446744073709551615 - d = Z.lnot d mod 2^64) by (unfold Z.lnot; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia).
rewrite E. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 64) eqn:L.
- rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite xorb_false_r, andb_false_r.
apply Z.ltb_ge in L. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec d 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m8_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
intros x Hx.
replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3)
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
replace 18446744073709551608 with (Z.lnot 7 mod 2^64) by reflexivity.
rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 7 with (Z.ones 3). rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 3) eqn:L3.
- apply Z.ltb_lt in L3. rewrite Z.shiftl_spec_low by lia. cbn. rewrite andb_false_r. reflexivity.
- apply Z.ltb_ge in L3. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - 3 + 3) with i by lia. cbn.
destruct (Z.ltb i 64) eqn:L64.
+ rewrite andb_true_r. reflexivity.
+ rewrite andb_false_r. apply Z.ltb_ge in L64. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ro_C8_of_bytes_at : forall segs m a v, bytes_at segs m a (le8 v) -> ro_cells segs m a [C8 v].
Proof. intros segs m a v H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma ro_C1_of_bytes_at : forall segs m a b, bytes_at segs m a [b] -> ro_cells segs m a [C1 b].
Proof. intros segs m a b H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact H]. Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned.
unfold bv_wrap.
replace (bv_modulus 8) with 256 by reflexivity. replace (bv_half_modulus 8) with 128 by reflexivity.
rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ov_read1_of_ro : forall segs m A b, ro_cells segs m A [C1 b] -> ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [b].
Proof.
intros segs m A b H. pose proof (cells_at_read segs m A [C1 b] 0%nat (C1 b) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma size_test_n : forall n, 0 < n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma size_test_big : forall n, (n = 0 \/ 65 <= n < 2^63) -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = true.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
apply negb_true_iff. apply Z.ltb_ge.
destruct Hn as [-> | Hn]; [change ((0 + -65) mod 2^64) with (2^64 - 65); lia|].
rewrite Z.mod_small by lia. lia.
Qed.

Lemma asan_rt_get : forall m a bs, asan_rt_ok m -> In (a, bs) a4_rt_cells -> bytes_at asegs m a bs.
Proof. intros m a bs H HI. unfold asan_rt_ok in H. rewrite Forall_forall in H. exact (H (a, bs) HI). Qed.
Ltac rt_in := cbn [a4_rt_cells a4_rt_consts app]; unfold A_GOT_SB, A_SB_CELL, A_SB; repeat (first [ left; reflexivity | right ]).

Tactic Notation "rt_cell" constr(RT) constr(a) "as" ident(H) :=
lazymatch type of RT with asan_rt_ok ?m => pose proof (asan_rt_get m a _ RT ltac:(rt_in)) as H; cbn [fst snd] in H end.

Lemma unpoisoned_sub_any : forall segs m SB s n s' n', unpoisoned segs m SB s n -> s <= s' -> s' + n' <= s + n -> 0 < n' ->
unpoisoned segs m SB s' n'.
Proof.
intros segs m SB s n s' n' (Hn & Ha & (v & Hb & Hv) & Hc) H1 H2 H3. split; [exact H3|]. split; [|split].
- intros g Hg. apply Ha. Z.div_mod_to_equations. lia.
- destruct (Z_lt_le_dec ((s' + n' - 1) / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
+ exists 0. split; [| left; reflexivity]. apply Ha. Z.div_mod_to_equations. lia.
+ assert (E : (s' + n' - 1) / 8 = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
exists v. rewrite E. split; [exact Hb |]. destruct Hv as [-> | [Hv1 Hv2]]; [left; reflexivity | right].
split; [exact Hv1|]. Z.div_mod_to_equations. lia.
- intros w Hw. apply Hc. Z.div_mod_to_equations. lia.
Qed.

Section RC__icpt. Context {RC__ : Q6q3.RunConsts}.

Lemma try_asan_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf07d9 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6aae0) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma init_gate_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf07d8 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf07d9 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a0' a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6a79c) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End RC__icpt.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6 QGcC.Mq0.
Import Qwm6.Mq0 QlKV.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithHI.
Variable HIx : heap_iface_A A4L.

Lemma errno_shadowA : forall A LB LM FR B m md,
HEAPA A4L HIx A LB LM FR B m md -> ro_cells asegs m (A_ERRNO / 8 + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md HP.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (A_ERRNO / 8) HP ltac:(unfold A_ERRNO; cbn; lia) ltac:(unfold A_ERRNO; cbn; lia)) as SH.
cbn [hl_sb hl_reg_globals hl_segs hla_base A4L A4H] in SH.
replace (img_shadow_val tokA_reg_globals (A_ERRNO / 8)) with 0 in SH by (vm_compute; reflexivity).
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact SH].
Qed.
End WithHI.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw. Import QPZI.Mq1.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition jo_get_type_A_entry : Z := 0x9ae00.
Definition jo_is_type_A_entry : Z := 0x9ae00.
Definition jo_get_object_A_entry : Z := 0x9bdf0.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition small_post (m : word -> option byte) (lo : Z) (v : word) : machine_state -> Prop :=
fun ms' => exists m', ret4x ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v m' ms'
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Definition small_pre (m : word -> option byte) (lo sbcell : Z) : Prop :=
mem_inv asegs m /\ stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - 16 /\ alloc_ceiling <= lo /\
ro_cells asegs m A_GOT_SB [C8 (Z_to_bv 64 sbcell)] /\ ro_cells asegs m sbcell [C8 (Z_to_bv 64 A_SB)] /\
0 < sbcell /\ sbcell + 8 <= alloc_ceiling.

Lemma jo_get_type_null_A : forall m lo sbcell,
small_pre m lo sbcell ->
evt asegs (small_post m lo (Z_to_bv 64 0))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_type_A_entry) fc None m (seg_rom asegs)).
Proof.
intros m lo sbcell (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8). unfold jo_get_type_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step. step. if_true. step. step. step.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma jo_get_type_A : forall m lo sbcell p ty rc tojs pb udel ud,
small_pre m lo sbcell ->
rw_cells asegs m p (jhdr_cells ty rc tojs pb udel ud) -> 0 < p -> p + 40 <= alloc_ceiling -> p mod 8 = 0 -> 0 <= ty < 2^31 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0)] -> p / 8 + A_SB + 1 <= alloc_ceiling ->
evt asegs (small_post m lo (Z_to_bv 64 ty))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_type_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ud. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) HDR Hp Hph Hal Hty SH0 HSH.
unfold jhdr_cells in HDR. unfold jo_get_type_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chk0.
step. norm_w32. step. step. step.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma jo_get_object_A : forall m lo sbcell p rc tojs pb udel ud t,
small_pre m lo sbcell ->
rw_cells asegs m p (jhdr_cells JT_OBJECT rc tojs pb udel ud ++ [C8 (Z_to_bv 64 t)]) -> 0 < p -> p + 48 <= alloc_ceiling -> p mod 8 = 0 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p / 8 + A_SB + 6 <= alloc_ceiling ->
evt asegs (small_post m lo (Z_to_bv 64 t))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_object_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until t. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) HDR Hp Hph Hal SH HSH.
unfold jhdr_cells, JT_OBJECT in HDR. cbn [app] in HDR. unfold jo_get_object_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
step. step. step. if_falsex.
step. step. step.
asan_chk0.
step. step. step. if_false.
step.
asan_chkA.
step. step. step. step. step.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

End Regs.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QJjn.
Import QnCn.Mq0.
Import Q7UD Qhd4.
Import Qwm6.Mq0 QlKV.Mq7 QlKV.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition arr_capA (BS : list blk) : Z := snd (nth 2 BS (0, 0)) / 8.

Lemma arr_capA_jval : forall m kids BS p rc,
jval asegs A4F (Sarr kids) m BS p rc ->
exists a arr rest, BS = (p, 48) :: (a, AL_SZ) :: (arr, 8 * arr_capA BS) :: rest /\
Z.of_nat (length kids) <= arr_capA BS /\ 1 <= arr_capA BS /\ 8 * arr_capA BS < 2^64.
Proof.
intros m kids BS p rc J. cbn [jval] in J.
destruct J as (pb & PBS & REST & EBS & _ & a & ABS & ps & KBS & EREST & _ & AL & L1 & _ & _).
destruct AL as (arr & size & junk & EABS & Hlen & Hsz & _ & _). subst ABS REST BS.
exists a, arr, (concat KBS ++ PBS). unfold arr_capA. cbn [app nth snd].
rewrite (Z.mul_comm 8 size), Z.div_mul by lia. rewrite <- L1, (Z.mul_comm size 8). split; [reflexivity|]. lia.
Qed.

Definition arr_add_costA (cap len : Z) : Z := if len + 1 <? cap then 0 else 256 * cap + 512.
Definition arr_grownA (cap len cap' : Z) : Prop := (cap' = cap /\ len + 1 < cap) \/ (cap' = 2 * cap /\ cap <= len + 1).
Definition arr_shrink_costA (cap len : Z) : Z := if len =? cap then 0 else 16 * (8 * Z.max len 1) + 512.
Definition new_array_costA : Z := 16 * 48 + 512 + (2048 + 128 * 32) + 512.

Section AJoStmts.
Variable HIx : heap_iface_A A4L.
Variable G : (word -> option byte) -> Prop.

Definition jo_preA (A : ASA A4L HIx) (LBall LM : list blk) (FRS : list frame) (B : bud) (m : word -> option byte) (md : config)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAPA A4L HIx A LBall LM FRS B m md /\
stk asegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hiA_top A4L HIx /\
rw_cells asegs m A_ERRNO [C4 errv] /\
tp = Z_to_bv 64 A_TP /\ bv_unsigned ra mod 2 = 0.

Definition jo_post_frameA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_new_container_A_stmt (entry stkb costB costD ura : Z) (s : jshape) (capok : list blk -> Prop) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
jo_preA A LB LM FRS B m md sp tp ra lo stkb errv -> G m ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 ura) u ->
costB <= bB B -> uw_cost u + costD <= bD B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - costB <= bB B' -> bD B - (uw_cost u + costD) <= bD B' ->
((r = 0 /\ HEAPA A4L HIx A' LB LM FRS B' m' md') \/
(r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ capok BS /\ HEAPA A4L HIx A' (BS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_array_add_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v : Z)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA A (ABS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> jopt asegs A4F vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
Z.of_nat (length kids) + 1 < 2^28 ->
arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bD B <= bD B' ->
((r = 0 /\ exists ABS', jval asegs A4F (Sarr (kids ++ [vs])) m' ABS' p 1 /\
arr_grownA (arr_capA ABS) (Z.of_nat (length kids)) (arr_capA ABS') /\
bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md' /\
(forall w wv, jtx (Sarr kids) ABS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sarr (kids ++ [vs])) ABS' = Some (w + (2 + wv), []))) \/
(r = 2^64 - 1 /\ bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
jval asegs A4F (Sarr kids) m' ABS p 1 /\ jopt asegs A4F vs m' VBS v /\
HEAPA A4L HIx A' (ABS ++ VBS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_array_shrink_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_preA A (ABS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
Z.of_nat (length kids) < 2^28 ->
arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
(exists ABS', jval asegs A4F (Sarr kids) m' ABS' p 1 /\
(arr_capA ABS' = arr_capA ABS \/ (r = 0 /\ arr_capA ABS' = Z.max (Z.of_nat (length kids)) 1)) /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md') ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End AJoStmts.

Definition jo_new_array_A (HIx : heap_iface_A A4L) :=
jo_new_container_A_stmt HIx (fun _ => True) 0x9eb2c (32 + 32 + 4096) new_array_costA 0 0x9eb50 (Sarr []) (fun BS => arr_capA BS = 32).
Definition jo_array_add_A (HIx : heap_iface_A A4L) := jo_array_add_A_stmt HIx 0x9ecf4 (16 + 96 + 4096).
Definition jo_array_shrink_A (HIx : heap_iface_A A4L) := jo_array_shrink_A_stmt HIx 0x9ed6c (16 + 48 + 4096).

End RC__1.
End Mq4.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition GHASHA : Z := 0xea540.
Definition GSEEDA : Z := 0xea560.
Definition A_GOT_LHEQ : Z := 0xe6a98.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_globA (m : word -> option byte) : Prop :=
rw_cells asegs m GHASHA [C8 (Z_to_bv 64 (fn_lh_char_hash A4F))]
/\ (exists seed : word, rw_cells asegs m GSEEDA [C4 seed]).

Lemma lh_globA_client : forall LB SP m m', heap_pres A4H LB SP m m' -> lh_globA m -> lh_globA m'.
Proof.
intros LB SP m m' HPR (G1 & [seed G2]). split.
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. unfold GHASHA in Ha.
cbn. unfold a4_client_static. lia.
- exists seed. eapply (heap_pres_rw_cells A4H); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. unfold GSEEDA in Ha.
cbn. unfold a4_client_static. lia.
Qed.

Lemma lh_globA_frame : forall m m' W,
lh_globA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (GHASHA + 8 <= fst iv \/ snd iv <= GHASHA) /\ (GSEEDA + 4 <= fst iv \/ snd iv <= GSEEDA)) W ->
lh_globA m'.
Proof.
intros m m' W (G1 & [seed G2]) MU WM DJ. split.
- eapply (rw_cells_transport asegs W m m'); [exact G1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(D1 & _) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
- exists seed. eapply (rw_cells_transport asegs W m m'); [exact G2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(_ & D1) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
Qed.

Definition rtc_lheq_stmt (HIx : heap_iface_A A4L) : Prop :=
forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md ->
bytes_at asegs m A_GOT_LHEQ (le8 (Z_to_bv 64 (fn_lh_char_equal A4F))).

Section WithHI.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma blk_ne_01A : forall A a n b k LB LM FR B m md,
HEAPAx A ((a, n) :: (b, k) :: LB) LM FR B m md -> a <> b.
Proof.
intros A a n b k LB LM FR B m md HP E. subst.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
apply Hni. left. reflexivity.
Qed.

Lemma blocks2A : forall A a na b nb LB LM FR B m md,
HEAPAx A ((a, na) :: (b, nb) :: LB) LM FR B m md ->
(a mod 16 = 0 /\ 0 < a /\ a + na <= alloc_ceiling /\ (a + na <= hl_img_lo A4H \/ hl_img_hi A4H <= a))
/\ (b mod 16 = 0 /\ 0 < b /\ b + nb <= alloc_ceiling /\ (b + nb <= hl_img_lo A4H \/ hl_img_hi A4H <= b))
/\ (a + na <= b \/ b + nb <= a).
Proof.
intros A a na b nb LB LM FR B m md HP.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a na HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ a na HP ltac:(apply in_or_app; left; left; reflexivity)) as Hia.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b nb HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hal2 & Hlo2 & Hhi2 & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b nb HP ltac:(apply in_or_app; left; right; left; reflexivity)) as Hia2.
pose proof (blk_ne_01A _ _ _ _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a na b nb HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hne) as Hdj.
repeat split; try assumption.
Qed.

Lemma lh_heap_factsA : forall A t tbl size es LB LM FR B m md,
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FR B m md ->
(t mod 16 = 0 /\ 0 < t /\ t + 56 <= alloc_ceiling /\ (t + 56 <= hl_img_lo A4H \/ hl_img_hi A4H <= t))
/\ (tbl mod 16 = 0 /\ 0 < tbl /\ tbl + 40 * size <= alloc_ceiling /\ (tbl + 40 * size <= hl_img_lo A4H \/ hl_img_hi A4H <= tbl))
/\ (t + 56 <= tbl \/ tbl + 40 * size <= t)
/\ (forall e, In e es ->
0 <= le_kn e /\ 0 < le_k e /\ le_k e + le_kn e <= alloc_ceiling /\ (le_k e + le_kn e <= hl_img_lo A4H \/ hl_img_hi A4H <= le_k e)
/\ (t + 56 <= le_k e \/ le_k e + le_kn e <= t) /\ (tbl + 40 * size <= le_k e \/ le_k e + le_kn e <= tbl)).
Proof.
intros A t tbl size es LB LM FR B m md HP. unfold lh_blocks in HP. cbn [app] in HP.
destruct (blocks2A _ _ _ _ _ _ _ _ _ _ _ HP) as (F1 & F2 & F12). split; [exact F1|]. split; [exact F2|]. split; [exact F12|].
intros e He.
assert (Hin : In (le_k e, le_kn e) (((t, 56) :: (tbl, 40 * size) :: map (fun e => (le_k e, le_kn e)) es ++ LB) ++ LM)).
{ apply in_or_app. left. right; right. apply in_or_app. left. apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as Himg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn [map blk_addr fst app] in ND.
inversion ND as [|x l Hnt ND1]; subst. inversion ND1 as [|y l' Hntb ND2]; subst.
assert (NEt : t <> le_k e).
{ intros E. apply Hnt. rewrite E. right. rewrite !map_app. apply in_or_app. left. apply in_or_app. left. apply in_map_iff. exists (le_k e, le_kn e). split; [reflexivity|].
apply in_map_iff. exists e. split; [reflexivity | exact He]. }
assert (NEb : tbl <> le_k e).
{ intros E. apply Hntb. rewrite E. rewrite !map_app. apply in_or_app. left. apply in_or_app. left. apply in_map_iff. exists (le_k e, le_kn e). split; [reflexivity|].
apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ t 56 (le_k e) (le_kn e) HP ltac:(apply in_or_app; left; left; reflexivity) Hin NEt) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) (le_k e) (le_kn e) HP ltac:(apply in_or_app; left; right; left; reflexivity) Hin NEb) as D2.
repeat split; try assumption; lia.
Qed.

Lemma lh_newkey_factsA : forall A t tbl size es k kn LB LM FR B m md,
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FR B m md ->
0 <= kn /\ 0 < k /\ k + kn <= alloc_ceiling /\ (k + kn <= hl_img_lo A4H \/ hl_img_hi A4H <= k)
/\ (t + 56 <= k \/ k + kn <= t) /\ (tbl + 40 * size <= k \/ k + kn <= tbl) /\ ~ In k (map le_k es).
Proof.
intros A t tbl size es k kn LB LM FR B m md HP.
assert (HinK : In (k, kn) ((lh_blocks t tbl size es ++ (k, kn) :: LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as (Hn & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as Himg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
assert (NT : t <> k).
{ intros ->. eapply (nodup_prefix_suffix (lh_blocks k tbl size es) (((k, kn) :: LB) ++ LM) k 56 kn ND); [left; reflexivity | left; reflexivity]. }
assert (NB : tbl <> k).
{ intros ->. eapply (nodup_prefix_suffix (lh_blocks t k size es) (((k, kn) :: LB) ++ LM) k (40 * size) kn ND); [right; left; reflexivity | left; reflexivity]. }
assert (NK : ~ In k (map le_k es)).
{ intros IN. apply in_map_iff in IN as (e & <- & He).
eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (((le_k e, kn) :: LB) ++ LM) (le_k e) (le_kn e) kn ND); [| left; reflexivity].
right; right. apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ t 56 k kn HP ltac:(apply in_or_app; left; left; reflexivity) HinK NT) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) k kn HP ltac:(apply in_or_app; left; right; left; reflexivity) HinK NB) as D2.
repeat split; try assumption; lia.
Qed.
End WithHI.

End RC__1.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition src_globA (b n : Z) : Prop :=
hl_img_lo A4H + 64 <= b /\ b + n + 64 <= hl_img_hi A4H
/\ ((forall a, b <= a < b + n -> hl_client_static A4H a) \/ (forall a, b <= a < b + n -> ro_addr asegs (wa a) = true))
/\ (forall g, b / 8 <= g < (b + n - 1) / 8 -> img_shadow_val (hl_reg_globals A4L) g = 0)
/\ (img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8) = 0
\/ (0 < img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8) < 8 /\ (b + n - 1) mod 8 < img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8))).

Definition src_locA (LB : list blk) (FRS : list frame) (b n : Z) : Prop :=
(exists sa sk, In (sa, sk) LB /\ sa <= b /\ b + n <= sa + sk)
\/ (exists Fs ks, In (Fs, ks) FRS /\ Fs <= b /\ b + n <= Fs + fr_size ks - 8)
\/ src_globA b n.

Lemma unpoisoned_of_shadow_fun : forall segs m SB s n glo ghi (V : Z -> Z),
(forall g, glo <= g < ghi -> bytes_at segs m (g + SB) [Z_to_bv 8 (V g)]) ->
glo + 8 <= s / 8 -> (s + n - 1) / 8 + 8 <= ghi -> 0 < n -> 0 <= glo + SB ->
(forall g, s / 8 <= g < (s + n - 1) / 8 -> V g = 0) ->
(V ((s + n - 1) / 8) = 0 \/ (0 < V ((s + n - 1) / 8) < 8 /\ (s + n - 1) mod 8 < V ((s + n - 1) / 8))) ->
unpoisoned segs m SB s n.
Proof.
intros segs m SB s n glo ghi V Z0 Hlo Hhi Hn Hpos VZ VL. split; [exact Hn|]. split; [|split].
- intros g Hg. rewrite <- (VZ g Hg). apply Z0. Z.div_mod_to_equations. lia.
- exists (V ((s + n - 1) / 8)). split; [| exact VL]. apply Z0. Z.div_mod_to_equations. lia.
- intros w Hw.
assert (B : forall i, 0 <= i < 8 -> bytes_at segs m (w * 8 + i) [Z_to_bv 8 (V (w * 8 + i - SB))]).
{ intros i Hi. replace (w * 8 + i) with ((w * 8 + i - SB) + SB) at 1 by lia. apply Z0. Z.div_mod_to_equations. lia. }
exists (map (fun i => Z_to_bv 8 (V (w * 8 + Z.of_nat i - SB))) (seq 0 8)). split; [reflexivity|].
destruct (B 0 ltac:(lia)) as (Hw0 & _ & _).
destruct (B 7 ltac:(lia)) as (_ & Hw7 & _). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in Hw7.
split; [lia|]. split; [cbn [length map seq Z.of_nat Pos.of_succ_nat Pos.to_nat]; lia|].
intros i Hi. cbn [length map seq] in Hi.
destruct (B (Z.of_nat i) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
rewrite Z.add_0_r in Hb. rewrite Hb. clear -Hi.
do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi. lia.
Qed.

Lemma client_range_incl : forall (LB LB' : list blk) SP A n,
(forall b, In b LB -> In b LB') -> client_range A4H LB SP A n -> client_range A4H LB' SP A n.
Proof.
intros LB LB' SP A n Hsub [H | [H | (b & Hb & Hr)]]; [left; exact H | right; left; exact H | right; right].
exists b. split; [apply Hsub; exact Hb | exact Hr].
Qed.

Lemma ro_range_bytes_pres : forall m m' b (bs : list byte),
mem_inv asegs m -> mem_inv asegs m' -> (forall a, b <= a < b + Z.of_nat (length bs) -> ro_addr asegs (wa a) = true) ->
bytes_at asegs m b bs -> bytes_at asegs m' b bs.
Proof.
intros m m' b bs MI MI' RO (B0 & B1 & BY). split; [exact B0|]. split; [exact B1|].
intros i Hi. rewrite <- (BY i Hi). specialize (RO (b + Z.of_nat i) ltac:(lia)).
unfold mrd. destruct (m' (wa (b + Z.of_nat i))) eqn:E'; [pose proof (MI' _ _ E'); congruence|].
destruct (m (wa (b + Z.of_nat i))) eqn:E; [pose proof (MI _ _ E); congruence| reflexivity].
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma src_loc_facts : forall A pb buf cap LB LM FRS B m md b n,
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md -> src_locA LB FRS b n -> 0 <= n ->
0 < b /\ b + n <= alloc_ceiling /\ (b + n <= buf \/ buf + cap <= b) /\ (b + n <= pb \/ pb + PB_SZ <= b) /\
((b + n <= hl_img_lo A4H \/ hl_img_hi A4H <= b) \/ src_globA b n) /\ (n <= 64 \/ app_mem b n).
Proof.
intros A pb buf cap LB LM FRS B m md b n HP SRCB Hn.
pose proof alloc_ceiling_range as ACR.
destruct SRCB as [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | SG]].
- assert (IN : In (sa, sk) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; right; exact Hsrc).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP IN) as (_ & _ & Hslo & Hshi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ sa sk HP IN) as Hsimg.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ sa sk HP IN) as Hsam. cbn [hl_sb A4L] in Hsam.
assert (Hsane : sa <> pb /\ sa <> buf).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst.
split; intros E; subst sa; [apply Hni; right | apply Hni2]; apply in_or_app; left; exact (in_map blk_addr _ _ Hsrc). }
destruct Hsane as [Hsapb Hsabuf].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf cap sa sk HP ltac:(right; left; reflexivity) IN ltac:(congruence)) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb PB_SZ sa sk HP ltac:(left; reflexivity) IN ltac:(congruence)) as D2.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg |- *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
destruct (Z.le_gt_cases n 64) as [Hle|Hgt]; [left; exact Hle | right].
unfold app_mem, A_HMB, A_SB in *. lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & _ & HF0 & HFc & HFimg & _).
pose proof (fr_size_pos ks ltac:(lia)) as HSZ.
assert (INb : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (right; left; reflexivity).
assert (INp : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HFs INb) as D1.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HFs INp) as D2.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as AM. cbn [hl_sb A4L] in AM.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg |- *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
destruct (Z.le_gt_cases n 64) as [Hle|Hgt]; [left; exact Hle | right].
unfold app_mem, A_HMB, A_SB in *. lia.
-
pose proof SG as (G1 & G2 & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as Ib.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as Ip.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (Hc0 & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in G1, G2, Ib, Ip |- *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; exact SG|].
destruct (Z.le_gt_cases n 64) as [Hle|Hgt]; [left; exact Hle | right].
unfold app_mem, A_HMB, A_SB in *. lia.
Qed.

Lemma src_loc_range : forall LB LM FRS SP b n,
src_locA LB FRS b n -> client_range A4H (LB ++ LM ++ fr_ivs A4L FRS) SP b n \/ (forall a, b <= a < b + n -> ro_addr asegs (wa a) = true).
Proof.
intros LB LM FRS SP b n [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | (_ & _ & [SG | RO] & _)]].
3:{ left; right; left. exact SG. }
3:{ right. exact RO. }
- left; right; right. exists (sa, sk). cbn. split; [apply in_or_app; left; exact Hsrc | lia].
- left; right; right. exists (Fs, fr_size ks - 8). cbn. split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFs | lia].
Qed.

Lemma src_loc_bytes_pres : forall LBs LB LM FRS SP m m' b (src : list byte),
heap_pres A4H LBs SP m m' -> mem_inv asegs m -> mem_inv asegs m' ->
(forall bb, In bb (LB ++ LM ++ fr_ivs A4L FRS) -> In bb LBs) ->
src_locA LB FRS b (Z.of_nat (length src)) -> bytes_at asegs m b src -> bytes_at asegs m' b src.
Proof.
intros LBs LB LM FRS SP m m' b src HPR MI MI' SUB SRCB SRC.
destruct (src_loc_range LB LM FRS SP b _ SRCB) as [CR | RO].
- eapply (heap_pres_bytes_at A4H); [exact HPR | exact SRC | eapply client_range_incl; [exact SUB | exact CR]].
- exact (ro_range_bytes_pres m m' b src MI MI' RO SRC).
Qed.

Lemma src_loc_fresh : forall A r nr LBX LM FRS B m md LB b n,
HEAPAx A ((r, nr) :: LBX) LM FRS B m md -> src_locA LB FRS b n -> 0 <= n ->
(forall sa sk, In (sa, sk) LB -> In (sa, sk) LBX) ->
r + nr <= b \/ b + n <= r.
Proof.
intros A r nr LBX LM FRS B m md LB b n HP [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | (G1 & G2 & _)]] Hn Hsub.
3:{ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r nr HP ltac:(left; reflexivity)) as Ir.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r nr HP ltac:(left; reflexivity)) as (Hr0 & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in G1, G2, Ir. lia. }
- assert (IN : In (sa, sk) (((r, nr) :: LBX) ++ LM)) by (apply in_or_app; left; right; apply Hsub; exact Hsrc).
assert (Hne : r <> sa).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
intros ->. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ (Hsub _ _ Hsrc)). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r nr sa sk HP ltac:(left; reflexivity) IN Hne). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & _). pose proof (fr_size_pos ks ltac:(lia)).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HFs ltac:(left; reflexivity)). lia.
Qed.

Lemma unpoisoned_of_glob : forall A LB LM FRS B m md b n,
HEAPAx A LB LM FRS B m md -> src_globA b n -> 0 < n -> unpoisoned asegs m A_SB b n.
Proof.
intros A LB LM FRS B m md b n HP (G1 & G2 & _ & GZ & GL) Hn.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in G1, G2.
eapply (unpoisoned_of_shadow_fun asegs m A_SB b n (hl_img_lo A4H / 8) (hl_img_hi A4H / 8) (img_shadow_val (hl_reg_globals A4L)));
cbn [hl_img_lo hl_img_hi hla_base A4L A4H]; unfold A_SB; try (Z.div_mod_to_equations; lia); try assumption.
intros g Hg. pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP) as SI. cbn [hl_img_lo hl_img_hi hl_sb hla_base A4L A4H] in SI.
apply SI; Z.div_mod_to_equations; lia.
Qed.

Lemma unpoisoned_pres_heap : forall LST SP m m' s n cA cK,
unpoisoned asegs m A_SB s n -> heap_pres A4H LST SP m m' ->
In (cA, cK) LST -> cA <= shadow_span_lo A_SB s -> shadow_span_hi A_SB s n <= cA + cK ->
unpoisoned asegs m' A_SB s n.
Proof.
intros LST SP m m' s n cA cK (Hn & GZ & (v & Hv & Hvr) & WRD) HPR Hin Hlo Hhi.
unfold shadow_span_lo, shadow_span_hi in *.
split; [exact Hn|]. split; [| split].
- intros g Hg. eapply (heap_pres_bytes_at A4H); [exact HPR | exact (GZ g Hg) |].
eapply client_range_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- exists v. split; [| exact Hvr]. eapply (heap_pres_bytes_at A4H); [exact HPR | exact Hv |].
eapply client_range_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- intros w Hw. destruct (WRD w Hw) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
eapply (heap_pres_bytes_at A4H); [exact HPR | exact Hbs |].
eapply client_range_block; [exact Hin | Z.div_mod_to_equations; lia | rewrite Hlen; cbn; Z.div_mod_to_equations; lia].
Qed.

Lemma unpoisoned_pres_frame : forall A LB LM FRS B m0 md LBX SP m m' Fs ks b n,
HEAPAx A LB LM FRS B m0 md -> In (Fs, ks) FRS -> Fs <= b -> b + n <= Fs + fr_size ks - 8 ->
unpoisoned asegs m A_SB b n -> heap_pres A4H (LBX ++ LM ++ fr_ivs A4L FRS) SP m m' ->
unpoisoned asegs m' A_SB b n.
Proof.
intros A LB LM FRS B m0 md LBX SP m m' Fs ks b n HP HFs HFa HFk UPS HPR.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & HFal & HF0 & HFc & _).
pose proof UPS as (Hn & _).
eapply unpoisoned_pres_heap; [exact UPS | exact HPR | apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFs | |].
- unfold shadow_span_lo, shad. cbn [hl_sb A4L]. unfold A_SB.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
Z.div_mod_to_equations. lia.
- unfold shadow_span_hi, shad. cbn [hl_sb A4L]. unfold A_SB. rewrite (fr_size_shadow ks) in HFk by lia.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
unfold fr_shadow_len in *. Z.div_mod_to_equations. lia.
Qed.
End WithIface.

Lemma utf8rep_src_globA : src_globA 0xea500 3.
Proof.
unfold src_globA. cbn [hl_img_lo hl_img_hi hla_base A4L A4H hl_client_static hl_reg_globals].
split; [lia|]. split; [lia|]. split; [left; intros a Ha; unfold a4_client_static; lia|].
split; [intros g Hg; exfalso; change (0xea500 / 8) with 119968 in Hg; change ((0xea500 + 3 - 1) / 8) with 119968 in Hg; lia|].
right. vm_compute. repeat split; reflexivity.
Qed.
Lemma utf8rep_src_locA : forall LB FRS, src_locA LB FRS 0xea500 3.
Proof. intros. right; right. exact utf8rep_src_globA. Qed.

Lemma ro_addr_rodata_A : forall a, 0x10000 <= a < 0x3bfe8 -> ro_addr asegs (wa a) = true.
Proof.
intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
unfold asegs, Asan.M.loaded_segments. cbn -[Z.leb Z.ltb Z.add Z.of_N].
repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; try reflexivity;
exfalso; repeat match goal with
| Hb : (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in Hb as [Hb | Hb]
| Hb : (_ <=? _) = false |- _ => apply Z.leb_gt in Hb
| Hb : (_ <? _) = false |- _ => apply Z.ltb_ge in Hb
| Hb : (_ && _)%bool = true |- _ => apply andb_prop in Hb as [? ?]
| Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb
| Hb : (_ <? _) = true |- _ => apply Z.ltb_lt in Hb
end; cbn in *; lia.
Qed.
Fixpoint zrange (lo : Z) (k : nat) : list Z := match k with O => [] | S k' => lo :: zrange (lo + 1) k' end.
Lemma zrange_in : forall k lo g, lo <= g < lo + Z.of_nat k -> In g (zrange lo k).
Proof. induction k as [|k IH]; intros lo g H; [lia|]. cbn [zrange]. destruct (Z.eq_dec g lo) as [->|NE]; [left; reflexivity| right; apply IH; lia]. Qed.
Definition src_ro_chk (b n : Z) : bool :=
(0x10000 + 64 <=? b) && (b + n + 64 <=? 0x3bfe8) && (0 <? n)
&& forallb (fun g => img_shadow_val (hl_reg_globals A4L) g =? 0) (zrange (b / 8) (Z.to_nat ((b + n - 1) / 8 - b / 8)))
&& (let v := img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8) in (v =? 0) || ((0 <? v) && (v <? 8) && ((b + n - 1) mod 8 <? v))).
Lemma src_globA_of_chk : forall b n, src_ro_chk b n = true -> src_globA b n.
Proof.
intros b n H. unfold src_ro_chk in H.
repeat match type of H with (_ && _)%bool = true => let H' := fresh "C" in apply andb_prop in H as [H H'] end.
apply Z.leb_le in H. apply Z.leb_le in C2. apply Z.ltb_lt in C1.
unfold src_globA. cbn [hl_img_lo hl_img_hi hla_base A4L A4H]. split; [lia|]. split; [lia|].
split; [right; intros a Ha; apply ro_addr_rodata_A; lia|]. split.
- intros g Hg. rewrite forallb_forall in C0. apply Z.eqb_eq. apply C0. apply zrange_in. lia.
- cbv zeta in C. apply orb_prop in C as [C|C]; [left; apply Z.eqb_eq; exact C| right].
repeat match type of C with (_ && _)%bool = true => let H' := fresh "D" in apply andb_prop in C as [C H'] end.
apply Z.ltb_lt in C. apply Z.ltb_lt in D0. apply Z.ltb_lt in D. lia.
Qed.

Lemma esc_src_globA : forall b, In b [0x23140; 0x23160; 0x23180; 0x231a0; 0x231c0] -> src_globA b 1.
Proof. intros b Hb. cbn in Hb. repeat (destruct Hb as [<-|Hb]; [apply src_globA_of_chk; vm_compute; reflexivity|]). destruct Hb. Qed.
Lemma esc_src_locA : forall LB FRS b, In b [0x23140; 0x23160; 0x23180; 0x231a0; 0x231c0] -> src_locA LB FRS b 1.
Proof. intros. right; right. apply esc_src_globA. assumption. Qed.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QZsi.Mq0.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma lxor_ones64 : forall d, 0 <= d < 2^64 -> Z.lxor d 18446744073709551615 = 18446744073709551615 - d.
Proof.
intros d Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
assert (E : 18446744073709551615 - d = Z.lnot d mod 2^64) by (unfold Z.lnot; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia).
rewrite E. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 64) eqn:L.
- rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite xorb_false_r, andb_false_r.
apply Z.ltb_ge in L. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec d 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m8_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
intros x Hx.
replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3)
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
replace 18446744073709551608 with (Z.lnot 7 mod 2^64) by reflexivity.
rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 7 with (Z.ones 3). rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 3) eqn:L3.
- apply Z.ltb_lt in L3. rewrite Z.shiftl_spec_low by lia. cbn. rewrite andb_false_r. reflexivity.
- apply Z.ltb_ge in L3. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - 3 + 3) with i by lia. cbn.
destruct (Z.ltb i 64) eqn:L64.
+ rewrite andb_true_r. reflexivity.
+ rewrite andb_false_r. apply Z.ltb_ge in L64. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ro_CB8_of_bytes_at : forall segs m a w, length w = 8%nat -> bytes_at segs m a w -> ro_cells segs m a [CB 8 w].
Proof. intros segs m a w Hl H. split; [cbn; rewrite Hl; split; [reflexivity|exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma amemset_real_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 (cv : word) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D n : Z) (junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= n < 2^63 ->
rw_cells asegs m D [CB (Z.to_nat n) junk] ->
mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 (bv_unsigned cv mod 256)) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) cv (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb750) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros HD HDn Hn DST MI.
pose proof (memset_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) cv (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk) as X.
rewrite (unsigned_lit D), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact DST | exact MI] |].
intros ms' P. unfold memset_post in P. rewrite (unsigned_lit D), (unsigned_lit n) in P by lia. exact P.
Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned.
unfold bv_wrap.
replace (bv_modulus 8) with 256 by reflexivity. replace (bv_half_modulus 8) with 128 by reflexivity.
rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ov_read1_of_ro : forall segs m A b, ro_cells segs m A [C1 b] -> ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [b].
Proof.
intros segs m A b H. pose proof (cells_at_read segs m A [C1 b] 0%nat (C1 b) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma size_test_n : forall n, 0 < n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.

Lemma ov_read8_of_ro : forall segs m A w, ro_cells segs m A [CB 8 w] -> ov_read_bytes segs m (Z_to_bv 64 A) 8 = Some w.
Proof.
intros segs m A w H. pose proof (cells_at_read segs m A [CB 8 w] 0%nat (CB 8 w) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma bytes_at_zero_run : forall segs m a k,
0 <= a -> a + Z.of_nat k <= 2^64 ->
(forall i, 0 <= i < Z.of_nat k -> bytes_at segs m (a + i) [Z_to_bv 8 0]) ->
bytes_at segs m a (repeat (Z_to_bv 8 0) k).
Proof.
intros segs m a k. revert a. induction k as [|k IH]; intros a Ha Hk HB.
- cbn. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- change (repeat (Z_to_bv 8 0) (S k)) with ([Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) k).
apply bytes_at_app. split.
+ specialize (HB 0 ltac:(lia)). rewrite Z.add_0_r in HB. exact HB.
+ change (Z.of_nat (length [Z_to_bv 8 0])) with 1. apply IH; [lia | lia |].
intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply HB. lia.
Qed.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.

Ltac asan_rechkA := step; rewrite ?sxb_zero, ?zxb_zero; step; first [ if_false | if_true ].

Tactic Notation "asan_rechkM" integer(n) := step; rewrite ?sxb_zero, ?zxb_zero; do n step; step; first [ if_false | if_true ].
Tactic Notation "asan_chkM" integer(n) :=
step; step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; do n step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Ltac lit_prefix_cells cs :=
lazymatch cs with
| ?c :: ?r => let r' := lit_prefix_cells r in constr:(c :: r')
| @nil _ => constr:(@nil cell)
| _ => constr:(@nil cell)
end.
Ltac sym_tail_cells cs :=
lazymatch cs with
| _ :: ?r => sym_tail_cells r
| @nil _ => fail
| ?t => t
end.
Ltac catch_upA :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>

repeat match goal with
| H : rw_cells segs ?m0 ?a ?cs |- _ =>
lazymatch m0 with mc => fail | _ => idtac end;
let tl := sym_tail_cells cs in let pre := lit_prefix_cells cs in
let H' := fresh H in
assert (H' : rw_cells segs m0 a pre) by (change cs with (pre ++ tl) in H; exact (proj1 (proj1 (rw_cells_app segs m0 a pre tl) H)));
clear H; rename H' into H
end;

repeat match goal with
| MU : munch ?W ?m0 mc, WM : wmono segs ?m0 mc, H : rw_cells segs ?m0 ?a ?cs |- _ =>
apply (rw_cells_transport segs W m0 mc a cs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| MU : munch ?W ?m0 mc, H : ro_cells segs ?m0 ?a ?cs |- _ =>
apply (ro_cells_transport segs W m0 mc a cs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| MU : munch ?W ?m0 mc, H : bytes_at segs ?m0 ?a ?bs |- _ =>
apply (bytes_at_transport segs W m0 mc a bs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
end
| _ => idtac
end.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TwKit.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma blk_gran0A : forall A LBx LM FRS B m md a n i, HEAPAx A LBx LM FRS B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LM FRS B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

Lemma jopt_frame_onlyA : forall A LB BS LM FRS B m md lo sp s p,
HEAPAx A (BS ++ LB) LM FRS B m md -> alloc_ceiling <= lo -> jopt asegs A4F s m BS p ->
forall N m', lo <= sp - N -> munch [(sp - N, sp)] m m' -> wmono asegs m m' -> jopt asegs A4F s m' BS p.
Proof.
intros A LB BS LM FRS B m md lo sp s p HP LO JO N m' LOS MU WM.
eapply (jopt_agree asegs A4F BS m m' s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *. split; [lia | exact I].
Qed.
End TwKit.
End RC__1.

Definition blk_seen (a n : Z) : Prop := True.
Ltac arm_blkA HIx :=
repeat match goal with
| HPx : HEAPA _ _ _ _ _ _ _ _ _, ER : ?REST = [(?a, ?n)], EBS : ?BSx = ?REST ++ _ |- _ =>
lazymatch goal with _ : blk_seen a n |- _ => fail | _ => idtac end;
let Hin := fresh "Hin" in let Hal := fresh "Hal" in let Hlo := fresh "Hlo" in let Hhi := fresh "Hhi" in
pose proof (heapA_blk _ HIx _ _ _ _ _ _ _ a n HPx
ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS, ER; apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi;
assert (blk_seen a n) by exact I
end.

Ltac site_granA HIx p i :=
lazymatch goal with
| HPx : HEAPA _ _ _ _ _ _ _ ?m0 _ |- _ =>
match goal with
| ER : ?REST = [(p, ?n)], EBS : ?BSx = ?REST ++ _ |- _ =>
let SH := fresh "SHg" in let K := eval vm_compute in (2147450880 + i) in
assert (SH : ro_cells asegs m0 (p / 8 + K) [C1 (Z_to_bv 8 0)]) by
(replace (p / 8 + K) with (p / 8 + 2147450880 + i) by lia;
eapply (blk_gran0A HIx _ _ _ _ _ _ _ p n i HPx); [ rewrite EBS, ER; apply in_or_app; left; apply in_or_app; left; left; reflexivity | lia | lia ])
end
end; catch_upA.

Ltac cells_take cs k :=
lazymatch k with
| O => constr:(@nil cell)
| _ => lazymatch cs with
| ?c :: ?r => let sz := eval cbv in (csize c) in
let ok := eval cbv in (Nat.leb sz k) in
lazymatch ok with true => let k' := eval cbv in (Nat.sub k sz) in let p := cells_take r k' in constr:(c :: p) end
end
end.
Ltac cells_drop cs k :=
lazymatch k with
| O => cs
| _ => lazymatch cs with ?c :: ?r => let sz := eval cbv in (csize c) in let k' := eval cbv in (Nat.sub k sz) in cells_drop r k' end
end.
Ltac zero_cells n :=
lazymatch n with
| O => constr:(@nil cell)
| _ => let n' := eval cbv in (Nat.sub n 8) in let r := zero_cells n' in constr:(C8 (Z_to_bv 64 0) :: r)
end.
Ltac amemset_callA HIx OBL HPx r size k n lo SPA :=
let kn := eval cbv in (Z.to_nat k) in let nn := eval cbv in (Z.to_nat n) in
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs0 |- _ =>
split_for_access BLKc asegs mc r cs0 kn nn;
let cs := lazymatch type of BLKc with rw_cells _ _ _ ?cs => cs end in
let pre := cells_take cs kn in let rest := cells_drop cs kn in let mid := cells_take rest nn in let post := cells_drop rest nn in
let HDRc := fresh "HDRc" in let RESTc := fresh "RESTc" in let DSTc := fresh "DSTc" in let TLc := fresh "TLc" in let HPc := fresh "HPc" in
change cs with (pre ++ (mid ++ post)) in BLKc;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDRc RESTc]; clear BLKc;
cbn [cells_size csize Nat.add] in RESTc; replace (r + Z.of_nat kn) with (r + k) in RESTc by lia;
destruct (proj1 (rw_cells_app asegs mc (r + k) _ _) RESTc) as [DSTc TLc]; clear RESTc;
cbn [cells_size csize Nat.add] in TLc; replace (r + k + Z.of_nat nn) with (r + (k + n)) in TLc by lia;
(let L4 := constr:(A4L) in heap_nowA_auto L4 HIx HPx HPc);
eapply (OBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r size (r + k) 0 n lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ first [ in_prefix | in_app_prefix ] | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DSTc
| eassumption | lia | lia
| first [ lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | (repeat match goal with |- context [bv_unsigned ?sp + - ?c] => replace (bv_unsigned sp + - c) with (bv_unsigned sp - c) by lia end); rewrite Zminus_mod, SPA; reflexivity ]
| lia | eassumption | reflexivity | ];
let mS := fresh "mS" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in let DZ := fresh "DZ" in let STc := fresh "STc" in
intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? mS MUc WMc MIc DZ STc;
transport_after_call asegs mc mS MUc WMc; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MUc WMc HPc;

let zc := zero_cells nn in
change (Z.to_nat n) with nn in DZ; cbn [repeat] in DZ;
apply (rw_cells_recast asegs mS (r + k) _ zc) in DZ; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity];
let BLKn := fresh "BLK" in
assert (BLKn : rw_cells asegs mS r (pre ++ (zc ++ post)));
[ apply (proj2 (rw_cells_app asegs mS r _ _)); cbn [cells_size csize Nat.add]; split; [exact HDRc |];
replace (r + Z.of_nat kn) with (r + k) by lia;
apply (proj2 (rw_cells_app asegs mS (r + k) _ _)); cbn [cells_size csize Nat.add]; split; [exact DZ |];
replace (r + k + Z.of_nat nn) with (r + (k + n)) by lia; exact TLc
| cbn [app] in BLKn; clear HDRc DZ TLc;
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?pcn)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 pcn)) with (Z_to_bv 64 pcn) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end ]
end
end.

Lemma fsaved_restore_kit : forall (F F' : bvmap 5 word) (k1 k2 k3 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> bv_unsigned k1 = bv_unsigned k3 ->
fsaved (bvmap_set k1 v F) F' -> fsaved F (bvmap_set k2 (Sem.reg_get F k3) F').
Proof.
intros F F' k1 k2 k3 v E12 E13 FS j Hj.
replace k2 with k1 by (apply bv_eq; exact E12). replace k3 with k1 by (apply bv_eq; exact E13).
destruct (Z.eq_dec (bv_unsigned k1) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other by (intros E; apply NE; rewrite E; reflexivity).
rewrite (FS j Hj). apply QEpW.reg_get_set_other. intros E; apply NE; rewrite E; reflexivity.
Qed.
Ltac tw_fsaved :=
first [ apply fsaved_refl | apply fsaved_set_self'; reflexivity | eassumption
| eapply fsaved_restore_kit; [reflexivity | reflexivity | first [ apply fsaved_refl | apply fsaved_set_self'; reflexivity | eassumption ] ]
| eapply fsaved_trans; [ eassumption | tw_fsaved ] ].
Ltac tw_ret :=
first [ apply ret_statew_same
| apply ret_statew_intro; [ tw_fsaved | let Hf := fresh "Hf" in intros Hf; first [ exact Hf | solve [eauto 6] ] ] ].
Ltac tw_vm := first [ apply model_vm_only_refl | eassumption | solve [eauto 8 using model_vm_only_trans, model_vm_only_refl] ].
Ltac tw_stk FR sp :=
lazymatch goal with STx : stk asegs ?mf _ _ |- stk asegs ?mf _ _ => first [ exact STx | release_frame FR STx (bv_unsigned sp); exact STx ] end.

Ltac tw_hpres HIx :=
first [ eassumption
| lazymatch goal with |- heap_pres _ ?LST ?SP ?m0 ?mf =>
match goal with
| HPRx : heap_pres _ LST SP m0 ?mk, HPk : HEAPA _ _ _ _ _ _ _ ?mk _, MUx : munch _ ?mk mf, WMx : wmono _ ?mk mf |- _ =>
eapply heap_pres_trans; [ exact HPRx |];
eapply (heap_pres_of_munch A4H LST SP); [ exact MUx | exact WMx |];
eapply (client_outsideA A4L HIx); [ exact HPk | (let bb := fresh "bb" in let Hbb := fresh "Hbb" in intros bb Hbb; first [ exact Hbb | in_tailA Hbb ]) | clia
| first [ solve [let L4 := constr:(A4L) in solve_clientWA L4 HIx HPk]
| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ] ] ]
end end ].
Ltac tw_errno := first [ eassumption | unfold A_ERRNO, A_TP; first [ eassumption | match goal with H : rw_cells asegs ?mf ?a _ |- rw_cells asegs ?mf _ _ => exact H end ] ].

Create HintDb twcost.
Ltac tw_budget :=
repeat autounfold with twcost in *; cbn [bB bD charge uw_cost length Z.of_nat Z.mul Z.eqb] in *;
first [ lia | repeat match goal with u : uwd |- _ => destruct u; cbn [uw_cost] in * end; lia ].

Ltac tw_heapA_with HIx HPp MUx WMx mf :=
eapply (heapA_client_frame A4L HIx);
[ exact HPp
| eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPp MUx);
first [ solve [solve_frameW_withA HPp]
| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; first [ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ] ]
| exact WMx | match goal with H : mem_inv asegs mf |- _ => exact H end ].
Ltac tw_heapA HIx :=
lazymatch goal with |- HEAPA _ _ _ _ _ _ _ ?mf _ =>
match goal with
| HPk : HEAPA _ _ _ _ _ _ _ ?mk _, MUx : munch _ ?mk mf, WMx : wmono _ ?mk mf |- _ =>
first [ tw_heapA_with HIx HPk MUx WMx mf
| let HPp := fresh "HPp" in
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HPk (Permutation.perm_swap _ _ _) (Permutation.Permutation_refl _) (Permutation.Permutation_refl _)) as HPp;
tw_heapA_with HIx HPp MUx WMx mf ]
end end.

Ltac cells_exactA H :=
first [ exact H
| eapply rw_cells_recast; [ exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ] ].
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QgoP.
Import QbFI. Import Qwm6.
Import Qwm6.Mq4 QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Section Models.
Variable stop : byte -> byte -> bool.
Variable value : byte -> byte -> Z.

Fixpoint icmp_walk (l r : list byte) (k : nat) {struct k} : option (nat * Z) :=
match k with
| O => Some (O, 0)
| S k' =>
match l, r with
| a :: l', b :: r' =>
if stop a b then Some (1%nat, value a b)
else match icmp_walk l' r' k' with
| Some (j, v) => Some (S j, v)
| None => None
end
| _, _ => None
end
end.

Lemma icmp_walk_nread : forall l r k j v, icmp_walk l r k = Some (j, v) ->
(j <= k)%nat /\ (j <= length l)%nat /\ (j <= length r)%nat.
Proof.
intros l r k. revert l r.
induction k as [|k IH]; intros l r j v H; cbn in H.
- injection H as <- <-. cbn. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b).
+ injection H as <- <-. cbn. lia.
+ destruct (icmp_walk l r k) as [[j' v']|] eqn:E; [|discriminate].
injection H as <- <-. apply IH in E. cbn. lia.
Qed.
End Models.

Definition cmp_stop (a b : byte) : bool := (negb (bv_unsigned a =? bv_unsigned b) || (bv_unsigned a =? 0))%bool.
Definition cmp_sign (a b : byte) : Z := Z.sgn (bv_unsigned a - bv_unsigned b).

Definition casecmp_stop (a b : byte) : bool := (negb (lower8 (bv_unsigned a) =? lower8 (bv_unsigned b)) || (bv_unsigned a =? 0))%bool.
Definition casecmp_val (a b : byte) : Z := lower8 (bv_unsigned a) - lower8 (bv_unsigned b).

Definition istrncmp_model (l r : list byte) (n : Z) : option (nat * Z) := icmp_walk cmp_stop cmp_sign l r (Z.to_nat n).
Definition istrncasecmp_model (l r : list byte) (n : Z) : option (nat * Z) := icmp_walk casecmp_stop casecmp_val l r (Z.to_nat n).

Definition istrcmp_model (ls rs : list byte) : option (nat * Z) :=
icmp_walk cmp_stop cmp_sign (ls ++ [b0]) (rs ++ [b0]) (S (length ls)).

Section WalkFacts.
Variable stop : byte -> byte -> bool.
Variable value : byte -> byte -> Z.
Notation walk := (icmp_walk stop value).

Lemma icmp_walk_zero : forall fuel l r v, walk l r fuel = Some (0%nat, v) -> fuel = 0%nat /\ v = 0.
Proof.
intros [|fuel] l r v H; cbn in H.
- injection H as <-. auto.
- destruct l; [discriminate|]. destruct r; [discriminate|]. destruct (stop _ _); [discriminate|].
destruct (icmp_walk stop value _ _ _) as [[? ?]|]; discriminate.
Qed.

Lemma icmp_walk_before : forall fuel l r j v i, walk l r fuel = Some (j, v) -> (S i < j)%nat ->
exists a b, nth_error l i = Some a /\ nth_error r i = Some b /\ stop a b = false.
Proof.
induction fuel as [|fuel IH]; intros l r j v i H Hi; cbn in H.
- injection H as <- <-. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b) eqn:Hs.
+ injection H as <- <-. lia.
+ destruct (icmp_walk stop value l r fuel) as [[j' v']|] eqn:E; [|discriminate]. injection H as <- <-.
destruct i as [|i].
* exists a, b. cbn. auto.
* destruct (IH l r j' v' i E ltac:(lia)) as (a' & b' & Ha & Hb & Hs'). exists a', b'. cbn. auto.
Qed.

Lemma icmp_walk_last : forall fuel l r j v, walk l r fuel = Some (j, v) -> (1 <= j)%nat ->
exists a b, nth_error l (j - 1) = Some a /\ nth_error r (j - 1) = Some b /\
((stop a b = true /\ v = value a b) \/ (stop a b = false /\ j = fuel /\ v = 0)).
Proof.
induction fuel as [|fuel IH]; intros l r j v H Hj; cbn in H.
- injection H as <- <-. lia.
- destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|].
destruct (stop a b) eqn:Hs.
+ injection H as <- <-. exists a, b. cbn. auto.
+ destruct (icmp_walk stop value l r fuel) as [[j' v']|] eqn:E; [|discriminate]. injection H as <- <-.
destruct j' as [|j''].
* destruct (icmp_walk_zero _ _ _ _ E) as [-> ->]. exists a, b. cbn. split; [reflexivity|]. split; [reflexivity|]. right. auto.
* destruct (IH l r (S j'') v' E ltac:(lia)) as (a' & b' & Ha & Hb & Hc).
exists a', b'. replace (S (S j'') - 1)%nat with (S j'') by lia. replace (S j'' - 1)%nat with j'' in Ha, Hb by lia.
cbn [nth_error]. split; [exact Ha|]. split; [exact Hb|].
destruct Hc as [Hc | (Hs' & Hf & Hv)]; [left; exact Hc | right]. subst. auto.
Qed.

Lemma icmp_walk_pos : forall fuel l r j v, walk l r fuel = Some (j, v) -> (1 <= fuel)%nat -> (1 <= j)%nat.
Proof.
intros fuel l r j v H Hf. destruct j; [|lia]. destruct (icmp_walk_zero _ _ _ _ H) as [-> _]. lia.
Qed.
End WalkFacts.

Lemma cstr_nth_zero : forall (s : list byte) i c, ~ In b0 s -> nth_error (s ++ [b0]) i = Some c ->
(bv_unsigned c = 0 <-> i = length s).
Proof.
intros s i c Hn Hc. destruct (Nat.lt_ge_cases i (length s)) as [Hlt | Hge].
- rewrite nth_error_app1 in Hc by lia. split; [| lia]. intros Hz. exfalso. exact (notin0_nth s i c Hn Hc Hz).
- rewrite nth_error_app2 in Hc by lia. pose proof (nth_error_lt _ _ _ Hc) as L. cbn in L.
replace (i - length s)%nat with 0%nat in Hc by lia. cbn in Hc. injection Hc as <-. split; [lia | reflexivity].
Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_ISTRCMP : Z := 0x4fd30.
Definition istrcmp_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b lo : Z) (ls rs : list byte) (k : nat) (v : Z)
(Q : machine_state -> Prop),
istrcmp_model ls rs = Some (k, v) ->
unpoisoned asegs m A_SB a (Z.of_nat k) -> unpoisoned asegs m A_SB b (Z.of_nat k) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length ls) + 1 <= 2^47 -> Z.of_nat (length ls) + 1 < 2^40 -> 0 <= b -> b + Z.of_nat (length rs) + 1 <= 2^47 ->
(64 < Z.of_nat k -> app_mem a (Z.of_nat k) /\ app_mem b (Z.of_nat k)) ->
(a + Z.of_nat (length ls) + 1 <= lo \/ bv_unsigned sp <= a) -> (b + Z.of_nat (length rs) + 1 <= lo \/ bv_unsigned sp <= b) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 b -> ~ In b0 ls -> ~ In b0 rs ->
bytes_at asegs m a (ls ++ [b0]) -> bytes_at asegs m b (rs ++ [b0]) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' a (ls ++ [b0]) -> bytes_at asegs m' b (rs ++ [b0]) ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ISTRCMP) fc None m (seg_rom asegs)).

Definition A_ISTRNCMP : Z := 0x4fd34.
Definition A_ISTRNCASECMP : Z := 0x4fd38.
Definition istrn_spec_U (entry : Z) (model : list byte -> list byte -> Z -> option (nat * Z)) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b n lo : Z) (la lb : list byte) (k : nat) (v : Z)
(Q : machine_state -> Prop),
model la lb n = Some (k, v) ->
unpoisoned asegs m A_SB a (Z.of_nat k) -> unpoisoned asegs m A_SB b (Z.of_nat k) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length la) <= 2^47 -> 0 <= b -> b + Z.of_nat (length lb) <= 2^47 ->
(a + Z.of_nat (length la) <= lo \/ bv_unsigned sp <= a) -> (b + Z.of_nat (length lb) <= lo \/ bv_unsigned sp <= b) ->
a0 = Z_to_bv 64 a -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n -> 0 < n <= 64 ->
bytes_at asegs m a la -> bytes_at asegs m b lb ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
bytes_at asegs m' a la -> bytes_at asegs m' b lb ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Definition istrncmp_spec_U : Prop := istrn_spec_U A_ISTRNCMP istrncmp_model.
Definition istrncasecmp_spec_U : Prop := istrn_spec_U A_ISTRNCASECMP istrncasecmp_model.

Definition A_ISTRTOLL : Z := 0x4fddc.
Definition A_GOT_GUARD : Z := 0xe8f90.
Definition A_GUARD : Z := 0x645560.
Definition istrtoll_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A E lo : Z) (str : list byte) (e g ej : word)
(Q : machine_state -> Prop),
unpoisoned asegs m A_SB A (Z.of_nat (length str) + 1) -> unpoisoned asegs m A_SB E 8 -> asan_rt_ok m ->
(64 < Z.of_nat (length str) + 1 -> app_mem A (Z.of_nat (length str) + 1)) -> app_mem E 8 ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 E -> a2 = Z_to_bv 64 10 -> tp = Z_to_bv 64 A_TP ->
0 <= A -> A + Z.of_nat (length str) + 2 <= 2^47 -> Z.of_nat (length str) + 1 < 2^40 -> 0x647000 <= E -> E + 8 <= 2^47 ->
bytes_at asegs m A (str ++ [b0]) -> ~ In b0 str ->
rw_cells asegs m E [C8 ej] -> rw_cells asegs m (A_TP - 164) [C4 e] ->
bytes_at asegs m A_GOT_GUARD (le8 (Z_to_bv 64 A_GUARD)) -> bytes_at asegs m A_GUARD (le8 g) ->
(E + 8 <= lo \/ bv_unsigned sp <= E) ->
(A + Z.of_nat (length str) + 1 <= lo \/ bv_unsigned sp <= A) ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A) ->
(A + Z.of_nat (length str) + 1 <= A_TP - 164 \/ A_TP - 160 <= A) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' (j : Z) (e' : word),
munch [(E, E + 8); (A_TP - 164, A_TP - 160); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' E [C8 (Z_to_bv 64 (A + j))] -> 0 <= j <= Z.of_nat (length str) ->
bytes_at asegs m' A (str ++ [b0]) -> rw_cells asegs m' (A_TP - 164) [C4 e'] ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ISTRTOLL) fc None m (seg_rom asegs)).

End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QbFI. Import Qwm6.
Import QZsi.Mq1 Qhd4.Mq2.
Import Qwm6.Mq4 QlKV.Mqj.
Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.

Lemma lxor_ones64 : forall d, 0 <= d < 2^64 -> Z.lxor d 18446744073709551615 = 18446744073709551615 - d.
Proof.
intros d Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
assert (E : 18446744073709551615 - d = Z.lnot d mod 2^64) by (unfold Z.lnot; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia).
rewrite E. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 64) eqn:L.
- rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite xorb_false_r, andb_false_r.
apply Z.ltb_ge in L. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec d 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m8_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
intros x Hx.
replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3)
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
replace 18446744073709551608 with (Z.lnot 7 mod 2^64) by reflexivity.
rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 7 with (Z.ones 3). rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 3) eqn:L3.
- apply Z.ltb_lt in L3. rewrite Z.shiftl_spec_low by lia. cbn. rewrite andb_false_r. reflexivity.
- apply Z.ltb_ge in L3. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - 3 + 3) with i by lia. cbn.
destruct (Z.ltb i 64) eqn:L64.
+ rewrite andb_true_r. reflexivity.
+ rewrite andb_false_r. apply Z.ltb_ge in L64. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ro_C8_of_bytes_at : forall segs m a v, bytes_at segs m a (le8 v) -> ro_cells segs m a [C8 v].
Proof. intros segs m a v H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma ro_C1_of_bytes_at : forall segs m a b, bytes_at segs m a [b] -> ro_cells segs m a [C1 b].
Proof. intros segs m a b H. split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact H]. Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned.
unfold bv_wrap.
replace (bv_modulus 8) with 256 by reflexivity. replace (bv_half_modulus 8) with 128 by reflexivity.
rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ov_read1_of_ro : forall segs m A b, ro_cells segs m A [C1 b] -> ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [b].
Proof.
intros segs m A b H. pose proof (cells_at_read segs m A [C1 b] 0%nat (C1 b) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma size_test_n : forall n, 0 < n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.
Lemma size_test_big : forall n, (n = 0 \/ 65 <= n < 2^63) -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = true.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
apply negb_true_iff. apply Z.ltb_ge.
destruct Hn as [-> | Hn]; [change ((0 + -65) mod 2^64) with (2^64 - 65); lia|].
rewrite Z.mod_small by lia. lia.
Qed.

Lemma asan_rt_get : forall m a bs, asan_rt_ok m -> In (a, bs) a4_rt_cells -> bytes_at asegs m a bs.
Proof. intros m a bs H HI. unfold asan_rt_ok in H. rewrite Forall_forall in H. exact (H (a, bs) HI). Qed.
Ltac rt_in := cbn [a4_rt_cells a4_rt_consts app]; unfold A_GOT_SB, A_SB_CELL, A_SB; repeat (first [ left; reflexivity | right ]).

Tactic Notation "rt_cell" constr(RT) constr(a) "as" ident(H) :=
lazymatch type of RT with asan_rt_ok ?m => pose proof (asan_rt_get m a _ RT ltac:(rt_in)) as H; cbn [fst snd] in H end.

Lemma unpoisoned_sub_any : forall segs m SB s n s' n', unpoisoned segs m SB s n -> s <= s' -> s' + n' <= s + n -> 0 < n' ->
unpoisoned segs m SB s' n'.
Proof.
intros segs m SB s n s' n' (Hn & Ha & (v & Hb & Hv) & Hc) H1 H2 H3. split; [exact H3|]. split; [|split].
- intros g Hg. apply Ha. Z.div_mod_to_equations. lia.
- destruct (Z_lt_le_dec ((s' + n' - 1) / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
+ exists 0. split; [| left; reflexivity]. apply Ha. Z.div_mod_to_equations. lia.
+ assert (E : (s' + n' - 1) / 8 = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
exists v. rewrite E. split; [exact Hb |]. destruct Hv as [-> | [Hv1 Hv2]]; [left; reflexivity | right].
split; [exact Hv1|]. Z.div_mod_to_equations. lia.
- intros w Hw. apply Hc. Z.div_mod_to_equations. lia.
Qed.

Section RC__icpt. Context {RC__ : Q6q3.RunConsts}.

Lemma try_asan_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf2e99 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6aeb8) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma init_gate_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
mem_inv asegs m -> ro_cells asegs m 0xf2e98 [C1 (Z_to_bv 8 1)] ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0xf2e99 <= lo -> bv_unsigned ra mod 2 = 0 ->
(forall a0' a1' m', munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x6ab74) fc None m (seg_rom asegs)).
Proof.
intros until Q. intros MI FLAG ST LOS FLO RA K.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 16%nat ST.
do 5 step.
step. step. step.
step. rewrite ?sxb_small by lia. if_falsex.
do 4 step.
eapply K; [exact MU | exact WM | exact MI |].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.
End RC__icpt.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import QbFI. Import Qhd4 Qwm6. Import QGcC.
Import Qwm6.Mq4 QlKV.Mqi.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithHI.
Variable HIx : heap_iface_A A4L.

Lemma errno_shadowA : forall A LB LM FR B m md,
HEAPA A4L HIx A LB LM FR B m md -> ro_cells asegs m (A_ERRNO / 8 + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md HP.
pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ (A_ERRNO / 8) HP ltac:(unfold A_ERRNO; cbn; lia) ltac:(unfold A_ERRNO; cbn; lia)) as SH.
cbn [hl_sb hl_reg_globals hl_segs hla_base A4L A4H] in SH.
replace (img_shadow_val tokA_reg_globals (A_ERRNO / 8)) with 0 in SH by (vm_compute; reflexivity).
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact SH].
Qed.
End WithHI.
End RC__1.
End Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw. Import QPZI.Mq1.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqc.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition jo_get_type_A_entry : Z := 0x9c4b8.
Definition jo_is_type_A_entry : Z := 0x9c4b8.
Definition jo_get_object_A_entry : Z := 0x9d5e8.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Regs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).

Definition small_post (m : word -> option byte) (lo : Z) (v : word) : machine_state -> Prop :=
fun ms' => exists m', ret4x ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v m' ms'
/\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Definition small_pre (m : word -> option byte) (lo sbcell : Z) : Prop :=
mem_inv asegs m /\ stk asegs m lo (bv_unsigned sp) /\ lo <= bv_unsigned sp - 16 /\ alloc_ceiling <= lo /\
ro_cells asegs m A_GOT_SB [C8 (Z_to_bv 64 sbcell)] /\ ro_cells asegs m sbcell [C8 (Z_to_bv 64 A_SB)] /\
0 < sbcell /\ sbcell + 8 <= alloc_ceiling.

Lemma jo_get_type_null_A : forall m lo sbcell,
small_pre m lo sbcell ->
evt asegs (small_post m lo (Z_to_bv 64 0))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_type_A_entry) fc None m (seg_rom asegs)).
Proof.
intros m lo sbcell (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8). unfold jo_get_type_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hc8. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep. bstep. if_true. bstep. bstep. bstep.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma jo_get_type_A : forall m lo sbcell p ty rc tojs pb udel ud,
small_pre m lo sbcell ->
rw_cells asegs m p (jhdr_cells ty rc tojs pb udel ud) -> 0 < p -> p + 40 <= alloc_ceiling -> p mod 8 = 0 -> 0 <= ty < 2^31 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0)] -> p / 8 + A_SB + 1 <= alloc_ceiling ->
evt asegs (small_post m lo (Z_to_bv 64 ty))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_type_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ud. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) HDR Hp Hph Hal Hty SH0 HSH.
unfold jhdr_cells in HDR. unfold jo_get_type_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chk0.
bstep. norm_w32. bstep. bstep. bstep.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

Lemma jo_get_object_A : forall m lo sbcell p rc tojs pb udel ud t,
small_pre m lo sbcell ->
rw_cells asegs m p (jhdr_cells JT_OBJECT rc tojs pb udel ud ++ [C8 (Z_to_bv 64 t)]) -> 0 < p -> p + 48 <= alloc_ceiling -> p mod 8 = 0 ->
ro_cells asegs m (p / 8 + A_SB) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
p / 8 + A_SB + 6 <= alloc_ceiling ->
evt asegs (small_post m lo (Z_to_bv 64 t))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 jo_get_object_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until t. intros (MI & ST & LOS & LO & GOT & CELL & Hc0 & Hc8) HDR Hp Hph Hal SH HSH.
unfold jhdr_cells, JT_OBJECT in HDR. cbn [app] in HDR. unfold jo_get_object_A_entry, A_GOT_SB, A_SB in *.
unfold alloc_ceiling, sp_window_lo, stack_max_size in LO, Hph, Hc8, HSH. word_range sp SPR.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
carve_frame 16%nat ST.
bstep. bstep. bstep. if_falsex.
bstep. bstep. bstep.
asan_chk0.
bstep. bstep. bstep. if_false.
bstep.
asan_chkA.
bstep. bstep. bstep. bstep. bstep.
apply evt_done. eexists. split; [eexists _, _, _; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

End Regs.
End RC__1.
End Mqc.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QJjn.
Import QnCn.Mq0.
Import QbFI. Import Qhd4.
Import Qwm6.Mq4 QlKV.Mqh. Import QlKV.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition arr_capA (BS : list blk) : Z := snd (nth 2 BS (0, 0)) / 8.

Lemma arr_capA_jval : forall m kids BS p rc,
jval asegs A4F (Sarr kids) m BS p rc ->
exists a arr rest, BS = (p, 48) :: (a, AL_SZ) :: (arr, 8 * arr_capA BS) :: rest /\
Z.of_nat (length kids) <= arr_capA BS /\ 1 <= arr_capA BS /\ 8 * arr_capA BS < 2^64.
Proof.
intros m kids BS p rc J. cbn [jval] in J.
destruct J as (pb & PBS & REST & EBS & _ & a & ABS & ps & KBS & EREST & _ & AL & L1 & _ & _).
destruct AL as (arr & size & junk & EABS & Hlen & Hsz & _ & _). subst ABS REST BS.
exists a, arr, (concat KBS ++ PBS). unfold arr_capA. cbn [app nth snd].
rewrite (Z.mul_comm 8 size), Z.div_mul by lia. rewrite <- L1, (Z.mul_comm size 8). split; [reflexivity|]. lia.
Qed.

Definition arr_add_costA (cap len : Z) : Z := if len + 1 <? cap then 0 else 256 * cap + 512.
Definition arr_grownA (cap len cap' : Z) : Prop := (cap' = cap /\ len + 1 < cap) \/ (cap' = 2 * cap /\ cap <= len + 1).
Definition arr_shrink_costA (cap len : Z) : Z := if len =? cap then 0 else 16 * (8 * Z.max len 1) + 512.
Definition new_array_costA : Z := 16 * 48 + 512 + (2048 + 128 * 32) + 512.

Section AJoStmts.
Variable HIx : heap_iface_A A4L.
Variable G : (word -> option byte) -> Prop.

Definition jo_preA (A : ASA A4L HIx) (LBall LM : list blk) (FRS : list frame) (B : bud) (m : word -> option byte) (md : config)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAPA A4L HIx A LBall LM FRS B m md /\
stk asegs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hiA_top A4L HIx /\
rw_cells asegs m A_ERRNO [C4 errv] /\
tp = Z_to_bv 64 A_TP /\ bv_unsigned ra mod 2 = 0.

Definition jo_post_frameA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : config) : Prop :=
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' /\
(exists errv', rw_cells asegs m' A_ERRNO [C4 errv']).

Definition jo_new_container_A_stmt (entry stkb costB costD ura : Z) (s : jshape) (capok : list blk -> Prop) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
jo_preA A LB LM FRS B m md sp tp ra lo stkb errv -> G m ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 ura) u ->
costB <= bB B -> uw_cost u + costD <= bD B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - costB <= bB B' -> bD B - (uw_cost u + costD) <= bD B' ->
((r = 0 /\ HEAPA A4L HIx A' LB LM FRS B' m' md') \/
(r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ capok BS /\ HEAPA A4L HIx A' (BS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_array_add_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v : Z)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA A (ABS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> jopt asegs A4F vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
Z.of_nat (length kids) + 1 < 2^28 ->
arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bD B <= bD B' ->
((r = 0 /\ exists ABS', jval asegs A4F (Sarr (kids ++ [vs])) m' ABS' p 1 /\
arr_grownA (arr_capA ABS) (Z.of_nat (length kids)) (arr_capA ABS') /\
bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md' /\
(forall w wv, jtx (Sarr kids) ABS = Some (w, []) -> jtx_opt vs VBS = Some (wv, []) ->
jtx (Sarr (kids ++ [vs])) ABS' = Some (w + (2 + wv), []))) \/
(r = 2^64 - 1 /\ bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
jval asegs A4F (Sarr kids) m' ABS p 1 /\ jopt asegs A4F vs m' VBS v /\
HEAPA A4L HIx A' (ABS ++ VBS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Definition jo_array_shrink_A_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_preA A (ABS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
Z.of_nat (length kids) < 2^28 ->
arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
(exists ABS', jval asegs A4F (Sarr kids) m' ABS' p 1 /\
(arr_capA ABS' = arr_capA ABS \/ (r = 0 /\ arr_capA ABS' = Z.max (Z.of_nat (length kids)) 1)) /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md') ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End AJoStmts.

Definition jo_new_array_A (HIx : heap_iface_A A4L) :=
jo_new_container_A_stmt HIx (fun _ => True) 0xa074c (32 + 32 + 4096) new_array_costA 0 0xa0770 (Sarr []) (fun BS => arr_capA BS = 32).
Definition jo_array_add_A (HIx : heap_iface_A A4L) := jo_array_add_A_stmt HIx 0xa097c (16 + 96 + 4096).
Definition jo_array_shrink_A (HIx : heap_iface_A A4L) := jo_array_shrink_A_stmt HIx 0xa0a14 (16 + 48 + 4096).

End RC__1.
End Mqd.

Module Mqe.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn Q8tj.
Import QSL3.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Definition GHASHA : Z := 0xec960.
Definition GSEEDA : Z := 0xec980.
Definition A_GOT_LHEQ : Z := 0xe8ea8.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lh_globA (m : word -> option byte) : Prop :=
rw_cells asegs m GHASHA [C8 (Z_to_bv 64 (fn_lh_char_hash A4F))]
/\ (exists seed : word, rw_cells asegs m GSEEDA [C4 seed]).

Lemma lh_globA_client : forall LB SP m m', heap_pres A4H LB SP m m' -> lh_globA m -> lh_globA m'.
Proof.
intros LB SP m m' HPR (G1 & [seed G2]). split.
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. unfold GHASHA in Ha.
cbn. unfold a4_client_static. lia.
- exists seed. eapply (heap_pres_rw_cells A4H); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. unfold GSEEDA in Ha.
cbn. unfold a4_client_static. lia.
Qed.

Lemma lh_globA_frame : forall m m' W,
lh_globA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => (GHASHA + 8 <= fst iv \/ snd iv <= GHASHA) /\ (GSEEDA + 4 <= fst iv \/ snd iv <= GSEEDA)) W ->
lh_globA m'.
Proof.
intros m m' W (G1 & [seed G2]) MU WM DJ. split.
- eapply (rw_cells_transport asegs W m m'); [exact G1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(D1 & _) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
- exists seed. eapply (rw_cells_transport asegs W m m'); [exact G2 | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
clear -DJ. induction W as [|[a b] W IH]; cbn; [exact I|]. apply Forall_cons_iff in DJ as [(_ & D1) DJ]. cbn in D1. split; [lia | apply IH; exact DJ].
Qed.

Definition rtc_lheq_stmt (HIx : heap_iface_A A4L) : Prop :=
forall A LB LM FR B m md, HEAPA A4L HIx A LB LM FR B m md ->
bytes_at asegs m A_GOT_LHEQ (le8 (Z_to_bv 64 (fn_lh_char_equal A4F))).

Section WithHI.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma blk_ne_01A : forall A a n b k LB LM FR B m md,
HEAPAx A ((a, n) :: (b, k) :: LB) LM FR B m md -> a <> b.
Proof.
intros A a n b k LB LM FR B m md HP E. subst.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
apply Hni. left. reflexivity.
Qed.

Lemma blocks2A : forall A a na b nb LB LM FR B m md,
HEAPAx A ((a, na) :: (b, nb) :: LB) LM FR B m md ->
(a mod 16 = 0 /\ 0 < a /\ a + na <= alloc_ceiling /\ (a + na <= hl_img_lo A4H \/ hl_img_hi A4H <= a))
/\ (b mod 16 = 0 /\ 0 < b /\ b + nb <= alloc_ceiling /\ (b + nb <= hl_img_lo A4H \/ hl_img_hi A4H <= b))
/\ (a + na <= b \/ b + nb <= a).
Proof.
intros A a na b nb LB LM FR B m md HP.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a na HP ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ a na HP ltac:(apply in_or_app; left; left; reflexivity)) as Hia.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b nb HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (_ & Hal2 & Hlo2 & Hhi2 & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b nb HP ltac:(apply in_or_app; left; right; left; reflexivity)) as Hia2.
pose proof (blk_ne_01A _ _ _ _ _ _ _ _ _ _ _ HP) as Hne.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a na b nb HP ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hne) as Hdj.
repeat split; try assumption.
Qed.

Lemma lh_heap_factsA : forall A t tbl size es LB LM FR B m md,
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FR B m md ->
(t mod 16 = 0 /\ 0 < t /\ t + 56 <= alloc_ceiling /\ (t + 56 <= hl_img_lo A4H \/ hl_img_hi A4H <= t))
/\ (tbl mod 16 = 0 /\ 0 < tbl /\ tbl + 40 * size <= alloc_ceiling /\ (tbl + 40 * size <= hl_img_lo A4H \/ hl_img_hi A4H <= tbl))
/\ (t + 56 <= tbl \/ tbl + 40 * size <= t)
/\ (forall e, In e es ->
0 <= le_kn e /\ 0 < le_k e /\ le_k e + le_kn e <= alloc_ceiling /\ (le_k e + le_kn e <= hl_img_lo A4H \/ hl_img_hi A4H <= le_k e)
/\ (t + 56 <= le_k e \/ le_k e + le_kn e <= t) /\ (tbl + 40 * size <= le_k e \/ le_k e + le_kn e <= tbl)).
Proof.
intros A t tbl size es LB LM FR B m md HP. unfold lh_blocks in HP. cbn [app] in HP.
destruct (blocks2A _ _ _ _ _ _ _ _ _ _ _ HP) as (F1 & F2 & F12). split; [exact F1|]. split; [exact F2|]. split; [exact F12|].
intros e He.
assert (Hin : In (le_k e, le_kn e) (((t, 56) :: (tbl, 40 * size) :: map (fun e => (le_k e, le_kn e)) es ++ LB) ++ LM)).
{ apply in_or_app. left. right; right. apply in_or_app. left. apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as Himg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn [map blk_addr fst app] in ND.
inversion ND as [|x l Hnt ND1]; subst. inversion ND1 as [|y l' Hntb ND2]; subst.
assert (NEt : t <> le_k e).
{ intros E. apply Hnt. rewrite E. right. rewrite !map_app. apply in_or_app. left. apply in_or_app. left. apply in_map_iff. exists (le_k e, le_kn e). split; [reflexivity|].
apply in_map_iff. exists e. split; [reflexivity | exact He]. }
assert (NEb : tbl <> le_k e).
{ intros E. apply Hntb. rewrite E. rewrite !map_app. apply in_or_app. left. apply in_or_app. left. apply in_map_iff. exists (le_k e, le_kn e). split; [reflexivity|].
apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ t 56 (le_k e) (le_kn e) HP ltac:(apply in_or_app; left; left; reflexivity) Hin NEt) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) (le_k e) (le_kn e) HP ltac:(apply in_or_app; left; right; left; reflexivity) Hin NEb) as D2.
repeat split; try assumption; lia.
Qed.

Lemma lh_newkey_factsA : forall A t tbl size es k kn LB LM FR B m md,
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FR B m md ->
0 <= kn /\ 0 < k /\ k + kn <= alloc_ceiling /\ (k + kn <= hl_img_lo A4H \/ hl_img_hi A4H <= k)
/\ (t + 56 <= k \/ k + kn <= t) /\ (tbl + 40 * size <= k \/ k + kn <= tbl) /\ ~ In k (map le_k es).
Proof.
intros A t tbl size es k kn LB LM FR B m md HP.
assert (HinK : In (k, kn) ((lh_blocks t tbl size es ++ (k, kn) :: LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as (Hn & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as Himg.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
assert (NT : t <> k).
{ intros ->. eapply (nodup_prefix_suffix (lh_blocks k tbl size es) (((k, kn) :: LB) ++ LM) k 56 kn ND); [left; reflexivity | left; reflexivity]. }
assert (NB : tbl <> k).
{ intros ->. eapply (nodup_prefix_suffix (lh_blocks t k size es) (((k, kn) :: LB) ++ LM) k (40 * size) kn ND); [right; left; reflexivity | left; reflexivity]. }
assert (NK : ~ In k (map le_k es)).
{ intros IN. apply in_map_iff in IN as (e & <- & He).
eapply (nodup_prefix_suffix (lh_blocks t tbl size es) (((le_k e, kn) :: LB) ++ LM) (le_k e) (le_kn e) kn ND); [| left; reflexivity].
right; right. apply in_map_iff. exists e. split; [reflexivity | exact He]. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ t 56 k kn HP ltac:(apply in_or_app; left; left; reflexivity) HinK NT) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tbl (40 * size) k kn HP ltac:(apply in_or_app; left; right; left; reflexivity) HinK NB) as D2.
repeat split; try assumption; lia.
Qed.
End WithHI.

End RC__1.
End Mqe.

Module Mqf.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition src_globA (b n : Z) : Prop :=
hl_img_lo A4H + 64 <= b /\ b + n + 64 <= hl_img_hi A4H
/\ ((forall a, b <= a < b + n -> hl_client_static A4H a) \/ (forall a, b <= a < b + n -> ro_addr asegs (wa a) = true))
/\ (forall g, b / 8 <= g < (b + n - 1) / 8 -> img_shadow_val (hl_reg_globals A4L) g = 0)
/\ (img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8) = 0
\/ (0 < img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8) < 8 /\ (b + n - 1) mod 8 < img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8))).

Definition src_locA (LB : list blk) (FRS : list frame) (b n : Z) : Prop :=
(exists sa sk, In (sa, sk) LB /\ sa <= b /\ b + n <= sa + sk)
\/ (exists Fs ks, In (Fs, ks) FRS /\ Fs <= b /\ b + n <= Fs + fr_size ks - 8)
\/ src_globA b n.

Lemma unpoisoned_of_shadow_fun : forall segs m SB s n glo ghi (V : Z -> Z),
(forall g, glo <= g < ghi -> bytes_at segs m (g + SB) [Z_to_bv 8 (V g)]) ->
glo + 8 <= s / 8 -> (s + n - 1) / 8 + 8 <= ghi -> 0 < n -> 0 <= glo + SB ->
(forall g, s / 8 <= g < (s + n - 1) / 8 -> V g = 0) ->
(V ((s + n - 1) / 8) = 0 \/ (0 < V ((s + n - 1) / 8) < 8 /\ (s + n - 1) mod 8 < V ((s + n - 1) / 8))) ->
unpoisoned segs m SB s n.
Proof.
intros segs m SB s n glo ghi V Z0 Hlo Hhi Hn Hpos VZ VL. split; [exact Hn|]. split; [|split].
- intros g Hg. rewrite <- (VZ g Hg). apply Z0. Z.div_mod_to_equations. lia.
- exists (V ((s + n - 1) / 8)). split; [| exact VL]. apply Z0. Z.div_mod_to_equations. lia.
- intros w Hw.
assert (B : forall i, 0 <= i < 8 -> bytes_at segs m (w * 8 + i) [Z_to_bv 8 (V (w * 8 + i - SB))]).
{ intros i Hi. replace (w * 8 + i) with ((w * 8 + i - SB) + SB) at 1 by lia. apply Z0. Z.div_mod_to_equations. lia. }
exists (map (fun i => Z_to_bv 8 (V (w * 8 + Z.of_nat i - SB))) (seq 0 8)). split; [reflexivity|].
destruct (B 0 ltac:(lia)) as (Hw0 & _ & _).
destruct (B 7 ltac:(lia)) as (_ & Hw7 & _). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in Hw7.
split; [lia|]. split; [cbn [length map seq Z.of_nat Pos.of_succ_nat Pos.to_nat]; lia|].
intros i Hi. cbn [length map seq] in Hi.
destruct (B (Z.of_nat i) ltac:(lia)) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)). cbn [nth_error] in Hb.
rewrite Z.add_0_r in Hb. rewrite Hb. clear -Hi.
do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi. lia.
Qed.

Lemma client_range_incl : forall (LB LB' : list blk) SP A n,
(forall b, In b LB -> In b LB') -> client_range A4H LB SP A n -> client_range A4H LB' SP A n.
Proof.
intros LB LB' SP A n Hsub [H | [H | (b & Hb & Hr)]]; [left; exact H | right; left; exact H | right; right].
exists b. split; [apply Hsub; exact Hb | exact Hr].
Qed.

Lemma ro_range_bytes_pres : forall m m' b (bs : list byte),
mem_inv asegs m -> mem_inv asegs m' -> (forall a, b <= a < b + Z.of_nat (length bs) -> ro_addr asegs (wa a) = true) ->
bytes_at asegs m b bs -> bytes_at asegs m' b bs.
Proof.
intros m m' b bs MI MI' RO (B0 & B1 & BY). split; [exact B0|]. split; [exact B1|].
intros i Hi. rewrite <- (BY i Hi). specialize (RO (b + Z.of_nat i) ltac:(lia)).
unfold mrd. destruct (m' (wa (b + Z.of_nat i))) eqn:E'; [pose proof (MI' _ _ E'); congruence|].
destruct (m (wa (b + Z.of_nat i))) eqn:E; [pose proof (MI _ _ E); congruence| reflexivity].
Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma src_loc_facts : forall A pb buf cap LB LM FRS B m md b n,
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md -> src_locA LB FRS b n -> 0 <= n ->
0 < b /\ b + n <= alloc_ceiling /\ (b + n <= buf \/ buf + cap <= b) /\ (b + n <= pb \/ pb + PB_SZ <= b) /\
((b + n <= hl_img_lo A4H \/ hl_img_hi A4H <= b) \/ src_globA b n) /\ (n <= 64 \/ app_mem b n).
Proof.
intros A pb buf cap LB LM FRS B m md b n HP SRCB Hn.
pose proof alloc_ceiling_range as ACR.
destruct SRCB as [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | SG]].
- assert (IN : In (sa, sk) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; right; exact Hsrc).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP IN) as (_ & _ & Hslo & Hshi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ sa sk HP IN) as Hsimg.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ sa sk HP IN) as Hsam. cbn [hl_sb A4L] in Hsam.
assert (Hsane : sa <> pb /\ sa <> buf).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite map_app in ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x2 l2 Hni2 Hnd2]; subst.
split; intros E; subst sa; [apply Hni; right | apply Hni2]; apply in_or_app; left; exact (in_map blk_addr _ _ Hsrc). }
destruct Hsane as [Hsapb Hsabuf].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ buf cap sa sk HP ltac:(right; left; reflexivity) IN ltac:(congruence)) as D1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ pb PB_SZ sa sk HP ltac:(left; reflexivity) IN ltac:(congruence)) as D2.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg |- *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
destruct (Z.le_gt_cases n 64) as [Hle|Hgt]; [left; exact Hle | right].
unfold app_mem, A_HMB, A_SB in *. lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & _ & HF0 & HFc & HFimg & _).
pose proof (fr_size_pos ks ltac:(lia)) as HSZ.
assert (INb : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (right; left; reflexivity).
assert (INp : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (left; reflexivity).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HFs INb) as D1.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HFs INp) as D2.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as AM. cbn [hl_sb A4L] in AM.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg |- *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
destruct (Z.le_gt_cases n 64) as [Hle|Hgt]; [left; exact Hle | right].
unfold app_mem, A_HMB, A_SB in *. lia.
-
pose proof SG as (G1 & G2 & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as Ib.
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ pb PB_SZ HP ltac:(apply in_or_app; left; left; reflexivity)) as Ip.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ buf cap HP ltac:(apply in_or_app; left; right; left; reflexivity)) as (Hc0 & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in G1, G2, Ib, Ip |- *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; exact SG|].
destruct (Z.le_gt_cases n 64) as [Hle|Hgt]; [left; exact Hle | right].
unfold app_mem, A_HMB, A_SB in *. lia.
Qed.

Lemma src_loc_range : forall LB LM FRS SP b n,
src_locA LB FRS b n -> client_range A4H (LB ++ LM ++ fr_ivs A4L FRS) SP b n \/ (forall a, b <= a < b + n -> ro_addr asegs (wa a) = true).
Proof.
intros LB LM FRS SP b n [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | (_ & _ & [SG | RO] & _)]].
3:{ left; right; left. exact SG. }
3:{ right. exact RO. }
- left; right; right. exists (sa, sk). cbn. split; [apply in_or_app; left; exact Hsrc | lia].
- left; right; right. exists (Fs, fr_size ks - 8). cbn. split; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFs | lia].
Qed.

Lemma src_loc_bytes_pres : forall LBs LB LM FRS SP m m' b (src : list byte),
heap_pres A4H LBs SP m m' -> mem_inv asegs m -> mem_inv asegs m' ->
(forall bb, In bb (LB ++ LM ++ fr_ivs A4L FRS) -> In bb LBs) ->
src_locA LB FRS b (Z.of_nat (length src)) -> bytes_at asegs m b src -> bytes_at asegs m' b src.
Proof.
intros LBs LB LM FRS SP m m' b src HPR MI MI' SUB SRCB SRC.
destruct (src_loc_range LB LM FRS SP b _ SRCB) as [CR | RO].
- eapply (heap_pres_bytes_at A4H); [exact HPR | exact SRC | eapply client_range_incl; [exact SUB | exact CR]].
- exact (ro_range_bytes_pres m m' b src MI MI' RO SRC).
Qed.

Lemma src_loc_fresh : forall A r nr LBX LM FRS B m md LB b n,
HEAPAx A ((r, nr) :: LBX) LM FRS B m md -> src_locA LB FRS b n -> 0 <= n ->
(forall sa sk, In (sa, sk) LB -> In (sa, sk) LBX) ->
r + nr <= b \/ b + n <= r.
Proof.
intros A r nr LBX LM FRS B m md LB b n HP [(sa & sk & Hsrc & Hsa & Hsk) | [(Fs & ks & HFs & HFa & HFk) | (G1 & G2 & _)]] Hn Hsub.
3:{ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r nr HP ltac:(left; reflexivity)) as Ir.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r nr HP ltac:(left; reflexivity)) as (Hr0 & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in G1, G2, Ir. lia. }
- assert (IN : In (sa, sk) (((r, nr) :: LBX) ++ LM)) by (apply in_or_app; left; right; apply Hsub; exact Hsrc).
assert (Hne : r <> sa).
{ pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn in ND. inversion ND as [|x l Hni Hnd]; subst.
intros ->. apply Hni. rewrite map_app. apply in_or_app. left. exact (in_map blk_addr _ _ (Hsub _ _ Hsrc)). }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r nr sa sk HP ltac:(left; reflexivity) IN Hne). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & _). pose proof (fr_size_pos ks ltac:(lia)).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HFs ltac:(left; reflexivity)). lia.
Qed.

Lemma unpoisoned_of_glob : forall A LB LM FRS B m md b n,
HEAPAx A LB LM FRS B m md -> src_globA b n -> 0 < n -> unpoisoned asegs m A_SB b n.
Proof.
intros A LB LM FRS B m md b n HP (G1 & G2 & _ & GZ & GL) Hn.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in G1, G2.
eapply (unpoisoned_of_shadow_fun asegs m A_SB b n (hl_img_lo A4H / 8) (hl_img_hi A4H / 8) (img_shadow_val (hl_reg_globals A4L)));
cbn [hl_img_lo hl_img_hi hla_base A4L A4H]; unfold A_SB; try (Z.div_mod_to_equations; lia); try assumption.
intros g Hg. pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ g HP) as SI. cbn [hl_img_lo hl_img_hi hl_sb hla_base A4L A4H] in SI.
apply SI; Z.div_mod_to_equations; lia.
Qed.

Lemma unpoisoned_pres_heap : forall LST SP m m' s n cA cK,
unpoisoned asegs m A_SB s n -> heap_pres A4H LST SP m m' ->
In (cA, cK) LST -> cA <= shadow_span_lo A_SB s -> shadow_span_hi A_SB s n <= cA + cK ->
unpoisoned asegs m' A_SB s n.
Proof.
intros LST SP m m' s n cA cK (Hn & GZ & (v & Hv & Hvr) & WRD) HPR Hin Hlo Hhi.
unfold shadow_span_lo, shadow_span_hi in *.
split; [exact Hn|]. split; [| split].
- intros g Hg. eapply (heap_pres_bytes_at A4H); [exact HPR | exact (GZ g Hg) |].
eapply client_range_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- exists v. split; [| exact Hvr]. eapply (heap_pres_bytes_at A4H); [exact HPR | exact Hv |].
eapply client_range_block; [exact Hin | Z.div_mod_to_equations; lia | cbn; Z.div_mod_to_equations; lia].
- intros w Hw. destruct (WRD w Hw) as (bs & Hlen & Hbs). exists bs. split; [exact Hlen|].
eapply (heap_pres_bytes_at A4H); [exact HPR | exact Hbs |].
eapply client_range_block; [exact Hin | Z.div_mod_to_equations; lia | rewrite Hlen; cbn; Z.div_mod_to_equations; lia].
Qed.

Lemma unpoisoned_pres_frame : forall A LB LM FRS B m0 md LBX SP m m' Fs ks b n,
HEAPAx A LB LM FRS B m0 md -> In (Fs, ks) FRS -> Fs <= b -> b + n <= Fs + fr_size ks - 8 ->
unpoisoned asegs m A_SB b n -> heap_pres A4H (LBX ++ LM ++ fr_ivs A4L FRS) SP m m' ->
unpoisoned asegs m' A_SB b n.
Proof.
intros A LB LM FRS B m0 md LBX SP m m' Fs ks b n HP HFs HFa HFk UPS HPR.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFs) as (Hks & HFal & HF0 & HFc & _).
pose proof UPS as (Hn & _).
eapply unpoisoned_pres_heap; [exact UPS | exact HPR | apply in_or_app; right; apply in_or_app; right; apply fr_ivs_shadow; exact HFs | |].
- unfold shadow_span_lo, shad. cbn [hl_sb A4L]. unfold A_SB.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
Z.div_mod_to_equations. lia.
- unfold shadow_span_hi, shad. cbn [hl_sb A4L]. unfold A_SB. rewrite (fr_size_shadow ks) in HFk by lia.
assert (HF8 : Fs mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size ks)); [| apply Z.mod_divide; [pose proof (fr_size_pos ks ltac:(lia)); lia | exact HFal]].
exists (2 ^ ks). unfold fr_size. lia. }
unfold fr_shadow_len in *. Z.div_mod_to_equations. lia.
Qed.
End WithIface.

Lemma utf8rep_src_globA : src_globA 0xec920 3.
Proof.
unfold src_globA. cbn [hl_img_lo hl_img_hi hla_base A4L A4H hl_client_static hl_reg_globals].
split; [lia|]. split; [lia|]. split; [left; intros a Ha; unfold a4_client_static; lia|].
split; [intros g Hg; exfalso; change (0xec920 / 8) with 121124 in Hg; change ((0xec920 + 3 - 1) / 8) with 121124 in Hg; lia|].
right. vm_compute. repeat split; reflexivity.
Qed.
Lemma utf8rep_src_locA : forall LB FRS, src_locA LB FRS 0xec920 3.
Proof. intros. right; right. exact utf8rep_src_globA. Qed.

Lemma ro_addr_rodata_A : forall a, 0x10000 <= a < 0x3bfc0 -> ro_addr asegs (wa a) = true.
Proof.
intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia.
unfold asegs, AsanUbsan.M.loaded_segments. cbn -[Z.leb Z.ltb Z.add Z.of_N].
repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; try reflexivity;
exfalso; repeat match goal with
| Hb : (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in Hb as [Hb | Hb]
| Hb : (_ <=? _) = false |- _ => apply Z.leb_gt in Hb
| Hb : (_ <? _) = false |- _ => apply Z.ltb_ge in Hb
| Hb : (_ && _)%bool = true |- _ => apply andb_prop in Hb as [? ?]
| Hb : (_ <=? _) = true |- _ => apply Z.leb_le in Hb
| Hb : (_ <? _) = true |- _ => apply Z.ltb_lt in Hb
end; cbn in *; lia.
Qed.
Fixpoint zrange (lo : Z) (k : nat) : list Z := match k with O => [] | S k' => lo :: zrange (lo + 1) k' end.
Lemma zrange_in : forall k lo g, lo <= g < lo + Z.of_nat k -> In g (zrange lo k).
Proof. induction k as [|k IH]; intros lo g H; [lia|]. cbn [zrange]. destruct (Z.eq_dec g lo) as [->|NE]; [left; reflexivity| right; apply IH; lia]. Qed.
Definition src_ro_chk (b n : Z) : bool :=
(0x10000 + 64 <=? b) && (b + n + 64 <=? 0x3bfc0) && (0 <? n)
&& forallb (fun g => img_shadow_val (hl_reg_globals A4L) g =? 0) (zrange (b / 8) (Z.to_nat ((b + n - 1) / 8 - b / 8)))
&& (let v := img_shadow_val (hl_reg_globals A4L) ((b + n - 1) / 8) in (v =? 0) || ((0 <? v) && (v <? 8) && ((b + n - 1) mod 8 <? v))).
Lemma src_globA_of_chk : forall b n, src_ro_chk b n = true -> src_globA b n.
Proof.
intros b n H. unfold src_ro_chk in H.
repeat match type of H with (_ && _)%bool = true => let H' := fresh "C" in apply andb_prop in H as [H H'] end.
apply Z.leb_le in H. apply Z.leb_le in C2. apply Z.ltb_lt in C1.
unfold src_globA. cbn [hl_img_lo hl_img_hi hla_base A4L A4H]. split; [lia|]. split; [lia|].
split; [right; intros a Ha; apply ro_addr_rodata_A; lia|]. split.
- intros g Hg. rewrite forallb_forall in C0. apply Z.eqb_eq. apply C0. apply zrange_in. lia.
- cbv zeta in C. apply orb_prop in C as [C|C]; [left; apply Z.eqb_eq; exact C| right].
repeat match type of C with (_ && _)%bool = true => let H' := fresh "D" in apply andb_prop in C as [C H'] end.
apply Z.ltb_lt in C. apply Z.ltb_lt in D0. apply Z.ltb_lt in D. lia.
Qed.

Lemma esc_src_globA : forall b, In b [0x231a0; 0x231c0; 0x231e0; 0x23200; 0x23220] -> src_globA b 1.
Proof. intros b Hb. cbn in Hb. repeat (destruct Hb as [<-|Hb]; [apply src_globA_of_chk; vm_compute; reflexivity|]). destruct Hb. Qed.
Lemma esc_src_locA : forall LB FRS b, In b [0x231a0; 0x231c0; 0x231e0; 0x23200; 0x23220] -> src_locA LB FRS b 1.
Proof. intros. right; right. apply esc_src_globA. assumption. Qed.
End RC__1.
End Mqf.

Module Mqg.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QZsi.Mq1.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma lxor_ones64 : forall d, 0 <= d < 2^64 -> Z.lxor d 18446744073709551615 = 18446744073709551615 - d.
Proof.
intros d Hd. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec.
assert (E : 18446744073709551615 - d = Z.lnot d mod 2^64) by (unfold Z.lnot; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia).
rewrite E. rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 64) eqn:L.
- rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite xorb_false_r, andb_false_r.
apply Z.ltb_ge in L. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec d 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_m8_64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
intros x Hx.
replace (x / 8 * 8) with (Z.shiftl (Z.shiftr x 3) 3)
by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec.
replace 18446744073709551608 with (Z.lnot 7 mod 2^64) by reflexivity.
rewrite <- Z.land_ones by lia. rewrite Z.land_spec, Z.lnot_spec by lia.
change 7 with (Z.ones 3). rewrite !Z.testbit_ones_nonneg by lia.
destruct (Z.ltb i 3) eqn:L3.
- apply Z.ltb_lt in L3. rewrite Z.shiftl_spec_low by lia. cbn. rewrite andb_false_r. reflexivity.
- apply Z.ltb_ge in L3. rewrite Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia.
replace (i - 3 + 3) with i by lia. cbn.
destruct (Z.ltb i 64) eqn:L64.
+ rewrite andb_true_r. reflexivity.
+ rewrite andb_false_r. apply Z.ltb_ge in L64. rewrite Z.bits_above_log2; try lia.
destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (m := 2^64); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma ro_CB8_of_bytes_at : forall segs m a w, length w = 8%nat -> bytes_at segs m a w -> ro_cells segs m a [CB 8 w].
Proof. intros segs m a w Hl H. split; [cbn; rewrite Hl; split; [reflexivity|exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact H]. Qed.

Lemma amemset_real_specZ :
forall ra sp gp tp t0 t1 t2 s0 s1 (cv : word) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D n : Z) (junk : list byte),
0 <= D < 2^64 -> D + n <= 2^64 -> 0 <= n < 2^63 ->
rw_cells asegs m D [CB (Z.to_nat n) junk] ->
mem_inv asegs m ->
evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 (bv_unsigned cv mod 256)) (Z.to_nat n))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) cv (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdde14) fc None m (seg_rom asegs)).
Proof.
intros until junk. intros HD HDn Hn DST MI.
pose proof (memset_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) cv (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk) as X.
rewrite (unsigned_lit D), (unsigned_lit n) in X by lia.
eapply evt_mono; [eapply X; [exact DST | exact MI] |].
intros ms' P. unfold memset_post in P. rewrite (unsigned_lit D), (unsigned_lit n) in P by lia. exact P.
Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned.
unfold bv_wrap.
replace (bv_modulus 8) with 256 by reflexivity. replace (bv_half_modulus 8) with 128 by reflexivity.
rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ov_read1_of_ro : forall segs m A b, ro_cells segs m A [C1 b] -> ov_read_bytes segs m (Z_to_bv 64 A) 1 = Some [b].
Proof.
intros segs m A b H. pose proof (cells_at_read segs m A [C1 b] 0%nat (C1 b) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma size_test_n : forall n, 0 < n <= 64 -> negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (n + -65))) = false.
Proof.
intros n Hn. unfold bv_ltu. rewrite !unsigned_lit_wrap.
replace ((-65) mod 2^64) with (2^64 - 65) by reflexivity.
replace ((n + -65) mod 2^64) with (2^64 + n - 65) by (Z.div_mod_to_equations; lia).
apply negb_false_iff. apply Z.ltb_lt. lia.
Qed.

Lemma ov_read8_of_ro : forall segs m A w, ro_cells segs m A [CB 8 w] -> ov_read_bytes segs m (Z_to_bv 64 A) 8 = Some w.
Proof.
intros segs m A w H. pose proof (cells_at_read segs m A [CB 8 w] 0%nat (CB 8 w) H eq_refl) as X.
cbn [csize cbytes] in X. unfold wa in X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma bytes_at_zero_run : forall segs m a k,
0 <= a -> a + Z.of_nat k <= 2^64 ->
(forall i, 0 <= i < Z.of_nat k -> bytes_at segs m (a + i) [Z_to_bv 8 0]) ->
bytes_at segs m a (repeat (Z_to_bv 8 0) k).
Proof.
intros segs m a k. revert a. induction k as [|k IH]; intros a Ha Hk HB.
- cbn. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- change (repeat (Z_to_bv 8 0) (S k)) with ([Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) k).
apply bytes_at_app. split.
+ specialize (HB 0 ltac:(lia)). rewrite Z.add_0_r in HB. exact HB.
+ change (Z.of_nat (length [Z_to_bv 8 0])) with 1. apply IH; [lia | lia |].
intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply HB. lia.
Qed.
End Mqg.

Module Mqh.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.

Ltac asan_rechkA := step; rewrite ?sxb_zero, ?zxb_zero; step; first [ if_false | if_true ].

Tactic Notation "asan_rechkM" integer(n) := step; rewrite ?sxb_zero, ?zxb_zero; do n step; step; first [ if_false | if_true ].
Tactic Notation "asan_chkM" integer(n) :=
step; step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; do n step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Ltac lit_prefix_cells cs :=
lazymatch cs with
| ?c :: ?r => let r' := lit_prefix_cells r in constr:(c :: r')
| @nil _ => constr:(@nil cell)
| _ => constr:(@nil cell)
end.
Ltac sym_tail_cells cs :=
lazymatch cs with
| _ :: ?r => sym_tail_cells r
| @nil _ => fail
| ?t => t
end.
Ltac catch_upA :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>

repeat match goal with
| H : rw_cells segs ?m0 ?a ?cs |- _ =>
lazymatch m0 with mc => fail | _ => idtac end;
let tl := sym_tail_cells cs in let pre := lit_prefix_cells cs in
let H' := fresh H in
assert (H' : rw_cells segs m0 a pre) by (change cs with (pre ++ tl) in H; exact (proj1 (proj1 (rw_cells_app segs m0 a pre tl) H)));
clear H; rename H' into H
end;

repeat match goal with
| MU : munch ?W ?m0 mc, WM : wmono segs ?m0 mc, H : rw_cells segs ?m0 ?a ?cs |- _ =>
apply (rw_cells_transport segs W m0 mc a cs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| MU : munch ?W ?m0 mc, H : ro_cells segs ?m0 ?a ?cs |- _ =>
apply (ro_cells_transport segs W m0 mc a cs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| MU : munch ?W ?m0 mc, H : bytes_at segs ?m0 ?a ?bs |- _ =>
apply (bytes_at_transport segs W m0 mc a bs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
end
| _ => idtac
end.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section TwKit.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma blk_gran0A : forall A LBx LM FRS B m md a n i, HEAPAx A LBx LM FRS B m md -> In (a, n) LBx -> 0 <= i -> 8 * i + 8 <= n ->
ro_cells asegs m (a / 8 + 2147450880 + i) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx LM FRS B m md a n i HP Hin Hi Hn.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH. unfold shad in SH. cbn [hl_sb hl_segs hla_base A4L A4H] in SH. unfold A_SB in SH.
assert (E : 8 * i / 8 = i) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
pose proof (shadow_at0 asegs m (a / 8 + 2147450880) n (8 * i) ltac:(lia) ltac:(rewrite E; lia) SH) as X. rewrite E in X. exact X.
Qed.

Lemma jopt_frame_onlyA : forall A LB BS LM FRS B m md lo sp s p,
HEAPAx A (BS ++ LB) LM FRS B m md -> alloc_ceiling <= lo -> jopt asegs A4F s m BS p ->
forall N m', lo <= sp - N -> munch [(sp - N, sp)] m m' -> wmono asegs m m' -> jopt asegs A4F s m' BS p.
Proof.
intros A LB BS LM FRS B m md lo sp s p HP LO JO N m' LOS MU WM.
eapply (jopt_agree asegs A4F BS m m' s BS p); [exact JO | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros bb kk Hb. cbn.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bb kk HP ltac:(apply in_or_app; left; apply in_or_app; left; exact Hb)) as (_ & _ & _ & Hh & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *. split; [lia | exact I].
Qed.
End TwKit.
End RC__1.

Definition blk_seen (a n : Z) : Prop := True.
Ltac arm_blkA HIx :=
repeat match goal with
| HPx : HEAPA _ _ _ _ _ _ _ _ _, ER : ?REST = [(?a, ?n)], EBS : ?BSx = ?REST ++ _ |- _ =>
lazymatch goal with _ : blk_seen a n |- _ => fail | _ => idtac end;
let Hin := fresh "Hin" in let Hal := fresh "Hal" in let Hlo := fresh "Hlo" in let Hhi := fresh "Hhi" in
pose proof (heapA_blk _ HIx _ _ _ _ _ _ _ a n HPx
ltac:(apply in_or_app; left; apply in_or_app; left; rewrite EBS, ER; apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _);
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi;
assert (blk_seen a n) by exact I
end.

Ltac site_granA HIx p i :=
lazymatch goal with
| HPx : HEAPA _ _ _ _ _ _ _ ?m0 _ |- _ =>
match goal with
| ER : ?REST = [(p, ?n)], EBS : ?BSx = ?REST ++ _ |- _ =>
let SH := fresh "SHg" in let K := eval vm_compute in (2147450880 + i) in
assert (SH : ro_cells asegs m0 (p / 8 + K) [C1 (Z_to_bv 8 0)]) by
(replace (p / 8 + K) with (p / 8 + 2147450880 + i) by lia;
eapply (blk_gran0A HIx _ _ _ _ _ _ _ p n i HPx); [ rewrite EBS, ER; apply in_or_app; left; apply in_or_app; left; left; reflexivity | lia | lia ])
end
end; catch_upA.

Ltac cells_take cs k :=
lazymatch k with
| O => constr:(@nil cell)
| _ => lazymatch cs with
| ?c :: ?r => let sz := eval cbv in (csize c) in
let ok := eval cbv in (Nat.leb sz k) in
lazymatch ok with true => let k' := eval cbv in (Nat.sub k sz) in let p := cells_take r k' in constr:(c :: p) end
end
end.
Ltac cells_drop cs k :=
lazymatch k with
| O => cs
| _ => lazymatch cs with ?c :: ?r => let sz := eval cbv in (csize c) in let k' := eval cbv in (Nat.sub k sz) in cells_drop r k' end
end.
Ltac zero_cells n :=
lazymatch n with
| O => constr:(@nil cell)
| _ => let n' := eval cbv in (Nat.sub n 8) in let r := zero_cells n' in constr:(C8 (Z_to_bv 64 0) :: r)
end.
Ltac amemset_callA HIx OBL HPx r size k n lo SPA :=
let kn := eval cbv in (Z.to_nat k) in let nn := eval cbv in (Z.to_nat n) in
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs0 |- _ =>
split_for_access BLKc asegs mc r cs0 kn nn;
let cs := lazymatch type of BLKc with rw_cells _ _ _ ?cs => cs end in
let pre := cells_take cs kn in let rest := cells_drop cs kn in let mid := cells_take rest nn in let post := cells_drop rest nn in
let HDRc := fresh "HDRc" in let RESTc := fresh "RESTc" in let DSTc := fresh "DSTc" in let TLc := fresh "TLc" in let HPc := fresh "HPc" in
change cs with (pre ++ (mid ++ post)) in BLKc;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDRc RESTc]; clear BLKc;
cbn [cells_size csize Nat.add] in RESTc; replace (r + Z.of_nat kn) with (r + k) in RESTc by lia;
destruct (proj1 (rw_cells_app asegs mc (r + k) _ _) RESTc) as [DSTc TLc]; clear RESTc;
cbn [cells_size csize Nat.add] in TLc; replace (r + k + Z.of_nat nn) with (r + (k + n)) in TLc by lia;
(let L4 := constr:(A4L) in heap_nowA_auto L4 HIx HPx HPc);
eapply (OBL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r size (r + k) 0 n lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ first [ in_prefix | in_app_prefix ] | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DSTc
| eassumption | lia | lia
| first [ lia | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | (repeat match goal with |- context [bv_unsigned ?sp + - ?c] => replace (bv_unsigned sp + - c) with (bv_unsigned sp - c) by lia end); rewrite Zminus_mod, SPA; reflexivity ]
| lia | eassumption | reflexivity | ];
let mS := fresh "mS" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MIc" in let DZ := fresh "DZ" in let STc := fresh "STc" in
intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? mS MUc WMc MIc DZ STc;
transport_after_call asegs mc mS MUc WMc; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MUc WMc HPc;

let zc := zero_cells nn in
change (Z.to_nat n) with nn in DZ; cbn [repeat] in DZ;
apply (rw_cells_recast asegs mS (r + k) _ zc) in DZ; [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity];
let BLKn := fresh "BLK" in
assert (BLKn : rw_cells asegs mS r (pre ++ (zc ++ post)));
[ apply (proj2 (rw_cells_app asegs mS r _ _)); cbn [cells_size csize Nat.add]; split; [exact HDRc |];
replace (r + Z.of_nat kn) with (r + k) by lia;
apply (proj2 (rw_cells_app asegs mS (r + k) _ _)); cbn [cells_size csize Nat.add]; split; [exact DZ |];
replace (r + k + Z.of_nat nn) with (r + (k + n)) by lia; exact TLc
| cbn [app] in BLKn; clear HDRc DZ TLc;
try lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?pcn)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 pcn)) with (Z_to_bv 64 pcn) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end ]
end
end.

Lemma fsaved_restore_kit : forall (F F' : bvmap 5 word) (k1 k2 k3 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> bv_unsigned k1 = bv_unsigned k3 ->
fsaved (bvmap_set k1 v F) F' -> fsaved F (bvmap_set k2 (Sem.reg_get F k3) F').
Proof.
intros F F' k1 k2 k3 v E12 E13 FS j Hj.
replace k2 with k1 by (apply bv_eq; exact E12). replace k3 with k1 by (apply bv_eq; exact E13).
destruct (Z.eq_dec (bv_unsigned k1) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other by (intros E; apply NE; rewrite E; reflexivity).
rewrite (FS j Hj). apply QEpW.reg_get_set_other. intros E; apply NE; rewrite E; reflexivity.
Qed.
Ltac tw_fsaved :=
first [ apply fsaved_refl | apply fsaved_set_self'; reflexivity | eassumption
| eapply fsaved_restore_kit; [reflexivity | reflexivity | first [ apply fsaved_refl | apply fsaved_set_self'; reflexivity | eassumption ] ]
| eapply fsaved_trans; [ eassumption | tw_fsaved ] ].
Ltac tw_ret :=
first [ apply ret_statew_same
| apply ret_statew_intro; [ tw_fsaved | let Hf := fresh "Hf" in intros Hf; first [ exact Hf | solve [eauto 6] ] ] ].
Ltac tw_vm := first [ apply model_vm_only_refl | eassumption | solve [eauto 8 using model_vm_only_trans, model_vm_only_refl] ].
Ltac tw_stk FR sp :=
lazymatch goal with STx : stk asegs ?mf _ _ |- stk asegs ?mf _ _ => first [ exact STx | release_frame FR STx (bv_unsigned sp); exact STx ] end.

Ltac tw_hpres HIx :=
first [ eassumption
| lazymatch goal with |- heap_pres _ ?LST ?SP ?m0 ?mf =>
match goal with
| HPRx : heap_pres _ LST SP m0 ?mk, HPk : HEAPA _ _ _ _ _ _ _ ?mk _, MUx : munch _ ?mk mf, WMx : wmono _ ?mk mf |- _ =>
eapply heap_pres_trans; [ exact HPRx |];
eapply (heap_pres_of_munch A4H LST SP); [ exact MUx | exact WMx |];
eapply (client_outsideA A4L HIx); [ exact HPk | (let bb := fresh "bb" in let Hbb := fresh "Hbb" in intros bb Hbb; first [ exact Hbb | in_tailA Hbb ]) | clia
| first [ solve [let L4 := constr:(A4L) in solve_clientWA L4 HIx HPk]
| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
first [ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ] ] ]
end end ].
Ltac tw_errno := first [ eassumption | unfold A_ERRNO, A_TP; first [ eassumption | match goal with H : rw_cells asegs ?mf ?a _ |- rw_cells asegs ?mf _ _ => exact H end ] ].

Create HintDb twcost.
Ltac tw_budget :=
repeat autounfold with twcost in *; cbn [bB bD charge uw_cost length Z.of_nat Z.mul Z.eqb] in *;
first [ lia | repeat match goal with u : uwd |- _ => destruct u; cbn [uw_cost] in * end; lia ].

Ltac tw_heapA_with HIx HPp MUx WMx mf :=
eapply (heapA_client_frame A4L HIx);
[ exact HPp
| eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPp MUx);
first [ solve [solve_frameW_withA HPp]
| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; first [ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ] ]
| exact WMx | match goal with H : mem_inv asegs mf |- _ => exact H end ].
Ltac tw_heapA HIx :=
lazymatch goal with |- HEAPA _ _ _ _ _ _ _ ?mf _ =>
match goal with
| HPk : HEAPA _ _ _ _ _ _ _ ?mk _, MUx : munch _ ?mk mf, WMx : wmono _ ?mk mf |- _ =>
first [ tw_heapA_with HIx HPk MUx WMx mf
| let HPp := fresh "HPp" in
pose proof (heapA_perm A4L HIx _ _ _ _ _ _ _ _ _ _ HPk (Permutation.perm_swap _ _ _) (Permutation.Permutation_refl _) (Permutation.Permutation_refl _)) as HPp;
tw_heapA_with HIx HPp MUx WMx mf ]
end end.

Ltac cells_exactA H :=
first [ exact H
| eapply rw_cells_recast; [ exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ] ].
End Mqh.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Local Ltac flia := Qo9G.term_slim ltac:(Zify.zify; xlia zchecker).

Definition pbtail (P : list blk) : Prop := P = [] \/ exists a L, P = (a, 16) :: L.
Lemma pbtail_nil : pbtail []. Proof. left; reflexivity. Qed.
Lemma pbtail_app : forall P Q, pbtail P -> pbtail Q -> pbtail (P ++ Q).
Proof. intros P Q [->|(a & L & ->)] HQ; [exact HQ | right; exists a, (L ++ Q); reflexivity]. Qed.
Lemma jtx_pbtail_nil : forall s P L w R, pbtail P -> jtx s (P ++ L) = Some (w, R) -> P = [].
Proof. intros s P L w R [->|(a & L' & ->)] H; [reflexivity|]. cbn [app] in H. rewrite jtx_pb_none in H. discriminate. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation jvalx := (jval segs fn).

Lemma opt_pbuf_pbtail : forall m PBS pb, opt_pbuf segs m PBS pb -> pbtail PBS.
Proof.
intros m PBS pb [[_ ->]|[_ (buf & bpos & size & content & -> & _)]]; [left; reflexivity | right; eexists _, _; reflexivity].
Qed.

Definition kids_okv (m : word -> option byte) :=
fix kids_ok (ks : list (option jshape)) (vs : list (Z * Z)) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', (_, v) :: vs', bs :: bss' =>
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end /\ kids_ok ks' vs' bss'
| _, _, _ => False
end.
Definition kids_okp (m : word -> option byte) :=
fix kids_ok (ks : list (option jshape)) (vs : list Z) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', v :: vs', bs :: bss' =>
match k with None => v = 0 /\ bs = [] | Some s' => v <> 0 /\ jvalx s' m bs v 1 end /\ kids_ok ks' vs' bss'
| _, _, _ => False
end.

Lemma jtxk_arr_tail : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> forall X w R, jtx s (bs ++ X) = Some (w, R) -> exists P, R = P ++ X /\ pbtail P) ->
forall ps KBS, kids_okp m kids ps KBS -> forall P0 Y acc w R, pbtail P0 ->
jtxk_arr kids (P0 ++ concat KBS ++ Y) acc = Some (w, R) -> exists P, R = P ++ Y /\ pbtail P.
Proof.
induction kids as [|[s'|] kids IH]; intros HK ps KBS OK P0 Y acc w R HP0 H.
- destruct ps; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_arr concat app] in H. injection H as _ <-. exists P0. split; [reflexivity | exact HP0].
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [jtxk_arr concat] in H. destruct (jtx s' (P0 ++ (bs1 ++ concat KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP0 E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (HK s' (or_introl eq_refl) _ _ _ JV _ _ _ E) as (P1 & -> & HP1).
eapply (IH (fun s Hs => HK s (or_intror Hs)) ps KBS OK P1 Y); [exact HP1 | exact H].
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_arr concat app] in H. eapply (IH (fun s Hs => HK s (or_intror Hs)) ps KBS OK P0 Y); [exact HP0 | exact H].
Qed.
Lemma jtxk_obj_tail : forall m kids, (forall s, In (Some s) kids -> forall bs p rc, jvalx s m bs p rc -> forall X w R, jtx s (bs ++ X) = Some (w, R) -> exists P, R = P ++ X /\ pbtail P) ->
forall kvs KBS, kids_okv m kids kvs KBS -> forall keys P0 Y acc w R, pbtail P0 ->
jtxk_obj kids keys (P0 ++ concat KBS ++ Y) acc = Some (w, R) -> exists P, R = P ++ Y /\ pbtail P.
Proof.
induction kids as [|[s'|] kids IH]; intros HK kvs KBS OK keys P0 Y acc w R HP0 H.
- destruct kvs; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_obj concat app] in H. injection H as _ <-. exists P0. split; [reflexivity | exact HP0].
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [jtxk_obj concat] in H. destruct keys as [|[k kn] keys]; [discriminate|].
destruct (jtx s' (P0 ++ (bs1 ++ concat KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP0 E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (HK s' (or_introl eq_refl) _ _ _ JV _ _ _ E) as (P1 & -> & HP1).
eapply (IH (fun s Hs => HK s (or_intror Hs)) kvs KBS OK keys P1 Y); [exact HP1 | exact H].
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_obj concat app] in H. destruct keys as [|[k kn] keys]; [discriminate|].
eapply (IH (fun s Hs => HK s (or_intror Hs)) kvs KBS OK keys P0 Y); [exact HP0 | exact H].
Qed.

Theorem jtx_val_tail : forall s m bs p rc, jvalx s m bs p rc -> forall X w R, jtx s (bs ++ X) = Some (w, R) -> exists P, R = P ++ X /\ pbtail P.
Proof.
induction s as [|u| |h|kids IHk|kids IHk] using jshape_ind2; intros m bs p rc JV X w R H.
- destruct JV as (pb & PBS & REST & -> & OP & b & junk & -> & _). cbn in H. injection H as _ <-. exists PBS. split; [reflexivity | eapply opt_pbuf_pbtail; exact OP].
- destruct u.
+ destruct JV as (pb & PBS & REST & -> & OP & bits & ud & udn & uds & -> & _). cbn in H. injection H as _ <-. exists PBS. split; [reflexivity | eapply opt_pbuf_pbtail; exact OP].
+ destruct JV as (pb & PBS & REST & -> & OP & bits & -> & _). cbn in H. injection H as _ <-. exists PBS. split; [reflexivity | eapply opt_pbuf_pbtail; exact OP].
- destruct JV as (pb & PBS & REST & -> & OP & cty & v & junk & -> & _). cbn in H. injection H as _ <-. exists PBS. split; [reflexivity | eapply opt_pbuf_pbtail; exact OP].
- destruct h.
+ destruct JV as (pb & PBS & REST & -> & OP & len & pd & pdn & str & junk2 & -> & _). cbn in H. injection H as _ <-. exists PBS. split; [reflexivity | eapply opt_pbuf_pbtail; exact OP].
+ destruct JV as (pb & PBS & REST & -> & OP & len & str & junk & -> & Hl & _). cbn [app jtx] in H. unfold str_objsize in H.
replace (57 <=? 49 + Z.max len 8) with true in H by (symmetry; apply Z.leb_le; lia). injection H as _ <-. exists PBS. split; [reflexivity | eapply opt_pbuf_pbtail; exact OP].
- destruct JV as (pb & PBS & REST & -> & OP & t & TBS & kvs & KBS & -> & _ & (tbl & size & es & svs & Ekvs & -> & _) & L1 & L2 & OK).
unfold lh_blocks in H. cbn [app] in H. rewrite <- !app_assoc in H. rewrite jtx_obj_eq in H. cbn [snd] in H.
assert (LKe : length es = length kids) by (rewrite Ekvs, length_map in L1; exact L1).
assert (LK : length (map (fun e => (le_k e, le_kn e) : blk) es) = length kids) by (rewrite length_map; exact LKe).
change (48 =? 48) with true in H. change (56 =? 56) with true in H. cbn [andb] in H.
match type of H with context [(?x <=? ?y)%nat] => destruct (Nat.leb_spec x y) as [_|GT]; [| exfalso; rewrite !length_app, length_map in GT; clear - GT LKe; flia] end.
rewrite (firstn_app_exact _ _ _ LK), (skipn_app_exact _ _ _ LK) in H.
destruct (jtxk_obj_tail m kids (fun s Hs => IHk s Hs m) kvs KBS OK _ [] (PBS ++ X) _ w R pbtail_nil H) as (P & -> & HP).
exists (P ++ PBS). split; [rewrite app_assoc; reflexivity | apply pbtail_app; [exact HP | eapply opt_pbuf_pbtail; exact OP]].
- destruct JV as (pb & PBS & REST & -> & OP & a & ABS & ps & KBS & -> & _ & (arr & size & junk & -> & _) & L1 & L2 & OK).
cbn [app] in H. rewrite <- !app_assoc in H. rewrite jtx_arr_eq in H. cbn [snd] in H.
change (48 =? 48) with true in H. change (32 =? 32) with true in H. cbn [andb] in H.
destruct (jtxk_arr_tail m kids (fun s Hs => IHk s Hs m) ps KBS OK [] (PBS ++ X) _ w R pbtail_nil H) as (P & -> & HP).
exists (P ++ PBS). split; [rewrite app_assoc; reflexivity | apply pbtail_app; [exact HP | eapply opt_pbuf_pbtail; exact OP]].
Qed.
End WithSegs.
