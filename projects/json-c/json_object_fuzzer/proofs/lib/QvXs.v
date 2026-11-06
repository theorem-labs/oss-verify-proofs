(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4Eu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc8V.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition json_parse_int64_entry : Z := 0x27268.
Definition json_parse_uint64_entry : Z := 0x272e8.

Definition parse_i64_W (SP R : Z) : list ivl :=
[(SP - 416, SP); (R, R + 8); (0x75e70 - 164, 0x75e70 - 160)].

Definition parse_i64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP A R lo : Z) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (rv : Z) (v e' : word),
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch (parse_i64_W SP R) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ (rv = 0 \/ rv = 1)
/\ rw_cells rsegs m' R [C8 v]
/\ bytes_at rsegs m' A (str ++ [b0])
/\ rw_cells rsegs m' (0x75e70 - 164) [C4 e']
/\ stk rsegs m' lo SP.

Definition parse_i64_stmt (entry : Z) : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str : list byte) (SP A R lo : Z) (e g rj : word),
bv_unsigned sp = SP -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 R ->
bytes_at rsegs m A (str ++ [b0]) -> ~ In b0 str -> 0 <= A -> A + Z.of_nat (length str) + 1 <= SP - 416 ->
rw_cells rsegs m R [C8 rj] -> SP <= R -> R + 8 <= 2^63 ->
rw_cells rsegs m (0x75e70 - 164) [C4 e] -> tp = Z_to_bv 64 0x75e70 ->
bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
stk rsegs m lo SP -> 0x97000 <= lo -> lo <= SP - 416 ->
(A + Z.of_nat (length str) + 1 <= 0x75e70 - 164 \/ 0x75e70 - 160 <= A) ->
bv_unsigned ra mod 2 = 0 ->
mem_inv rsegs m ->
evt rsegs (parse_i64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP A R lo str m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Lemma zbv_shift64 : forall z, Z_to_bv 64 (z + 18446744073709551616) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
change (2^64) with 18446744073709551616.
rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma string_byte : forall m sb payload co c,
bytes_at rsegs m sb payload -> nth_error payload (Z.to_nat co) = Some c -> 0 <= co ->
ov_read_bytes rsegs m (Z_to_bv 64 (sb + co)) 1 = Some [c].
Proof.
intros m sb payload co c B Hn Hco.
assert (L : (Z.to_nat co < length payload)%nat) by (apply (proj1 (nth_error_Some payload (Z.to_nat co))); congruence).
pose proof (bytes_at_read rsegs m sb payload co 1 B Hco ltac:(lia)) as R.
replace (firstn 1 (skipn (Z.to_nat co) payload)) with [c] in R; [exact R|].
pose proof (@nth_error_split _ payload (Z.to_nat co) c Hn) as (l1 & l2 & E & Hl1). rewrite E at 1.
rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Section ParseInt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.

#[using="STRTOLL"] Lemma json_parse_int64_spec : parse_i64_stmt json_parse_int64_entry.
Proof.
unfold parse_i64_stmt, json_parse_int64_entry.
intros until rj. intros HSP A0 A1 STR NONUL HA0 AHI RV HR0 RHI ERR TP GOTF GF ST LO LOS ASEP RA MI.
subst a0 a1 tp.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
word_range sp SPR. rewrite HSP in SPR.
pose proof (munch_refl (parse_i64_W SP R) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold parse_i64_W in MU. unfold GOT_GUARD, GUARD in *.
symmetry in HSP. subst SP. change (0x75e70 - 164) with 482764 in *. change (0x75e70 - 160) with 482768 in *.
carve_frame 48%nat ST.
destruct (rw_cells_CB_sizes rsegs m [8;8;8;8;8;8]%nat _ _ _ FR eq_refl) as (q0 & q1 & q2 & q3 & q4 & q5 & FR'). clear FR. rename FR' into FR.

step. step. step. step. step. step. step. stepz.

step. step. step. step. step. stepz.
step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
apply (proj1 (rw_cells_app rsegs _ _ [CB 8 q0] _)) in FR as [FR0 FR];
apply (proj1 (rw_cells_app rsegs _ _ [C8 (Z_to_bv 64 0)] _)) in FR as [FE FR];
cbn [cells_size csize Nat.add] in FE, FR;
replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FE by lia;
replace (bv_unsigned sp + -48 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -32) in FR by lia
end.
pose proof STRTOLL as SU. unfold strtox_stmt in SU.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply SU with (SP := bv_unsigned sp + -48) (A := A) (E := bv_unsigned sp + -40) (lo := lo) (str := str)
| unfold strtox_post, strtox_W; post_call segs mm ] end.
all: clear SU.
1:{ apply unsigned_lit; lia. } 1:{ apply unsigned_lit; lia. } 1:{ apply unsigned_lit; lia. } 1:{ reflexivity. }
1:{ exact STR. } 1:{ exact NONUL. } 1:{ lia. } 1:{ exact FE. } 1:{ exact ERR. } 1:{ reflexivity. }
1:{ exact GOTF. } 1:{ exact GF. } 1:{ exact ST. }
1-7: lia.
1:{ exact MI. }
cbv beta. change (0x75e70 - 164) with 482764 in *. change (0x75e70 - 160) with 482768 in *.

assert (EPI : forall mc (rv : Z) (jv v1 e1 : word) y5 y6 y7 a1' a2' a3' a4' a5' a6' a7' y28 y29 y30 y31,
rw_cells rsegs mc (bv_unsigned sp + -48) [CB 8 q0] ->
rw_cells rsegs mc (bv_unsigned sp + -40) [C8 jv] ->
rw_cells rsegs mc (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs mc R [C8 v1] -> bytes_at rsegs mc A (str ++ [b0]) -> rw_cells rsegs mc 482764 [C4 e1] ->
stk rsegs mc lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 416, bv_unsigned sp); (R, R + 8); (482764, 482768)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(rv = 0 \/ rv = 1) ->
evt rsegs (parse_i64_post ra sp gp (Z_to_bv 64 482928) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp) A R lo str m)
(MS (mkR (Z_to_bv 64 0x272a4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 482928) y5 y6 y7
(Z_to_bv 64 482764) (Z_to_bv 64 R) (Z_to_bv 64 rv) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 A) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 0x272d0) fc None mc (seg_rom rsegs))).
{ intros mc rv jv v1 e1 y5 y6 y7 a1' a2' a3' a4' a5' a6' a7' y28 y29 y30 y31 FR0' FE' FR' RV' STR' ERR' ST' MU' WM' MI' Hrv.
step. step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (FRX : rw_cells rsegs mx (bv_unsigned sp + -48) ([CB 8 q0] ++ [C8 jv] ++ [C8 s2; C8 s1; C8 s0; C8 ra]))
by (apply (proj2 (rw_cells_app rsegs mx _ _ _)); split; [exact FR0'|]; cbn [cells_size csize Nat.add];
replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) by lia;
apply (proj2 (rw_cells_app rsegs mx _ _ _)); split; [exact FE'|]; cbn [cells_size csize Nat.add];
replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia; exact FR')
end.
clear FR0' FE' FR'. cbn [app] in FRX.
release_frame FRX ST' (bv_unsigned sp).
step.
finish. all: first [exact Hrv | exact RV' | exact STR' | exact ERR' | exact ST' | exact MU' | idtac]. }
step.
match goal with Hj : 0 <= ?j <= Z.of_nat (length str), HE : rw_cells rsegs _ (bv_unsigned sp + -40) [C8 (Z_to_bv 64 (A + ?j))] |- _ =>
rename Hj into HJ; rename HE into FE2 end.
lazymatch type of FE2 with rw_cells _ _ _ [C8 (Z_to_bv 64 (A + ?j))] =>
step; destruct (Z.eq_dec j 0) as [J0 | Jn];
[
rewrite J0 in *; rewrite Z.add_0_r in *; if_true; step; stepz; step;
eapply EPI; try eassumption; right; reflexivity
| if_falsex ] end.

step.
step. if_cases Hv.
-
step. step. if_cases He.
+
zify_cond He.
match goal with |- context [sx32 ?ev] =>
replace (sx32 ev) with (Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia) end.
eapply EPI; try eassumption; left; reflexivity.
+ step. stepz. step. eapply EPI; try eassumption; right; reflexivity.
- step. step. eapply EPI; try eassumption; left; reflexivity.
Qed.

#[using="STRTOULL"] Lemma json_parse_uint64_spec : parse_i64_stmt json_parse_uint64_entry.
Proof.
unfold parse_i64_stmt, json_parse_uint64_entry.
intros until rj. intros HSP A0 A1 STR NONUL HA0 AHI RV HR0 RHI ERR TP GOTF GF ST LO LOS ASEP RA MI.
subst a0 a1 tp.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
word_range sp SPR. rewrite HSP in SPR.
pose proof (munch_refl (parse_i64_W SP R) m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold parse_i64_W in MU. unfold GOT_GUARD, GUARD in *.
symmetry in HSP. subst SP. change (0x75e70 - 164) with 482764 in *. change (0x75e70 - 160) with 482768 in *.
carve_frame 48%nat ST.
destruct (rw_cells_CB_sizes rsegs m [8;8;8;8;8;8]%nat _ _ _ FR eq_refl) as (q0 & q1 & q2 & q3 & q4 & q5 & FR'). clear FR. rename FR' into FR.

step. step. step. step. step. step. step. stepz.

step. step. step. step. step. stepz.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
apply (proj1 (rw_cells_app rsegs _ _ [CB 8 q0] _)) in FR as [FR0 FR];
apply (proj1 (rw_cells_app rsegs _ _ [C8 (Z_to_bv 64 0)] _)) in FR as [FE FR];
cbn [cells_size csize Nat.add] in FE, FR;
replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) in FE by lia;
replace (bv_unsigned sp + -48 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -32) in FR by lia
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (EPI : forall mc (rv k : Z) (jv v1 e1 : word) y1 y5 y6 y7 a0' a1' a2' a3' a4' a5' a6' a7' y28 y29 y30 y31,
rw_cells rsegs mc (bv_unsigned sp + -48) [CB 8 q0] ->
rw_cells rsegs mc (bv_unsigned sp + -40) [C8 jv] ->
rw_cells rsegs mc (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells rsegs mc R [C8 v1] -> bytes_at rsegs mc A (str ++ [b0]) -> rw_cells rsegs mc 482764 [C4 e1] ->
stk rsegs mc lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 416, bv_unsigned sp); (R, R + 8); (482764, 482768)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
(rv = 0 \/ rv = 1) -> a0' = Z_to_bv 64 rv ->
evt rsegs (parse_i64_post ra sp gp (Z_to_bv 64 482928) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp) A R lo str m)
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 482928) y5 y6 y7
(Z_to_bv 64 482764) (Z_to_bv 64 R) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (A + k)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
F (Z_to_bv 64 0x27378) fc None mc (seg_rom rsegs)))
end.
{ intros mc rv k jv v1 e1 y1 y5 y6 y7 a0' a1' a2' a3' a4' a5' a6' a7' y28 y29 y30 y31 FR0' FE' FR' RV' STR' ERR' ST' MU' WM' MI' Hrv ->.
step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (FRX : rw_cells rsegs mx (bv_unsigned sp + -48) ([CB 8 q0] ++ [C8 jv] ++ [C8 s2; C8 s1; C8 s0; C8 ra]))
by (apply (proj2 (rw_cells_app rsegs mx _ _ _)); split; [exact FR0'|]; cbn [cells_size csize Nat.add];
replace (bv_unsigned sp + -48 + Z.of_nat 8) with (bv_unsigned sp + -40) by lia;
apply (proj2 (rw_cells_app rsegs mx _ _ _)); split; [exact FE'|]; cbn [cells_size csize Nat.add];
replace (bv_unsigned sp + -40 + Z.of_nat 8) with (bv_unsigned sp + -32) by lia; exact FR')
end.
clear FR0' FE' FR'. cbn [app] in FRX.
release_frame FRX ST' (bv_unsigned sp).
step.
finish. all: first [exact Hrv | exact RV' | exact STR' | exact ERR' | exact ST' | exact MU' | idtac]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (POSTLOOP : forall (k : Z) (c : byte) (a3v : word),
0 <= k <= Z.of_nat (length str) -> nth_error (str ++ [b0]) (Z.to_nat k) = Some c ->
evt rsegs (parse_i64_post ra sp gp (Z_to_bv 64 482928) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp) A R lo str m)
(MS (mkR (Z_to_bv 64 0x2730c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 482928) t0 t1 t2
(Z_to_bv 64 482764) (Z_to_bv 64 R) (Z_to_bv 64 5) (Z_to_bv 64 32) (zxb c) a3v a4 a5 a6 a7 (Z_to_bv 64 (A + k)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x27334) fc None m1 (seg_rom rsegs)))
end.
{ intros k c a3v Hk Hc.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
unfold zxb. step. step.
destruct (Z.eq_dec (bv_unsigned c) 45) as [Cm | Cn].
-
if_truex. step. eapply EPI; try eassumption; [right; reflexivity | reflexivity].
- if_falsex. step. step. step. step.

assert (STRk : bytes_at rsegs m1 (A + k) (skipn (Z.to_nat k) str ++ [b0])).
{ pose proof STR as X. rewrite <- (firstn_skipn (Z.to_nat k) str) in X. rewrite <- app_assoc in X.
apply (proj1 (bytes_at_app rsegs _ _ _ _)) in X as [_ X]. rewrite length_firstn in X.
replace (A + Z.of_nat (Nat.min (Z.to_nat k) (length str))) with (A + k) in X by lia. exact X. }
assert (NONULk : ~ In b0 (skipn (Z.to_nat k) str)).
{ intros Hin. apply NONUL. rewrite <- (firstn_skipn (Z.to_nat k) str). apply in_or_app. right. exact Hin. }
assert (Lk : Z.of_nat (length (skipn (Z.to_nat k) str)) = Z.of_nat (length str) - k) by (rewrite length_skipn; lia).
pose proof STRTOULL as SU. unfold strtox_stmt in SU.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply SU with (SP := bv_unsigned sp + -48) (A := A + k) (E := bv_unsigned sp + -40) (lo := lo) (str := skipn (Z.to_nat k) str)
| unfold strtox_post, strtox_W; post_call segs mm ] end.
all: clear SU.
1:{ apply unsigned_lit; lia. } 1:{ apply unsigned_lit; lia. } 1:{ apply unsigned_lit; lia. } 1:{ reflexivity. }
1:{ exact STRk. } 1:{ exact NONULk. } 1:{ lia. } 1:{ exact FE. } 1:{ eassumption. } 1:{ reflexivity. }
1:{ exact GOTF. } 1:{ exact GF. } 1:{ eassumption. }
1-7: lia.
1:{ assumption. }
cbv beta. change (0x75e70 - 164) with 482764 in *. change (0x75e70 - 160) with 482768 in *.
step.
match goal with Hj : 0 <= ?j <= Z.of_nat (length (skipn _ str)) |- _ => rename Hj into HJ end.
lazymatch type of HJ with 0 <= ?j <= _ =>
step; destruct (Z.eq_dec j 0) as [J0 | Jn];
[ rewrite J0 in *; rewrite Z.add_0_r in *; if_true; step; stepz; step;
eapply EPI; try eassumption; [right; reflexivity | reflexivity]
| if_falsex ] end.
step.
step. if_cases Hv.
+ step. step. if_cases He.
* zify_cond He.
match goal with |- context [sx32 ?ev] =>
replace (sx32 ev) with (Z_to_bv 64 0) by (apply bv_eq; change (bv_unsigned (Z_to_bv 64 0)) with 0; lia) end.
eapply EPI; try eassumption; [left; reflexivity | reflexivity].
* step. stepz. step. eapply EPI; try eassumption; [right; reflexivity | reflexivity].
+ step. step. eapply EPI; try eassumption; [left; reflexivity | reflexivity]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
assert (LOOP : forall (n : nat) (k : Z) (a2v a3v : word),
(length str - Z.to_nat k <= n)%nat -> 0 <= k <= Z.of_nat (length str) ->
evt rsegs (parse_i64_post ra sp gp (Z_to_bv 64 482928) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned sp) A R lo str m)
(MS (mkR (Z_to_bv 64 0x2730c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 482928) t0 t1 t2
(Z_to_bv 64 482764) (Z_to_bv 64 R) (Z_to_bv 64 5) (Z_to_bv 64 32) a2v a3v a4 a5 a6 a7 (Z_to_bv 64 (A + k)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x27324) fc None m1 (seg_rom rsegs)))
end.
{ induction n as [|n IH]; intros k a2v a3v Hn Hk.
all: destruct (nth_error (str ++ [b0]) (Z.to_nat k)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; rewrite length_app in Hc; cbn in Hc; lia].
all: pose proof (string_byte m1 A _ k c STR Hc ltac:(lia)) as RDk.
all: pose proof (bv_unsigned_in_range 8 c) as CR; unfold bv_modulus in CR; cbn in CR.
-
assert (k = Z.of_nat (length str)) by lia.
rewrite nth_error_app2 in Hc by lia. replace (Z.to_nat k - length str)%nat with 0%nat in Hc by lia. cbn in Hc. injection Hc as <-.
step. step. change (bv_unsigned (zxb b0)) with 0. step.
replace (Z_to_bv 64 (0 + -9)) with (Z_to_bv 64 (2^64 - 9)) by (apply bv_eq; vm_compute; reflexivity).
if_false. step. if_false.
apply (POSTLOOP k b0); [lia|]. rewrite nth_error_app2 by lia. replace (Z.to_nat k - length str)%nat with 0%nat by lia. reflexivity.
- step. step. unfold zxb at 1. rewrite (unsigned_lit (bv_unsigned c)) by lia. step.
destruct (Z.lt_ge_cases (bv_unsigned c) 9) as [Clt | Cge].
+ rewrite <- (zbv_shift64 (bv_unsigned c + -9)).
if_falsex. step. unfold zxb. if_falsex.
apply (POSTLOOP k c); [lia | exact Hc].
+ destruct (Z.le_gt_cases (bv_unsigned c) 13) as [Cws | Cbig].
*
if_truex. step.
assert (Kl : k < Z.of_nat (length str)).
{ destruct (Z.eq_dec k (Z.of_nat (length str))) as [E|]; [|lia]. exfalso.
rewrite E, nth_error_app2 in Hc by lia. rewrite Nat2Z.id, Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-. change (bv_unsigned b0) with 0 in Cge. lia. }
replace (A + k + 1) with (A + (k + 1)) by lia. apply IH; lia.
* if_falsex. step. unfold zxb.
destruct (Z.eq_dec (bv_unsigned c) 32) as [Csp | Cnsp].
-- if_truex. step.
assert (Kl : k < Z.of_nat (length str)).
{ destruct (Z.eq_dec k (Z.of_nat (length str))) as [E|]; [|lia]. exfalso.
rewrite E, nth_error_app2 in Hc by lia. rewrite Nat2Z.id, Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-. change (bv_unsigned b0) with 0 in Csp. lia. }
replace (A + k + 1) with (A + (k + 1)) by lia. apply IH; lia.
-- if_falsex. fold (zxb c). apply (POSTLOOP k c); [lia | exact Hc]. }
replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + 0)) by (rewrite Z.add_0_r; reflexivity).
apply (LOOP (length str) 0); lia.
Qed.
End ParseInt.
