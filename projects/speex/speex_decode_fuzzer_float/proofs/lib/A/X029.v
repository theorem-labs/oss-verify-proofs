(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X03z X04v X00b.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X0ux X0vt X0ra.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ux OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0vt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Definition memcmp_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(b1 b2 : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (v a1' a2' a3' a4' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch [] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ m' = m /\ (bv_unsigned v = 0 <-> b1 = b2).

Lemma memcmp_loop : forall (b1 b2 : list byte) (P1 P2 c : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
length b1 = length b2 -> b1 <> [] -> c = Z.of_nat (length b1) -> 0 <= P1 -> 0 <= P2 -> P1 + c <= 2^63 -> P2 + c <= 2^63 ->
bytes_at bsegs m P1 b1 -> bytes_at bsegs m P2 b2 -> mem_inv bsegs m ->
evt bsegs (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc b1 b2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P1) (Z_to_bv 64 P2) (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xf16c8) fc None m (seg_rom bsegs)).
Proof.
induction b1 as [|x r1 IH]; intros b2 P1 P2 c ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
LEN NE -> H1 H2 B1 B2 BY1 BY2 MI; [contradiction|].
destruct b2 as [|y r2]; [discriminate LEN|]. injection LEN as LEN.
change (x :: r1) with ([x] ++ r1) in BY1. change (y :: r2) with ([y] ++ r2) in BY2.
apply (proj1 (bytes_at_app bsegs m P1 [x] r1)) in BY1. destruct BY1 as [BX BR1].
apply (proj1 (bytes_at_app bsegs m P2 [y] r2)) in BY2. destruct BY2 as [BY BR2].
cbn [length] in BR1, BR2, B1, B2 |- *. change (Z.of_nat 1) with 1 in BR1, BR2.
pose proof (ro_C1_of_bytes m P1 x BX) as CX. pose proof (ro_C1_of_bytes m P2 y BY) as CY.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EU1 : bv_unsigned (Z_to_bv 64 P1) = P1) by (apply unsigned_lit; lia).
assert (EU2 : bv_unsigned (Z_to_bv 64 P2) = P2) by (apply unsigned_lit; lia).
pose proof (bv_unsigned_in_range 8 x) as RX. pose proof (bv_unsigned_in_range 8 y) as RY. unfold bv_modulus in RX, RY.
change (2 ^ Z.of_N 8) with 256 in RX, RY.
assert (EUX : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia).
assert (EUY : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia).
lstep. lstep. lstep.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned y)) as [EXY|NXY].
-
assert (x = y) by (apply bv_eq; exact EXY). subst y.
replace (bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 (bv_unsigned x))) with true by (symmetry; unfold bv_eqb; apply Z.eqb_refl).
cbn [negb]. cbv iota.
remember (Z.of_nat (Datatypes.S (length r1))) as c eqn:Ec.
assert (EUC : bv_unsigned (Z_to_bv 64 (c + -1)) = c - 1) by (rewrite unsigned_lit by lia; lia).
lstep. lstep. lstep. lstep.
if_cases K; zify_cond K.
+
destruct r1 as [|x1 r1']; [cbn [length] in Ec; lia|].
eapply evt_mono.
{ eapply (IH r2 (P1 + 1) (P2 + 1) (c + -1)); [exact LEN | discriminate | cbn [length] in *; lia | lia | lia | lia | lia | exact BR1 | exact BR2 | exact MI]. }
intros ms' (v & a1' & a2' & a3' & a4' & m' & -> & MU' & WM' & MI' & EM & IFF).
do 6 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact EM|].
rewrite IFF. split; [intros ->; reflexivity | intros E; injection E as E; exact E].
+
destruct r1 as [|x1 r1']; [| cbn [length] in Ec; lia]. destruct r2; [| discriminate LEN].
lstep. lstep.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [reflexivity|].
split; [reflexivity | intros _; reflexivity].
-
replace (bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 (bv_unsigned y))) with false.
2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite EUX, EUY. exact NXY. }
cbn [negb]. cbv iota.
lstep. lstep.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [reflexivity|].
split.
+ intros V. exfalso. rewrite Z_to_bv_unsigned in V. unfold bv_wrap, bv_modulus in V. change (2 ^ Z.of_N 64) with (2^64) in V.
rewrite ?EUX, ?EUY in V. Z.div_mod_to_equations. lia.
+ intros E. injection E as E _. subst y. contradiction.
Qed.

Lemma memcmp_spec : forall (p1 p2 : Z) (b1 b2 : list byte)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) -> length b1 = length b2 ->
0 <= p1 -> 0 <= p2 -> p1 + Z.of_nat (length b1) <= 2^63 -> p2 + Z.of_nat (length b1) <= 2^63 ->
bytes_at bsegs m p1 b1 -> bytes_at bsegs m p2 b2 -> mem_inv bsegs m ->
evt bsegs (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc b1 b2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xf16c4) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> -> -> LEN H1 H2 B1 B2 BY1 BY2 MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (EUN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length b1))) = Z.of_nat (length b1)) by (apply unsigned_lit; lia).
lstep. if_cases K; zify_cond K.
- destruct b1; [| cbn [length] in K; lia]. destruct b2; [| discriminate LEN].
lstep. lstep.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [reflexivity|].
split; [reflexivity | intros _; reflexivity].
- apply (memcmp_loop b1 b2 p1 p2 (Z.of_nat (length b1))); try assumption; try reflexivity.
intros ->. cbn [length] in K. lia.
Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

Definition memcmp_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(b1 b2 : list byte) (m : mem) : machine_state -> Prop :=
fun ms' => exists (v a1' a2' a3' a4' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ m' = m /\ (bv_unsigned v = 0 <-> b1 = b2).

Lemma memcmp_loop : forall (b1 b2 : list byte) (P1 P2 c : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
length b1 = length b2 -> b1 <> [] -> c = Z.of_nat (length b1) -> 0 <= P1 -> 0 <= P2 -> P1 + c <= 2^63 -> P2 + c <= 2^63 ->
bytes_at asegs m P1 b1 -> bytes_at asegs m P2 b2 -> mem_inv asegs m ->
evt asegs (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc b1 b2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P1) (Z_to_bv 64 P2) (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe8e54) fc None m (seg_rom asegs)).
Proof.
induction b1 as [|x r1 IH]; intros b2 P1 P2 c ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
LEN NE -> H1 H2 B1 B2 BY1 BY2 MI; [contradiction|].
destruct b2 as [|y r2]; [discriminate LEN|]. injection LEN as LEN.
change (x :: r1) with ([x] ++ r1) in BY1. change (y :: r2) with ([y] ++ r2) in BY2.
apply (proj1 (bytes_at_app asegs m P1 [x] r1)) in BY1. destruct BY1 as [BX BR1].
apply (proj1 (bytes_at_app asegs m P2 [y] r2)) in BY2. destruct BY2 as [BY BR2].
cbn [length] in BR1, BR2, B1, B2 |- *. change (Z.of_nat 1) with 1 in BR1, BR2.
pose proof (ro_C1_of_bytes m P1 x BX) as CX. pose proof (ro_C1_of_bytes m P2 y BY) as CY.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EU1 : bv_unsigned (Z_to_bv 64 P1) = P1) by (apply unsigned_lit; lia).
assert (EU2 : bv_unsigned (Z_to_bv 64 P2) = P2) by (apply unsigned_lit; lia).
pose proof (bv_unsigned_in_range 8 x) as RX. pose proof (bv_unsigned_in_range 8 y) as RY. unfold bv_modulus in RX, RY.
change (2 ^ Z.of_N 8) with 256 in RX, RY.
assert (EUX : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia).
assert (EUY : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia).
lstep. lstep. lstep.
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned y)) as [EXY|NXY].
-
assert (x = y) by (apply bv_eq; exact EXY). subst y.
replace (bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 (bv_unsigned x))) with true by (symmetry; unfold bv_eqb; apply Z.eqb_refl).
cbn [negb]. cbv iota.
remember (Z.of_nat (Datatypes.S (length r1))) as c eqn:Ec.
assert (EUC : bv_unsigned (Z_to_bv 64 (c + -1)) = c - 1) by (rewrite unsigned_lit by lia; lia).
lstep. lstep. lstep. lstep.
if_cases K; zify_cond K.
+
destruct r1 as [|x1 r1']; [cbn [length] in Ec; lia|].
eapply evt_mono.
{ eapply (IH r2 (P1 + 1) (P2 + 1) (c + -1)); [exact LEN | discriminate | cbn [length] in *; lia | lia | lia | lia | lia | exact BR1 | exact BR2 | exact MI]. }
intros ms' (v & a1' & a2' & a3' & a4' & m' & -> & MU' & WM' & MI' & EM & IFF).
do 6 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact EM|].
rewrite IFF. split; [intros ->; reflexivity | intros E; injection E as E; exact E].
+
destruct r1 as [|x1 r1']; [| cbn [length] in Ec; lia]. destruct r2; [| discriminate LEN].
lstep. lstep.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [reflexivity|].
split; [reflexivity | intros _; reflexivity].
-
replace (bv_eqb (Z_to_bv 64 (bv_unsigned x)) (Z_to_bv 64 (bv_unsigned y))) with false.
2:{ symmetry. unfold bv_eqb. apply Z.eqb_neq. rewrite EUX, EUY. exact NXY. }
cbn [negb]. cbv iota.
lstep. lstep.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [reflexivity|].
split.
+ intros V. exfalso. rewrite Z_to_bv_unsigned in V. unfold bv_wrap, bv_modulus in V. change (2 ^ Z.of_N 64) with (2^64) in V.
rewrite ?EUX, ?EUY in V. Z.div_mod_to_equations. lia.
+ intros E. injection E as E _. subst y. contradiction.
Qed.

Lemma memcmp_spec : forall (p1 p2 : Z) (b1 b2 : list byte)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) -> length b1 = length b2 ->
0 <= p1 -> 0 <= p2 -> p1 + Z.of_nat (length b1) <= 2^63 -> p2 + Z.of_nat (length b1) <= 2^63 ->
bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> mem_inv asegs m ->
evt asegs (memcmp_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc b1 b2 m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe8e50) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> -> -> LEN H1 H2 B1 B2 BY1 BY2 MI.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (EUN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length b1))) = Z.of_nat (length b1)) by (apply unsigned_lit; lia).
lstep. if_cases K; zify_cond K.
- destruct b1; [| cbn [length] in K; lia]. destruct b2; [| discriminate LEN].
lstep. lstep.
apply evt_done. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [reflexivity|].
split; [reflexivity | intros _; reflexivity].
- apply (memcmp_loop b1 b2 p1 p2 (Z.of_nat (length b1))); try assumption; try reflexivity.
intros ->. cbn [length] in K. lia.
Qed.
