(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0yq X0yp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma ro_f32_winB : forall m B (l : list word) (n : Z) (cnt : nat), ro_cells bsegs m B (f32 l) ->
0 <= n -> n + Z.of_nat cnt <= Z.of_nat (length l) ->
exists w, length w = cnt /\ ro_cells bsegs m (B + 4 * n) (f32 w).
Proof.
intros m B l n cnt X Hn Hn2.
pose proof (ro_f32_mid bsegs m B l (Z.to_nat n) cnt X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
exists (firstn cnt (skipn (Z.to_nat n) l)). split; [| exact W].
rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia.
Qed.
Lemma f32_winB : forall m B (l : list word) (n : Z) (cnt : nat), rw_cells bsegs m B (f32 l) ->
0 <= n -> n + Z.of_nat cnt <= Z.of_nat (length l) ->
exists w, length w = cnt /\ rw_cells bsegs m (B + 4 * n) (f32 w).
Proof.
intros m B l n cnt X Hn Hn2.
pose proof (rw_cells_f32_mid bsegs m B l (Z.to_nat n) cnt X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
exists (firstn cnt (skipn (Z.to_nat n) l)). split; [| exact W].
rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia.
Qed.

Section INNERB.
Variables (m : mem) (A X1 X2 XN N2 i FB : Z) (al xl1 xl2 : list word).
Variables spv gp tp t1v t5v s0v a5v a7v : word.
Hypothesis OBA : aobj bsegs m A 256.
Hypothesis OB1 : aobj bsegs m X1 XN.
Hypothesis OB2 : aobj bsegs m X2 XN.
Hypothesis A8 : A mod 8 = 0.
Hypothesis AR : 0 < A /\ A + 256 < 2^62.
Hypothesis X14 : X1 mod 4 = 0.
Hypothesis X24 : X2 mod 4 = 0.
Hypothesis X1R : 0 < X1 /\ X1 + XN < 2^62.
Hypothesis X2R : 0 < X2 /\ X2 + XN < 2^62.
Hypothesis LA : length al = 64%nat.
Hypothesis L1 : Z.of_nat (length xl1) = N2 + 32.
Hypothesis L2 : Z.of_nat (length xl2) = N2 + 32.
Hypothesis LXN : 4 * (N2 + 32) <= XN.
Hypothesis NR : 2 <= N2 < 2^20.
Hypothesis Hi : 0 <= i <= N2 - 2.
Hypothesis FBR : 0 <= FB /\ FB + 208 < 2^63.
Hypothesis RA : ro_cells bsegs m A (f32 al).
Hypothesis RX1 : rw_cells bsegs m X1 (f32 xl1).
Hypothesis RX2 : rw_cells bsegs m X2 (f32 xl2).
Hypothesis SM : rw_cells bsegs m (FB + 56) [C8 (Z_to_bv 64 32)].

Definition RIB (j : Z) (t0v a0v a1v a2v s6v s7v : word) : bvmap 5 word :=
mkR (Z_to_bv 64 (8 * j)) spv gp tp t0v t1v (Z_to_bv 64 1) s0v (Z_to_bv 64 FB) a0v a1v a2v (Z_to_bv 64 (18446744073709551615 - X1)) (Z_to_bv 64 (N2 - 1)) a5v
(Z_to_bv 64 (18446744073709551615 - X2)) a7v (Z_to_bv 64 N2) (Z_to_bv 64 (32 + N2)) (Z_to_bv 64 X2) (Z_to_bv 64 X1) s6v s7v (Z_to_bv 64 A) (Z_to_bv 64 i)
(Z_to_bv 64 j) (Z_to_bv 64 SHB) (Z_to_bv 64 j) (Z_to_bv 64 (18446744073709551615 - A)) t5v (Z_to_bv 64 1).

Definition innerB_post : machine_state -> Prop :=
fun ms' => exists t0' a0' a1' a2' s6' s7' F' fc',
ms' = MS (RIB 32 t0' a0' a1' a2' s6' s7') F' (Z_to_bv 64 0xa8c3c) fc' None m (seg_rom bsegs)
/\ frm0 fc'.

Ltac inner_iterB j :=
bato 0xa8a3c; astep; chk_merge OBA 4;
bato 0xa8a5c; astep; chk_merge OBA 4;
bato 0xa8a98; replace ((N2 - 1 + j + 0 - i) * 4) with (4 * (N2 - 1 + j - i)) by lia;
bato 0xa8aa8; astep; chk_merge OB1 4;
bato 0xa8ac0; astep; chk_merge OB2 4;
bato 0xa8ae0; astep; chk_merge OBA 4;
bato 0xa8b00; astep; chk_merge OBA 4;
bato 0xa8b38; replace (X1 + (N2 + j + 0 - i) * 4) with (X1 + 4 * (N2 - 1 + j - i) + 4) by lia;
bato 0xa8b48; astep; chk_merge OB1 4;
bato 0xa8b50; replace (X2 + (N2 + j + 0 - i) * 4) with (X2 + 4 * (N2 - 1 + j - i) + 4) by lia;
bato 0xa8b60; astep; chk_merge OB2 4;
bato 0xa8bb4; rewrite swrap32_small by lia; astep.

Lemma qmf_innerB : forall (k : nat) (j : Z) (t0v a0v a1v a2v s6v s7v : word) F1 fc,
j + 2 + 2 * Z.of_nat k = 32 -> 0 <= j ->
frm0 fc -> mem_inv bsegs m ->
evt bsegs innerB_post (MS (RIB j t0v a0v a1v a2v s6v s7v) F1 (Z_to_bv 64 0xa8a1c) fc None m (seg_rom bsegs)).
Proof using OBA OB1 OB2 A8 AR X14 X24 X1R X2R LA L1 L2 LXN NR Hi FBR RA RX1 RX2 SM.
pose proof OBA as (OA0 & OA1 & _). pose proof OB1 as (O10 & O11 & _). pose proof OB2 as (O20 & O21 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros j t0v a0v a1v a2v s6v s7v F1 fc Hj Hj0 FRM MI;
destruct (ro_f32_winB m A al (2 * j) 4%nat RA ltac:(lia) ltac:(rewrite LA; lia)) as (wa & Lwa & WA);
destruct wa as [|q0 [|q1 [|q2 [|q3 [|? ?]]]]]; try (cbn in Lwa; lia); clear Lwa;
replace (A + 4 * (2 * j)) with (A + 8 * j) in WA by lia; rewrite !f32_cons, f32_nil in WA;
destruct (f32_winB m X1 xl1 (N2 - 1 + j - i) 2%nat RX1 ltac:(lia) ltac:(lia)) as (w1 & Lw1 & W1);
destruct w1 as [|u0 [|u1 [|? ?]]]; try (cbn in Lw1; lia); clear Lw1; rewrite !f32_cons, f32_nil in W1;
destruct (f32_winB m X2 xl2 (N2 - 1 + j - i) 2%nat RX2 ltac:(lia) ltac:(lia)) as (w2 & Lw2 & W2);
destruct w2 as [|v0 [|v1 [|? ?]]]; try (cbn in Lw2; lia); clear Lw2; rewrite !f32_cons, f32_nil in W2;
unfold RIB.
- inner_iterB j. sh_if. astep.
replace (8 * j + 16) with (8 * 32) by lia. replace (j + 2) with 32 by lia.
apply evt_done. unfold innerB_post, RIB. do 8 eexists. split; [reflexivity | assumption].
- inner_iterB j. sh_if.
replace (8 * j + 16) with (8 * (j + 2)) by lia.
eapply (IH (j + 2)); [lia | lia | assumption | exact MI].
Qed.
End INNERB.
