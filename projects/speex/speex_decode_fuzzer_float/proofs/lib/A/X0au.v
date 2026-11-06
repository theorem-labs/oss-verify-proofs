(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0aq.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma ro_f32_win : forall m B (l : list word) (n : Z) (cnt : nat), ro_cells asegs m B (f32 l) ->
0 <= n -> n + Z.of_nat cnt <= Z.of_nat (length l) ->
exists w, length w = cnt /\ ro_cells asegs m (B + 4 * n) (f32 w).
Proof.
intros m B l n cnt X Hn Hn2.
pose proof (ro_f32_mid asegs m B l (Z.to_nat n) cnt X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
exists (firstn cnt (skipn (Z.to_nat n) l)). split; [| exact W].
rewrite firstn_length_le; [reflexivity|]. rewrite skipn_length. lia.
Qed.

Section INNER.
Variables (m : mem) (A X1 X2 XN n1 b : Z) (al xl1 xl2 : list word).
Variables rav spv gp tp t0v t2v s0v s1v a3v a4v a5v a6v s2v s3v s5v s6v s7v : word.
Hypothesis OBA : aobj asegs m A 256.
Hypothesis OB1 : aobj asegs m X1 XN.
Hypothesis OB2 : aobj asegs m X2 XN.
Hypothesis A8 : A mod 8 = 0.
Hypothesis X14 : X1 mod 4 = 0.
Hypothesis X24 : X2 mod 4 = 0.
Hypothesis LA : length al = 64%nat.
Hypothesis L1 : Z.of_nat (length xl1) = n1 + 33.
Hypothesis L2 : Z.of_nat (length xl2) = n1 + 33.
Hypothesis LXN : 4 * (n1 + 33) <= XN.
Hypothesis Hb : 1 <= b <= n1.
Hypothesis RA : ro_cells asegs m A (f32 al).
Hypothesis RX1 : rw_cells asegs m X1 (f32 xl1).
Hypothesis RX2 : rw_cells asegs m X2 (f32 xl2).

Definition RI (xa xs jz off : Z) (a1v a2v s10v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v (Z_to_bv 64 (X1 + 4 * (n1 + 1))) t2v s0v s1v (Z_to_bv 64 xa) a1v a2v a3v a4v a5v a6v (Z_to_bv 64 (X2 + 4 * (n1 + 1)))
s2v s3v (Z_to_bv 64 32) s5v s6v s7v (Z_to_bv 64 jz) (Z_to_bv 64 xs) s10v (Z_to_bv 64 SHB)
(Z_to_bv 64 (Z.shiftr A 3 + SHB)) (Z_to_bv 64 (X1 + 4 * n1)) (Z_to_bv 64 (X2 + 4 * n1)) (Z_to_bv 64 off).

Definition inner_post : machine_state -> Prop :=
fun ms' => exists a1' a2' s10' F' fc',
ms' = MS (RI (A + 8 * 32) (A + 8 * 32 + 8) 32 (4 * (b + 32 - n1)) a1' a2' s10') F' (Z_to_bv 64 0xa50c8) fc' None m (seg_rom asegs)
/\ frm0 fc'.

Ltac inner_iter jz off :=
astep; replace (Z.shiftr A 3 + SHB + jz) with (Z.shiftr (A + 8 * jz) 3 + SHB) by (rewrite shiftr3_add; lia);
astep; astep; chk_merge OBA 4;
ato 0xa4f5c; astep; chk_merge OBA 4;
ato 0xa4f64; replace (X1 + 4 * n1 + off) with (X1 + 4 * (b + jz)) by lia;
ato 0xa4f74; astep; chk_merge OB1 4;
ato 0xa4f7c; replace (X2 + 4 * n1 + off) with (X2 + 4 * (b + jz)) by lia;
ato 0xa4f8c; astep; chk_merge OB2 4;
ato 0xa4fa4; astep; chk_merge OBA 4;
ato 0xa4fbc; astep; chk_merge OBA 4;
ato 0xa4fc4; replace (X1 + 4 * (n1 + 1) + off) with (X1 + 4 * (b + jz) + 4) by lia;
ato 0xa4fd4; astep; chk_merge OB1 4;
ato 0xa4fdc; replace (X2 + 4 * (n1 + 1) + off) with (X2 + 4 * (b + jz) + 4) by lia;
ato 0xa4fec; astep; chk_merge OB2 4;
ato 0xa5040; astep.

Lemma qmf_inner : forall (k : nat) (xa xs jz off : Z) (a1v a2v s10v : word) F1 fc,
xa = A + 8 * jz -> xs = A + 8 * jz + 8 -> jz + 2 + 2 * Z.of_nat k = 32 -> 0 <= jz -> off = 4 * (b + jz - n1) ->
frm0 fc -> mem_inv asegs m ->
evt asegs inner_post (MS (RI xa xs jz off a1v a2v s10v) F1 (Z_to_bv 64 0xa4f3c) fc None m (seg_rom asegs)).
Proof using OBA OB1 OB2 A8 X14 X24 LA L1 L2 LXN Hb RA RX1 RX2.
pose proof OBA as (OA0 & OA1 & _). pose proof OB1 as (O10 & O11 & _). pose proof OB2 as (O20 & O21 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros xa xs jz off a1v a2v s10v F1 fc -> -> Hj Hj0 Hoff FRM MI;
destruct (ro_f32_win m A al (2 * jz) 4%nat RA ltac:(lia) ltac:(rewrite LA; lia)) as (wa & Lwa & WA);
destruct wa as [|q0 [|q1 [|q2 [|q3 [|? ?]]]]]; try (cbn in Lwa; lia); clear Lwa;
replace (A + 4 * (2 * jz)) with (A + 8 * jz) in WA by lia; rewrite !f32_cons, f32_nil in WA;
destruct (f32_win m X1 xl1 (b + jz) 2%nat RX1 ltac:(lia) ltac:(lia)) as (w1 & Lw1 & W1);
destruct w1 as [|u0 [|u1 [|? ?]]]; try (cbn in Lw1; lia); clear Lw1; rewrite !f32_cons, f32_nil in W1;
destruct (f32_win m X2 xl2 (b + jz) 2%nat RX2 ltac:(lia) ltac:(lia)) as (w2 & Lw2 & W2);
destruct w2 as [|v0 [|v1 [|? ?]]]; try (cbn in Lw2; lia); clear Lw2; rewrite !f32_cons, f32_nil in W2;
unfold RI.
- inner_iter jz off. sh_if. astep.
replace (jz + 2) with 32 by lia. replace (A + 8 * jz + 16) with (A + 8 * 32) by lia. replace (A + 8 * jz + 24) with (A + 8 * 32 + 8) by lia.
replace (off + 8) with (4 * (b + 32 - n1)) by lia.
apply evt_done; unfold inner_post, RI. do 5 eexists. split; [reflexivity| assumption].
- inner_iter jz off. sh_if.
replace (A + 8 * jz + 16) with (A + 8 * (jz + 2)) by lia. replace (A + 8 * jz + 24) with (A + 8 * (jz + 2) + 8) by lia.
eapply (IH _ _ (jz + 2) (off + 8)); [reflexivity | lia | lia | lia | lia | assumption | exact MI].
Qed.
End INNER.
