(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1ev.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma eb_window : forall m EB (eb : list word) (k : Z), rw_cells rsegs m EB (f32 eb) -> length eb = 500%nat ->
0 <= k -> k + 80 <= 500 ->
rw_cells rsegs m (EB + 4 * k) (f32 (firstn 80 (skipn (Z.to_nat k) eb))) /\ Z.of_nat (length (firstn 80 (skipn (Z.to_nat k) eb))) = 4 * 20.
Proof.
intros m EB eb k X L Hk Hk2. split.
- replace (4 * k) with (4 * Z.of_nat (Z.to_nat k)) by lia. apply rw_cells_f32_mid; [exact X| lia].
- rewrite firstn_length_le; [lia|]. rewrite skipn_length. lia.
Qed.

Section A.
Context {RCEIL : RunCeiling}.

Variables (EB eoff p IP q lo : Z) (eb : list word) (m0 : mem).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis R1 : 0 <= eoff - p - 6.
Hypothesis R2 : eoff - p <= 414.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.

Hypothesis QLO : lo + 16 <= q.
Hypothesis Q63 : q + 192 < 2 ^ 63.
Hypothesis AEB : apart EB 2000 lo (q + 192 - lo).
Hypothesis EBP : 1 <= eoff.
Hypothesis EBA : EB mod 4 = 0.
Local Notation exc := (EB + 4 * eoff).
Local Notation FRAME := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition corr0_post : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G' : bvmap 5 word) (fc' : bv 32) (m' : mem) (c0 : list word),
ms' = MS (mkR (Z_to_bv 64 0x24bf0) (Z_to_bv 64 q) gp tp t0 t1 t2 (Z_to_bv 64 exc) (Z_to_bv 64 IP) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 p) (Z_to_bv 64 1) (Z_to_bv 64 (exc - 4 * p - 12)) (Z_to_bv 64 28) (Z_to_bv 64 (18446744073709551615 - (exc - 4 * p - 12)))
(Z_to_bv 64 q) (Z_to_bv 64 28) s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0x24c00) fc' None m' (seg_rom rsegs)
/\ munch [(lo, q + 28)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' q (f32 c0) /\ length c0 = 7%nat /\ stk rsegs m' lo q.

#[using="lo LEB R1 R2 R3 R4 QLO Q63 AEB EBP EBA"] Lemma corr0_loop : forall (k : nat) (done rest : list word) (cs cy co : Z) (cw : word)
(xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 6)%nat ->
cs = q + 4 * Z.of_nat (length done) -> cy = exc - 4 * p - 12 -> co = 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, q + 28)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo q ->
rw_cells rsegs m EB (f32 eb) ->
rw_cells rsegs m q (f32 done) -> rw_cells rsegs m cs (f32 (cw :: rest)) ->
evt rsegs corr0_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 (Z_to_bv 64 exc) (Z_to_bv 64 IP) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 p) (Z_to_bv 64 1) (Z_to_bv 64 cy) (Z_to_bv 64 co) (Z_to_bv 64 (18446744073709551615 - cy))
(Z_to_bv 64 q) (Z_to_bv 64 28) s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x24bdc) fc None m (seg_rom rsegs)).
Proof.
unfold apart in AEB.
induction k as [|k IH]; intros done rest cs cy co cw xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 G fc m
LR LD Hcs Hcy Hco FRM MI MU WM ST XEB CD CC;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ CD) as BD;
pose proof (rw_cells_bound _ _ _ _ CC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (eb_window m EB eb eoff XEB LEB ltac:(lia) ltac:(lia)) as [WX LX];
destruct (eb_window m EB eb (eoff - p - 3 + Z.of_nat (length done)) XEB LEB ltac:(lia) ltac:(lia)) as [WY LY];
rewrite <- Hco in Hcs;
assert (USP : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in CC.
zstep. ub_dec. zstep. zstep. zstep. zstep.
replace (cy + co) with (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) by lia.
call (inner_prod_spec (firstn 80 (skipn (Z.to_nat eoff) eb)) (firstn 80 (skipn (Z.to_nat (eoff - p - 3 + Z.of_nat (length done))) eb)) 20
exc (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) lo);
[ exact MI | lia | exact LX | exact LY | lia | rewrite Z.mul_comm, Z.mod_add by lia; exact EBA | lia | rewrite Z.mul_comm, Z.mod_add by lia; exact EBA
| rewrite USP; exact ST | lia | unfold apart; lia | unfold apart; lia | exact WX | exact WY | exact FRM | ].
rename MI0 into MI || idtac.
match goal with H : stk _ _ _ (bv_unsigned _) |- _ => rewrite USP in H end.
zstep. replace (q + co) with cs by lia. zstep. zstep. zstep. if_false_x.
chunk_snoc CD CC. rewrite f32_snoc in CD.
replace (co + 4) with 28 by lia. subst cy.
apply evt_done; unfold corr0_post.
sf_eexists 19%nat; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|].
split; [exact CD|]. split; [rewrite length_app; cbn [length]; lia|]. assumption.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in CC.
zstep. ub_dec. zstep. zstep. zstep. zstep.
replace (cy + co) with (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) by lia.
call (inner_prod_spec (firstn 80 (skipn (Z.to_nat eoff) eb)) (firstn 80 (skipn (Z.to_nat (eoff - p - 3 + Z.of_nat (length done))) eb)) 20
exc (EB + 4 * (eoff - p - 3 + Z.of_nat (length done))) lo);
[ exact MI | lia | exact LX | exact LY | lia | rewrite Z.mul_comm, Z.mod_add by lia; exact EBA | lia | rewrite Z.mul_comm, Z.mod_add by lia; exact EBA
| rewrite USP; exact ST | lia | unfold apart; lia | unfold apart; lia | exact WX | exact WY | exact FRM | ].
rename MI0 into MI || idtac.
match goal with H : stk _ _ _ (bv_unsigned _) |- _ => rewrite USP in H end.
zstep. replace (q + co) with cs by lia. zstep. zstep. zstep. if_true_x.
chunk_uncons CC as C1. chunk_snoc CD C1. rewrite f32_snoc in CD.
eapply (IH (done ++ [_]) rest (cs + 4) cy (co + 4));
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | exact Hcy | rewrite length_app; cbn [length]; lia
| assumption | exact MI | exact MU | exact WM | assumption | assumption | exact CD | exact CC ].
Qed.
End A.
