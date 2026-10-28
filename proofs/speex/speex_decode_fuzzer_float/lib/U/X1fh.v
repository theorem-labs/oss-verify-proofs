(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ed.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Lemma f32_win1 : forall m A (l : list word) (L : nat) (n : Z), rw_cells rsegs m A (f32 l) -> length l = L ->
0 <= n -> n + 1 <= Z.of_nat L ->
exists y0, rw_cells rsegs m (A + 4 * n) (f32 [y0]).
Proof.
intros m A l L n X HL Hn Hn2.
pose proof (rw_cells_f32_mid rsegs m A l (Z.to_nat n) 1 X ltac:(lia)) as W.
rewrite Z2Nat.id in W by lia.
remember (firstn 1 (skipn (Z.to_nat n) l)) as w eqn:Hw.
assert (Lw : length w = 1%nat) by (subst w; rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct w as [|y0 [|? ?]]; try (cbn in Lw; lia).
exists y0. exact W.
Qed.

Section L1.
Context {RCEIL : RunCeiling}.
Variables (EB eoff ne I1 I2 : Z) (eb i1 i2 : list word) (m0 : mem).
Variables ra sp gp tp s0 s5 s6 s7 s10 t3 t4 t5 t6 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis LI1 : length i1 = 80%nat.
Hypothesis LI2 : length i2 = 80%nat.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis HI2 : I2 = I1 + 320.
Hypothesis ANE : apart ne 320 EB 2000.
Hypothesis ANI : apart ne 320 I1 640.
Hypothesis E0 : 0 < EB + 4 * eoff.
Hypothesis N0 : 0 < ne.
Local Notation exc := (EB + 4 * eoff).

Definition l1_post : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 (Z_to_bv 64 80) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 ne) (Z_to_bv 64 exc) (Z_to_bv 64 I1) s5 s6 s7 (Z_to_bv 64 640) (Z_to_bv 64 (2^64 - 1 - I1)) s10 (Z_to_bv 64 320) t3 t4 t5 t6)
F' (Z_to_bv 64 0x24a50) fc' None m' (seg_rom rsegs)
/\ munch [(ne, ne + 320)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' ne (f32 ns') /\ length ns' = 80%nat.

#[using="LEB LI1 LI2 R3 R4 HI2 ANE ANI E0 N0"] Lemma loop1 : forall (k : nat) (done rest : list word) (i ca : Z) (cw t0v t1v t2v a7v : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> ca = ne + 4 * i ->
frm0 fc -> mem_inv rsegs m -> munch [(ne, ne + 320)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m I1 (f32 i1) -> rw_cells rsegs m I2 (f32 i2) ->
rw_cells rsegs m ne (f32 done) -> rw_cells rsegs m ca (f32 (cw :: rest)) ->
evt rsegs l1_post
(MS (mkR ra sp gp tp t0v t1v t2v s0 (Z_to_bv 64 80) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i))
(Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 320) a7v
(Z_to_bv 64 ne) (Z_to_bv 64 exc) (Z_to_bv 64 I1) s5 s6 s7 (Z_to_bv 64 640) (Z_to_bv 64 (2^64 - 1 - I1)) s10 (Z_to_bv 64 320) t3 t4 t5 t6)
G (Z_to_bv 64 0x249d4) fc None m (seg_rom rsegs)).
Proof.
unfold apart in ANE, ANI.
induction k as [|k IH]; intros done rest i ca cw t0v t1v t2v a7v G fc m LR LD Hi Hca FRM MI MU WM XEB XI1 XI2 XD XC;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XI1) as BI1; rewrite cells_size_f32, LI1 in BI1;
pose proof (rw_cells_bound _ _ _ _ XI2) as BI2; rewrite cells_size_f32, LI2 in BI2;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1 m EB eb 500%nat (eoff + i) XEB LEB ltac:(lia) ltac:(lia)) as (y1 & W1);
destruct (f32_win1 m I1 i1 80%nat i XI1 LI1 ltac:(lia) ltac:(lia)) as (y4 & W4);
destruct (f32_win1 m I2 i2 80%nat i XI2 LI2 ltac:(lia) ltac:(lia)) as (y5 & W5);
rewrite f32_cons, f32_nil in W1, W4, W5.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
bato 0x24a24%Z.
replace (I2 + 4 * i) with (I1 + (i + 80) * 4) in W5 by lia. replace (EB + 4 * (eoff + i)) with (EB + 4 * eoff + 4 * i) in W1 by lia.
set (c5 := I1 + (i + 80) * 4) in *. set (xa := EB + 4 * eoff + 4 * i) in *. rewrite <- Hca.
do 2 zstep. set (c4 := I1 + 4 * i) in *.
bato 0x24a4c%Z. zstep. if_false_x. clear W1 W4 W5.
chunk_snoc XD XC. rewrite f32_snoc in XD.
apply evt_done; unfold l1_post. sf_eexists 15%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|].
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
bato 0x24a24%Z.
replace (I2 + 4 * i) with (I1 + (i + 80) * 4) in W5 by lia. replace (EB + 4 * (eoff + i)) with (EB + 4 * eoff + 4 * i) in W1 by lia.
set (c5 := I1 + (i + 80) * 4) in *. set (xa := EB + 4 * eoff + 4 * i) in *. rewrite <- Hca.
do 2 zstep. set (c4 := I1 + 4 * i) in *.
bato 0x24a4c%Z. zstep. if_true_x. clear W1 W4 W5.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?v0 ?v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
replace v0 with (Z_to_bv 64 (i + 1)) by (rewrite ?swrap32_mod64_add, ?swrap32_small by lia; f_equal; lia);
replace v1 with (Z_to_bv 64 (4 * (i + 1))) by (f_equal; lia) end.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (ca + 4) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia
| assumption | exact MI | exact MU | exact WM | exact XEB | exact XI1 | exact XI2 | exact XD | exact XC ].
Qed.
End L1.

Section L3.
Context {RCEIL : RunCeiling}.
Variables (xs : list word) (p : Z) (m : mem).
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Variable F : bvmap 5 word.
Hypothesis MI : mem_inv rsegs m.
Hypothesis LEN : 1 <= Z.of_nat (length xs) < 2^31.
Local Notation lenw := (Z_to_bv 64 (Z.of_nat (length xs))).

Definition l3_post : machine_state -> Prop :=
compute_rms16_post ra sp gp tp s0 s1 lenw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F xs m.

#[using="MI LEN"] Lemma loop3 : forall (a2 : word) (fc : bv 32),
rw_cells rsegs m p (f32 xs) -> frm0 fc -> 0 < p -> p mod 4 = 0 ->
evt rsegs l3_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) lenw a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x22fc4) fc None m (seg_rom rsegs)).
Proof.
intros a2 fc X FRM P0 P4.
pose proof (rw_cells_bound _ _ _ _ X) as BX. rewrite cells_size_f32 in BX.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
zstep. if_false_x. do 8 zstep. cond_prep.
rewrite Exs in X. rewrite !f32_cons in X.
rms_checks. zstep.
unfold l3_post. eapply rms_loop with (rest := rest) (done := []) (x := x) (q := p); try eassumption.
all: try exact Exs.
all: try (cbn [length]; lia).
all: try (rewrite Exs; reflexivity).
Qed.
End L3.

Section L4.
Context {RCEIL : RunCeiling}.

Variables (ne : Z) (m0 : mem).
Variables ra sp gp tp t0 t1 t2 s0 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Hypothesis N0 : 0 < ne.

Definition l4_post : machine_state -> Prop :=
fun ms' => exists (a0' a1' a2' a3' a4' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) a0' a1' a2' a3' a4' a5 a6 a7
(Z_to_bv 64 ne) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x24aec) fc' None m' (seg_rom rsegs)
/\ munch [(ne, ne + 320)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' ne (f32 ns') /\ length ns' = 80%nat.

#[using="N0"] Lemma loop4 : forall (k : nat) (done rest : list word) (i ca : Z) (cw a4v : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> ca = ne + 4 * i ->
frm0 fc -> mem_inv rsegs m -> munch [(ne, ne + 320)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m ne (f32 done) -> rw_cells rsegs m ca (f32 (cw :: rest)) ->
evt rsegs l4_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (80 - i)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 ca) (Z_to_bv 64 ca) a4v a5 a6 a7
(Z_to_bv 64 ne) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x24abc) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros done rest i ca cw a4v G fc m LR LD Hi Hca FRM MI MU WM XD XC;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ XD) as BD; rewrite cells_size_f32 in BD.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
bato 0x24ae8%Z. zstep. if_false_x.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ ?v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
replace v with (Z_to_bv 64 0) by (f_equal; lia) end.
chunk_snoc XD XC. rewrite f32_snoc in XD.
apply evt_done; unfold l4_post. sf_eexists 9%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|].
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
bato 0x24ae8%Z. zstep. if_true_x.
lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ ?v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
replace v with (Z_to_bv 64 (80 - (i + 1))) by (f_equal; lia) end.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (ca + 4) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia
| assumption | exact MI | exact MU | exact WM | exact XD | exact XC ].
Qed.
End L4.
