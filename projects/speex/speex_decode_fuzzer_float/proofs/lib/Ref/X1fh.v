(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1ho X1hm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.

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
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis LI1 : length i1 = 80%nat.
Hypothesis LI2 : length i2 = 80%nat.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Hypothesis HI2 : I2 = I1 + 320.
Hypothesis ANE : apart ne 320 EB 2000.
Hypothesis ANI : apart ne 320 I1 640.
Local Notation exc := (EB + 4 * eoff).

Definition l1_post : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (I1 + 640)) (Z_to_bv 64 (exc + 320)) (Z_to_bv 64 (ne + 320))
a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (I1 + 320)) (Z_to_bv 64 (I1 + 640)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x2176c) fc' None m' (seg_rom rsegs)
/\ munch [(ne, ne + 320)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' ne (f32 ns') /\ length ns' = 80%nat.

#[using="LEB LI1 LI2 R3 R4 HI2 ANE ANI"] Lemma loop1 : forall (k : nat) (done rest : list word) (i ca xa c4 c5 : Z) (cw : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) ->
ca = ne + 4 * i -> xa = exc + 4 * i -> c4 = I1 + 4 * i -> c5 = I1 + 320 + 4 * i ->
frm0 fc -> mem_inv rsegs m -> munch [(ne, ne + 320)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m EB (f32 eb) -> rw_cells rsegs m I1 (f32 i1) -> rw_cells rsegs m I2 (f32 i2) ->
rw_cells rsegs m ne (f32 done) -> rw_cells rsegs m ca (f32 (cw :: rest)) ->
evt rsegs l1_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (I1 + 640)) (Z_to_bv 64 xa) (Z_to_bv 64 ca)
a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 c4) (Z_to_bv 64 c5) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x2173c) fc None m (seg_rom rsegs)).
Proof.
unfold apart in ANE, ANI.
induction k as [|k IH]; intros done rest i ca xa c4 c5 cw G fc m LR LD Hi Hca Hxa Hc4 Hc5 FRM MI MU WM XEB XI1 XI2 XD XC;
pose proof (rw_cells_bound _ _ _ _ XEB) as BEB; rewrite cells_size_f32, LEB in BEB;
pose proof (rw_cells_bound _ _ _ _ XI1) as BI1; rewrite cells_size_f32, LI1 in BI1;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (f32_win1 m EB eb 500%nat (eoff + i) XEB LEB ltac:(lia) ltac:(lia)) as (y1 & W1);
destruct (f32_win1 m I1 i1 80%nat i XI1 LI1 ltac:(lia) ltac:(lia)) as (y4 & W4);
destruct (f32_win1 m I2 i2 80%nat i XI2 LI2 ltac:(lia) ltac:(lia)) as (y5 & W5);
replace (EB + 4 * (eoff + i)) with xa in W1 by lia; replace (I1 + 4 * i) with c4 in W4 by lia; replace (I2 + 4 * i) with c5 in W5 by lia;
rewrite f32_cons, f32_nil in W1, W4, W5.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
do 12 zstep. if_false_x. clear W1 W4 W5.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (xa + 4) with (exc + 320) by lia. replace (ca + 4) with (ne + 320) by lia.
replace (c4 + 4) with (I1 + 320) by lia. replace (c5 + 4) with (I1 + 640) by lia.
apply evt_done; unfold l1_post. sf_eexists 4%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|].
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
do 12 zstep. if_true_x. clear W1 W4 W5.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (ca + 4) (xa + 4) (c4 + 4) (c5 + 4) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia | lia | lia | lia
| assumption | exact MI | exact MU | exact WM | exact XEB | exact XI1 | exact XI2 | exact XD | exact XC ].
Qed.
End L1.

Section L2.
Context {RCEIL : RunCeiling}.

Variables (A : Z) (xs : list word) (m : mem).
Variables ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Hypothesis LX : length xs = 80%nat.

Definition l2_post : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + 320)) (Z_to_bv 64 (A + 320)) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21790) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

#[using="LX"] Lemma loop2 : forall (k : nat) (i ca : Z) (G : bvmap 5 word) (fc : bv 32),
i + Z.of_nat k = 79 -> 0 <= i -> ca = A + 4 * i ->
frm0 fc -> mem_inv rsegs m -> rw_cells rsegs m A (f32 xs) ->
evt rsegs l2_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + 320)) (Z_to_bv 64 ca) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x21780) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ca G fc Hik Hi Hca FRM MI X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LX in BX;
destruct (f32_win1 m A xs 80%nat i X LX ltac:(lia) ltac:(lia)) as (y & W);
replace (A + 4 * i) with ca in W by lia; rewrite f32_cons, f32_nil in W.
- do 4 zstep. if_false_x. replace (ca + 4) with (A + 320) by lia.
apply evt_done; unfold l2_post. sf_eexists 2%nat. split; [reflexivity| assumption].
- do 4 zstep. if_true_x. clear W.
eapply (IH (i + 1) (ca + 4)); [lia | lia | lia | assumption | exact MI | exact X].
Qed.
End L2.

Section L3.
Context {RCEIL : RunCeiling}.

Variables (EB eoff : Z) (eb : list word) (m : mem).
Variables ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Hypothesis LEB : length eb = 500%nat.
Hypothesis R3 : eoff + 80 <= 500.
Hypothesis R4 : 0 <= eoff.
Local Notation exc := (EB + 4 * eoff).

Definition l3_post : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (exc + 320)) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 (exc + 320)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x217c8) fc' None m (seg_rom rsegs)
/\ frm0 fc'.

#[using="LEB R3 R4"] Lemma loop3 : forall (k : nat) (i ca : Z) (G : bvmap 5 word) (fc : bv 32),
i + Z.of_nat k = 79 -> 0 <= i -> ca = exc + 4 * i ->
frm0 fc -> mem_inv rsegs m -> rw_cells rsegs m EB (f32 eb) ->
evt rsegs l3_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (exc + 320)) a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 ca) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x217b8) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i ca G fc Hik Hi Hca FRM MI X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32, LEB in BX;
destruct (f32_win1 m EB eb 500%nat (eoff + i) X LEB ltac:(lia) ltac:(lia)) as (y & W);
replace (EB + 4 * (eoff + i)) with ca in W by lia; rewrite f32_cons, f32_nil in W.
- do 4 zstep. if_false_x. replace (ca + 4) with (exc + 320) by lia.
apply evt_done; unfold l3_post. sf_eexists 2%nat. split; [reflexivity| assumption].
- do 4 zstep. if_true_x. clear W.
eapply (IH (i + 1) (ca + 4)); [lia | lia | lia | assumption | exact MI | exact X].
Qed.
End L3.

Section L4.
Context {RCEIL : RunCeiling}.

Variables (ne : Z) (m0 : mem).
Variables ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word.

Definition l4_post : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ns' : list word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (ne + 320)) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (ne + 320)) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21834) fc' None m' (seg_rom rsegs)
/\ munch [(ne, ne + 320)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ rw_cells rsegs m' ne (f32 ns') /\ length ns' = 80%nat.

#[using="Type"] Lemma loop4 : forall (k : nat) (done rest : list word) (i ca : Z) (cw : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
length rest = k -> (length done + k = 79)%nat -> i = Z.of_nat (length done) -> ca = ne + 4 * i ->
frm0 fc -> mem_inv rsegs m -> munch [(ne, ne + 320)] m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m ne (f32 done) -> rw_cells rsegs m ca (f32 (cw :: rest)) ->
evt rsegs l4_post
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 ca) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (ne + 320)) s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x21820) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros done rest i ca cw G fc m LR LD Hi Hca FRM MI MU WM XD XC;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
pose proof (rw_cells_bound _ _ _ _ XD) as BD; rewrite cells_size_f32 in BD.
- destruct rest; [|cbn in LR; lia]. cbn [length] in LD. rewrite f32_cons, f32_nil in XC.
do 5 zstep. if_false_x.
chunk_snoc XD XC. rewrite f32_snoc in XD. replace (ca + 4) with (ne + 320) by lia.
apply evt_done; unfold l4_post. sf_eexists 4%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|].
split; [exact XD|]. rewrite length_app; cbn [length]; lia.
- destruct rest as [|cw' rest]; [cbn in LR; lia|]. cbn [length] in LR, LD, BC. rewrite !f32_cons in XC.
do 5 zstep. if_true_x.
chunk_uncons XC as X1. chunk_snoc XD X1. rewrite f32_snoc in XD. rewrite <- !f32_cons in XC.
eapply (IH (done ++ [_]) rest (i + 1) (ca + 4) cw');
[ lia | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia | lia
| assumption | exact MI | exact MU | exact WM | exact XD | exact XC ].
Qed.
End L4.
