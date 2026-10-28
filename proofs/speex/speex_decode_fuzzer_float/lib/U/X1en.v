(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c4.
Local Ltac plia_gen stock ::= plia_size stock.
Import ListNotations.
Open Scope bv_scope.

Definition fwritex_entry := 0x34d08%Z.

Definition FILE_cells (fl0 : byte) (j1 : list byte) (WEND WPOS : Z) (j2 : list byte) (lbfw : word) : list cell :=
[CB 1 [fl0]; CB 31 j1; C8 (Z_to_bv 64 WEND); C8 (Z_to_bv 64 WPOS); CB 96 j2; C4 lbfw].

Definition wfile (m : word -> option byte) (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word)
(B : Z) (content junk : list byte) : Prop :=
rw_cells rsegs m Fp (FILE_cells fl0 j1 (B + Z.of_nat (length content) + Z.of_nat (length junk))
(B + Z.of_nat (length content)) j2 lbfw)
/\ rw_cells rsegs m B [CB (length content) content; CB (length junk) junk]
/\ Z.land (bv_unsigned fl0) 32 = 0%Z
/\ (2147483648 <= bv_unsigned lbfw mod 4294967296)%Z
/\ (0 < B)%Z /\ (B + Z.of_nat (length content) + Z.of_nat (length junk) < 2^64)%Z
/\ (Fp + 148 <= B \/ B + Z.of_nat (length content) + Z.of_nat (length junk) <= Fp)%Z.

Definition fwritex_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (bv_unsigned sp - 64) (bv_unsigned sp)
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at rsegs m' S bs.

Lemma wr_at_app : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros segs m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). repeat split; try lia.
+ intros i Hi. apply H. lia.
+ intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall segs m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros segs m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma sx32_neg : forall w : word, (2147483648 <= bv_unsigned w mod 4294967296)%Z ->
(9223372036854775808 <= bv_unsigned (sx32 w))%Z.
Proof.
intros w H. unfold sx32. rewrite unsigned_lit_wrap, swrap32_eq.
pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
change (2^64)%Z with 18446744073709551616%Z in *.
Z.div_mod_to_equations. lia.
Qed.

Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D : Z) (a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + bv_unsigned a2)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat (bv_unsigned a2)) src]
/\ bytes_at rsegs m' (bv_unsigned a1) src.
Lemma memcpy_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (src junk : list byte),
bytes_at rsegs m (bv_unsigned a1) src ->
length src = Z.to_nat (bv_unsigned a2) ->
rw_cells rsegs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(0 <= D < 2^64)%Z ->
(bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv rsegs m ->
evt rsegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c5c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN DST HD SEP MI.
assert (E : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D)); rewrite ?E; eauto. }
intros ms' P. unfold memcpy_post in P. rewrite !E in P. exact P.
Qed.

Ltac unwrap_in K := rewrite ?land_W64 in K; change (2^64)%Z with 18446744073709551616%Z in K; rewrite ?Z.mod_small in K by lia.

Lemma fwritex_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
wfile m (bv_unsigned a2) fl0 j1 j2 lbfw B content junk ->
bytes_at rsegs m (bv_unsigned a0) bs ->
Z.of_nat (length bs) = bv_unsigned a1 ->
(length bs <= length junk)%nat ->
stk rsegs m (bv_unsigned sp - 64) (bv_unsigned sp) ->
mem_inv rsegs m ->
(64 <= bv_unsigned sp)%Z ->
(bv_unsigned a2 + 148 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
(B + Z.of_nat (length content) + Z.of_nat (length junk) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= B)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= B + Z.of_nat (length content)
\/ B + Z.of_nat (length content) + Z.of_nat (length bs) <= bv_unsigned a0)%Z ->
(bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a2 \/ bv_unsigned a2 + 148 <= bv_unsigned a0)%Z ->
evt rsegs (fwritex_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
(bv_unsigned a2) fl0 j1 j2 lbfw B content junk (bv_unsigned a0) bs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34d08) fc None m (seg_rom rsegs)).
Proof.
intros until bs. intros sfH_; first [ sf_destruct 7%nat sfH_ as FC BUF FL LBF Bpos Bhi SEPfb | sf_fb; destruct sfH_ as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb) ]; intros SRC LEN LE ST MI SPLO SEP1 SEP2 SEP3 SEP4 SEP5.
pose_word_ranges.
set (Fp := bv_unsigned a2) in *. replace a2 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
set (S := bv_unsigned a0) in *.
set (nc := length content) in *. set (nj := length junk) in *. set (lb := length bs) in *.
pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (B + Z.of_nat nc, B + Z.of_nat nc + Z.of_nat lb); (Fp + 40, Fp + 48)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
unfold FILE_cells in FC.
carve_frame 64%nat ST.
do 8 zstep.
zstep. zstep. zstep. zstep.
zstep. if_cases Kw; zify_cond Kw; unwrap_in Kw.
{ exfalso. lia. }
zstep. zstep.
zstep. if_cases Kr; zify_cond Kr; unwrap_in Kr.
2:{ exfalso. lia. }
zstep. zstep. zstep. if_cases Kl; zify_cond Kl.
2:{ exfalso. pose proof (sx32_neg lbfw LBF). lia. }
zstep. zstep.

apply (rw_cells_split_CB rsegs _ _ [CB nc content] nj junk [] [lb; nj - lb]%nat) in BUF; [ | cbn; lia ].
cbn [mk_CB_cells app] in BUF.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUF].
cbn [cells_size csize Nat.add] in BUF. rewrite Nat.add_0_r in BUF.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in BUF. destruct BUF as [BUFb BUFc].
cbn [cells_size csize] in BUFc. rewrite Nat.add_0_r in BUFc.
zstep. call memcpy_callZ.
1:{ exact SRC. }
1:{ unfold lb in LEN. rewrite <- LEN, Nat2Z.id. reflexivity. }
1:{ rewrite <- LEN, Nat2Z.id. exact BUFb. }
1:{ lia. } 1:{ lia. } 1:{ assumption. }
rewrite <- !LEN in *. rewrite !Nat2Z.id in *.
rewrite firstn_all2 in BUFc by (rewrite length_skipn; lia).
match goal with MC : rw_cells _ _ (B + Z.of_nat nc)%Z [CB lb bs] |- _ => rename MC into BUFb end.
zstep. zstep. zstep. zstep.
replace (0 + bv_unsigned a1)%Z with (Z.of_nat lb) by lia.
replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + Z.of_nat (length (content ++ bs)))%Z by (rewrite length_app; lia).
do 9 zstep. release_frame FR ST (bv_unsigned sp).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (BUF : rw_cells rsegs mm B ([] ++ [CB nc content; CB lb bs] ++ [CB (nj - lb)%nat (skipn lb junk)]));
[ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [ exact BUFa |];
cbn [cells_size csize]; rewrite Nat.add_0_r;
apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [ exact BUFb |];
cbn [cells_size csize]; rewrite Nat.add_0_r; exact BUFc
| apply rw_cells_merge in BUF; cbn [cells_size cells_bytes csize cbytes app Nat.add] in BUF;
rewrite Nat.add_0_r, app_nil_r in BUF; clear BUFa BUFb BUFc ]
end.
apply evt_done. unfold fwritex_post.
repeat (lazymatch goal with |- ex _ => eexists end).
split; [ ms_eq | ].
repeat match goal with |- _ /\ _ => split end; try assumption;
try (replace (bv_unsigned sp - 64)%Z with (bv_unsigned sp + -64)%Z by lia; assumption).

unfold wfile, FILE_cells. rewrite !length_app, !length_skipn. fold nc lb nj.
rewrite !Nat2Z.inj_add, !Nat2Z.inj_sub by lia.
replace (B + (Z.of_nat nc + Z.of_nat lb) + (Z.of_nat nj - Z.of_nat lb))%Z with (B + Z.of_nat nc + Z.of_nat nj)%Z by lia.
replace (B + Z.of_nat nc + bv_unsigned a1)%Z with (B + (Z.of_nat nc + Z.of_nat lb))%Z in FC by lia.
split; [exact FC|]. split; [exact BUF|]. split; [exact FL|]. split; [exact LBF|]. split; [lia|]. split; lia.
Qed.

Definition fwritex_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte)
(S : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length bs))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 64, q);
(B + Z.of_nat (length content), B + Z.of_nat (length content) + Z.of_nat (length bs));
(Fp + 40, Fp + 48)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 64) q
/\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ bs) (skipn (length bs) junk)
/\ bytes_at rsegs m' S bs.

Lemma fwritex_call : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q S L Fp : Z)
(fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk bs : list byte),
wfile m Fp fl0 j1 j2 lbfw B content junk ->
bytes_at rsegs m S bs ->
Z.of_nat (length bs) = L ->
(length bs <= length junk)%nat ->
stk rsegs m (q - 64) q ->
mem_inv rsegs m ->
(64 <= q < 2^64)%Z -> (0 <= S)%Z -> (S + L < 2^64)%Z -> (0 <= Fp)%Z ->
(Fp + 148 <= q - 64 \/ q <= Fp)%Z ->
(B + Z.of_nat (length content) + Z.of_nat (length junk) <= q - 64 \/ q <= B)%Z ->
(S + L <= q - 64 \/ q <= S)%Z ->
(S + L <= B + Z.of_nat (length content) \/ B + Z.of_nat (length content) + L <= S)%Z ->
(S + L <= Fp \/ Fp + 148 <= S)%Z ->
evt rsegs (fwritex_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
Fp fl0 j1 j2 lbfw B content junk S bs m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x34d08) fc None m (seg_rom rsegs)).
Proof.
intros until bs. intros WF SRC LEN LE ST MI Hq HS HSL HFp SEP1 SEP2 SEP3 SEP4 SEP5.
assert (HF : (Fp + 148 <= 2^64)%Z).
{ destruct WF as (FC & _). pose proof (rw_cells_bound _ _ _ _ FC) as BF. unfold FILE_cells in BF. cbn [cells_size csize Nat.add length] in BF.
lia. }
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (El : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (fwritex_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) (Z_to_bv 64 Fp)); rewrite ?Eq, ?Es, ?El, ?Ef; eauto; lia. }
intros ms' P. unfold fwritex_post in P. rewrite !Eq, !Es, !Ef in P. exact P.
Qed.
