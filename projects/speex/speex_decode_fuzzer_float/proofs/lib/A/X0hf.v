(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg X1cj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j2 X0j3 X0gi X02b X0he.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9 X1e5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.MallocA Require Import X1dn.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X19m X173 X0ta X17z.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ta OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17z.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA.X1e9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA.X1e5.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.MallocA.X1dn.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac addr_near k ::=
let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 512))%Z in
lazymatch inb with true => idtac end.

Definition intalloc_entry : Z := 0x74018.
Definition IAP : Z := 0x106cc0.
Definition g_ia_word : Z := 0x195548.

Lemma rw_cells_relist : forall m A cs cs',
rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells bsegs m A cs'.
Proof.
intros m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'| rewrite E; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy| apply IH; exact Hl].
Qed.

Lemma rw_cells_relistZ : forall m A cs cs',
rw_cells bsegs m A cs -> cells_wf cs' ->
map (@bv_unsigned 8) (cells_bytes cs') = map (@bv_unsigned 8) (cells_bytes cs) -> rw_cells bsegs m A cs'.
Proof. intros m A cs cs' H Hwf E. apply (rw_cells_relist m A cs cs' H Hwf). apply map_unsigned_inj. exact E. Qed.

Lemma wr_at_app2 : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
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

Lemma rw_cells_app2 : forall m A cs1 cs2,
rw_cells bsegs m A (cs1 ++ cs2) <-> rw_cells bsegs m A cs1 /\ rw_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app2 by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma split_repeat_cb : forall m A n k (z : byte),
rw_cells bsegs m A [CB (Z.to_nat n) (repeat z (Z.to_nat n))] -> 0 <= k <= n ->
rw_cells bsegs m A [CB (Z.to_nat k) (repeat z (Z.to_nat k))] /\ u8arr bsegs m (A + k) (repeat z (Z.to_nat (n - k))).
Proof.
intros m A n k z H Hk.
apply (rw_cells_relist _ _ _ ([CB (Z.to_nat k) (repeat z (Z.to_nat k))] ++ [CB (Z.to_nat (n - k)) (repeat z (Z.to_nat (n - k)))])) in H.
- apply rw_cells_app2 in H. destruct H as [H1 H2]. split; [exact H1|].
cbn [cells_size csize] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia. exact (u8arr_of_rw_cells _ _ _ _ _ H2).
- cbn [cells_wf app cell_wf]. rewrite !repeat_length. repeat split; reflexivity || exact I.
- cbn [cells_bytes app cbytes]. rewrite !app_nil_r, <- repeat_app, <- Z2Nat.inj_add by lia.
replace (k + (n - k)) with n by lia. reflexivity.
Qed.

Definition ia_state (b : bool) (m : mem) : Prop :=
if b then
rw_cells bsegs m g_ia_word [C4 (Z_to_bv 64 1)]
/\ u8arr bsegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))
else
rw_cells bsegs m g_ia_word [C4 (Z_to_bv 64 0)]
/\ (exists j, rw_cells bsegs m IAP [C1 j])
/\ (exists bs, Z.of_nat (length bs) = 0x40000 /\ u8arr bsegs m (IAP + 8) bs)
/\ (exists bs, Z.of_nat (length bs) = 0xd80 /\ u8arr bsegs m (IAP + 0x40040) bs)
/\ (exists bs, Z.of_nat (length bs) = 0x40248 /\ u8arr bsegs m (IAP + 0x40dc0) bs)
/\ (exists j, rw_cells bsegs m (IAP + 0x81008) [CB 40 j])
/\ rw_cells bsegs m 0xfc0f8 [C8 (Z_to_bv 64 0x195560)]
/\ rw_cells bsegs m 0x195560 [C8 (Z_to_bv 64 4096)].

Definition ia_W (usp : Z) : list (Z * Z) := [(usp - 48, usp); (g_ia_word, g_ia_word + 4); (IAP, IAP + 0x81030)].

Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 IAP) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
/\ munch (ia_W (bv_unsigned sp)) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ ia_state true m'.

Lemma intalloc_fast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
ia_state true m ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x65b000 <= lo ->
mem_inv bsegs m ->
evt bsegs (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros IS ST LO ILO MI.
destruct IS as (W & MAP).
unfold g_ia_word, intalloc_entry, IAP in *.
assert (LMAP : Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))) = 0x40000) by (rewrite repeat_length; lia).
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold ia_W, g_ia_word, IAP in MU.
carve_frame 48%nat ST.
apply (rw_cells_relist _ _ _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
[| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
do 11 zstep. ifT.
do 8 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
finish.
unfold ia_state, g_ia_word, IAP.
split; [eapply rw_cells_relist; [exact W | vm_compute; repeat split; reflexivity | vm_compute; reflexivity]| exact MAP].
Qed.

Lemma intalloc_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
ia_state false m ->
stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x65b000 <= lo ->
mem_inv bsegs m ->
evt bsegs (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom bsegs)).
Proof.
intros until lo. intros IS ST LO ILO MI.
destruct IS as (W & (j0 & P0) & (j1 & LMAP & MAP) & (j2 & LINFO & INFO) & (j3 & LSEC & SEC) & (j4 & STATS) & GOT & PS).
unfold g_ia_word, intalloc_entry, IAP in *.
replace (1076416 + 8) with 1076424 in MAP by reflexivity. replace (1076416 + 262208) with 1338624 in INFO by reflexivity.
replace (1076416 + 265664) with 1342080 in SEC by reflexivity. replace (1076416 + 528392) with 1604808 in STATS by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold ia_W, g_ia_word, IAP in MU.
apply (rw_cells_relist _ _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
[| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
carve_frame 48%nat ST.
do 11 zstep. ifF.
do 8 zstep.
apply (rw_cells_relist _ _ _ [C4 (Z_to_bv 64 0)]) in W; [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
assert (AMO : amo_aligned AW (Z_to_bv 64 1660232) = true) by (vm_compute; reflexivity).
amo_step AMO.
change (sx32 z64) with (Z_to_bv 64 0).
do 4 zstep.
amo_step AMO; try fix_lit_store.
zstep. ifF.
do 3 zstep. ifF.
apply (rw_cells_relistZ _ _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
[| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
do 2 zstep. ifF.
do 8 zstep.
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1604808 0 40 j4).
all: try assumption; try lia.
rename POST into STATS2.
lstep.
do 5 zstep.
assert (EL1 : length j1 = Z.to_nat 262144) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LMAP).
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1076424 0 262144 j1).
1:{ rewrite <- EL1. apply rw_cells_of_u8arr. exact MAP. }
all: try assumption; try lia.
apply u8arr_of_rw_cells in POST. rename POST into MAP2.
assert (LMAP2 : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 262144))) = 262144) by (rewrite repeat_length; lia).
clear EL1 LMAP.
do 6 zstep.
assert (EL2 : length j2 = Z.to_nat 3456) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LINFO).
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1338624 0 3456 j2).
1:{ rewrite <- EL2. apply rw_cells_of_u8arr. exact INFO. }
all: try assumption; try lia.
apply u8arr_of_rw_cells in POST. rename POST into INFO2.
assert (LINFO2 : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 3456))) = 3456) by (rewrite repeat_length; lia).
clear EL2 LINFO.
do 6 zstep.
assert (EL3 : length j3 = Z.to_nat 262728) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LSEC).
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1342080 0 262728 j3).
1:{ rewrite <- EL3. apply rw_cells_of_u8arr. exact SEC. }
all: try assumption; try lia.
destruct (split_repeat_cb _ _ _ 16 _ POST ltac:(lia)) as [SEC16 SECR]. clear POST.
change (Z.to_nat 16) with 16%nat in SEC16. change (Z.to_nat (262728 - 16)) with (Z.to_nat 262712) in SECR.
assert (LSECR : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 262712))) = 262712) by (rewrite repeat_length; lia).
clear EL3 LSEC.
do 4 zstep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by (vm_compute; reflexivity) end.
cbv iota.
do 4 zstep. lstep. lstep.
zstep. lstep. zstep. lstep.
do 8 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
finish.
unfold ia_state, g_ia_word, IAP. split.
- eapply rw_cells_relistZ; [exact W | vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
- exact MAP2.
Qed.

Lemma skipn_repeat' : forall {X} (z : X) n k, skipn k (repeat z n) = repeat z (n - k).
Proof. intros X z n. induction n as [|n IH]; intros [|k]; cbn; auto. Qed.
Lemma firstn_repeat' : forall {X} (z : X) n k, firstn k (repeat z n) = repeat z (Nat.min k n).
Proof. intros X z n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma zero_run_read8 : forall m A N i,
u8arr bsegs m A (repeat (Z_to_bv 8 0) (Z.to_nat N)) -> 0 <= i -> i + 8 <= N ->
ov_read_bytes bsegs m (wa (A + i)) 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
intros m A N i [HB _] Hi HN.
rewrite (bytes_at_read bsegs m A _ i 8 HB Hi) by (rewrite repeat_length; lia).
f_equal. rewrite skipn_repeat', firstn_repeat'. f_equal. lia.
Qed.

Lemma pim_spec : forall (Q : machine_state -> Prop) (m : mem) (p : Z)
ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
0 <= p < 2 ^ 47 ->
u8arr bsegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000)) -> mem_inv bsegs m ->
(forall a1' a2' a3', evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 IAP) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x6806c) fc None m (seg_rom bsegs))) ->
evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 IAP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x67fc8) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros HP MAP MI K. unfold IAP in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (E47 : Z.shiftr p 47 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
zstep. rewrite E47. zstep. ifF.
assert (HQ : 0 <= Z.shiftr p 32 < 32768).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
do 3 zstep.
assert (SH3 : (p ≫ 32) ≪ 3 = 8 * (p ≫ 32)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite SH3.
pose proof (zero_run_read8 m (1076416 + 8) 262144 (8 * (p ≫ 32)) MAP ltac:(lia) ltac:(lia)) as RD.
replace (1076416 + 8 + 8 * (p ≫ 32)) with (1076416 + 8 * (p ≫ 32) + 8) in RD by lia.
zstep. change (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0).
zstep. zstep. ifT.
apply K.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac addr_near k ::=
let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 512))%Z in
lazymatch inb with true => idtac end.

Definition intalloc_entry : Z := 0x73f2c.
Definition IAP : Z := 0xfe480.
Definition g_ia_word : Z := 0x18cd08.

Lemma rw_cells_relist : forall m A cs cs',
rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
intros m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'| rewrite E; exact Hb]|].
rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hxy Hl. f_equal; [apply bv_eq; exact Hxy| apply IH; exact Hl].
Qed.

Lemma rw_cells_relistZ : forall m A cs cs',
rw_cells asegs m A cs -> cells_wf cs' ->
map (@bv_unsigned 8) (cells_bytes cs') = map (@bv_unsigned 8) (cells_bytes cs) -> rw_cells asegs m A cs'.
Proof. intros m A cs cs' H Hwf E. apply (rw_cells_relist m A cs cs' H Hwf). apply map_unsigned_inj. exact E. Qed.

Lemma wr_at_app2 : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
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

Lemma rw_cells_app2 : forall m A cs1 cs2,
rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app2 by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma split_repeat_cb : forall m A n k (z : byte),
rw_cells asegs m A [CB (Z.to_nat n) (repeat z (Z.to_nat n))] -> 0 <= k <= n ->
rw_cells asegs m A [CB (Z.to_nat k) (repeat z (Z.to_nat k))] /\ u8arr asegs m (A + k) (repeat z (Z.to_nat (n - k))).
Proof.
intros m A n k z H Hk.
apply (rw_cells_relist _ _ _ ([CB (Z.to_nat k) (repeat z (Z.to_nat k))] ++ [CB (Z.to_nat (n - k)) (repeat z (Z.to_nat (n - k)))])) in H.
- apply rw_cells_app2 in H. destruct H as [H1 H2]. split; [exact H1|].
cbn [cells_size csize] in H2. rewrite Nat.add_0_r, Z2Nat.id in H2 by lia. exact (u8arr_of_rw_cells _ _ _ _ _ H2).
- cbn [cells_wf app cell_wf]. rewrite !repeat_length. repeat split; reflexivity || exact I.
- cbn [cells_bytes app cbytes]. rewrite !app_nil_r, <- repeat_app, <- Z2Nat.inj_add by lia.
replace (k + (n - k)) with n by lia. reflexivity.
Qed.

Definition ia_state (b : bool) (m : mem) : Prop :=
if b then
rw_cells asegs m g_ia_word [C4 (Z_to_bv 64 1)]
/\ u8arr asegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))
else
rw_cells asegs m g_ia_word [C4 (Z_to_bv 64 0)]
/\ (exists j, rw_cells asegs m IAP [C1 j])
/\ (exists bs, Z.of_nat (length bs) = 0x40000 /\ u8arr asegs m (IAP + 8) bs)
/\ (exists bs, Z.of_nat (length bs) = 0xd80 /\ u8arr asegs m (IAP + 0x40040) bs)
/\ (exists bs, Z.of_nat (length bs) = 0x40248 /\ u8arr asegs m (IAP + 0x40dc0) bs)
/\ (exists j, rw_cells asegs m (IAP + 0x81008) [CB 40 j])
/\ rw_cells asegs m 0xf3878 [C8 (Z_to_bv 64 0x18cd20)]
/\ rw_cells asegs m 0x18cd20 [C8 (Z_to_bv 64 4096)].

Definition ia_W (usp : Z) : list (Z * Z) := [(usp - 48, usp); (g_ia_word, g_ia_word + 4); (IAP, IAP + 0x81030)].

Definition ia_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 IAP) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch (ia_W (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ ia_state true m'.

Lemma intalloc_fast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
ia_state true m ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x652000 <= lo ->
mem_inv asegs m ->
evt asegs (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros IS ST LO ILO MI.
destruct IS as (W & MAP).
unfold g_ia_word, intalloc_entry, IAP in *.
assert (LMAP : Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000))) = 0x40000) by (rewrite repeat_length; lia).
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ia_W, g_ia_word, IAP in MU.
carve_frame 48%nat ST.
apply (rw_cells_relist _ _ _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
[| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
do 11 zstep. ifT.
do 8 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
finish.
unfold ia_state, g_ia_word, IAP.
split; [eapply rw_cells_relist; [exact W | vm_compute; repeat split; reflexivity | vm_compute; reflexivity]| exact MAP].
Qed.

Lemma intalloc_init_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (lo : Z),
ia_state false m ->
stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> 0x652000 <= lo ->
mem_inv asegs m ->
evt asegs (ia_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 intalloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros IS ST LO ILO MI.
destruct IS as (W & (j0 & P0) & (j1 & LMAP & MAP) & (j2 & LINFO & INFO) & (j3 & LSEC & SEC) & (j4 & STATS) & GOT & PS).
unfold g_ia_word, intalloc_entry, IAP in *.
replace (1041536 + 8) with 1041544 in MAP by reflexivity. replace (1041536 + 262208) with 1303744 in INFO by reflexivity.
replace (1041536 + 265664) with 1307200 in SEC by reflexivity. replace (1041536 + 528392) with 1569928 in STATS by reflexivity.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (munch_refl (ia_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold ia_W, g_ia_word, IAP in MU.
apply (rw_cells_relist _ _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
[| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
carve_frame 48%nat ST.
do 11 zstep. ifF.
do 8 zstep.
apply (rw_cells_relist _ _ _ [C4 (Z_to_bv 64 0)]) in W; [| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
assert (AMO : amo_aligned AW (Z_to_bv 64 1625352) = true) by (vm_compute; reflexivity).
amo_step AMO.
change (sx32 z64) with (Z_to_bv 64 0).
do 4 zstep.
amo_step AMO; try fix_lit_store.
zstep. ifF.
do 3 zstep. ifF.
apply (rw_cells_relistZ _ _ _ [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); CB 2 [Z_to_bv 8 0; Z_to_bv 8 0]]) in W;
[| vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
do 2 zstep. ifF.
do 8 zstep.
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1569928 0 40 j4).
all: try assumption; try lia.
rename POST into STATS2.
lstep.
do 5 zstep.
assert (EL1 : length j1 = Z.to_nat 262144) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LMAP).
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1041544 0 262144 j1).
1:{ rewrite <- EL1. apply rw_cells_of_u8arr. exact MAP. }
all: try assumption; try lia.
apply u8arr_of_rw_cells in POST. rename POST into MAP2.
assert (LMAP2 : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 262144))) = 262144) by (rewrite repeat_length; lia).
clear EL1 LMAP.
do 6 zstep.
assert (EL2 : length j2 = Z.to_nat 3456) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LINFO).
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1303744 0 3456 j2).
1:{ rewrite <- EL2. apply rw_cells_of_u8arr. exact INFO. }
all: try assumption; try lia.
apply u8arr_of_rw_cells in POST. rename POST into INFO2.
assert (LINFO2 : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 3456))) = 3456) by (rewrite repeat_length; lia).
clear EL2 LINFO.
do 6 zstep.
assert (EL3 : length j3 = Z.to_nat 262728) by (apply Nat2Z.inj; rewrite Z2Nat.id by lia; exact LSEC).
call (imemset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 1307200 0 262728 j3).
1:{ rewrite <- EL3. apply rw_cells_of_u8arr. exact SEC. }
all: try assumption; try lia.
destruct (split_repeat_cb _ _ _ 16 _ POST ltac:(lia)) as [SEC16 SECR]. clear POST.
change (Z.to_nat 16) with 16%nat in SEC16. change (Z.to_nat (262728 - 16)) with (Z.to_nat 262712) in SECR.
assert (LSECR : Z.of_nat (length (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 262712))) = 262712) by (rewrite repeat_length; lia).
clear EL3 LSEC.
do 4 zstep.
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true by (vm_compute; reflexivity) end.
cbv iota.
do 4 zstep. lstep. lstep.
zstep. lstep. zstep. lstep.
do 8 zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
finish.
unfold ia_state, g_ia_word, IAP. split.
- eapply rw_cells_relistZ; [exact W | vm_compute; repeat split; reflexivity | vm_compute; reflexivity].
- exact MAP2.
Qed.

Lemma skipn_repeat' : forall {X} (z : X) n k, skipn k (repeat z n) = repeat z (n - k).
Proof. intros X z n. induction n as [|n IH]; intros [|k]; cbn; auto. Qed.
Lemma firstn_repeat' : forall {X} (z : X) n k, firstn k (repeat z n) = repeat z (Nat.min k n).
Proof. intros X z n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma zero_run_read8 : forall m A N i,
u8arr asegs m A (repeat (Z_to_bv 8 0) (Z.to_nat N)) -> 0 <= i -> i + 8 <= N ->
ov_read_bytes asegs m (wa (A + i)) 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
intros m A N i [HB _] Hi HN.
rewrite (bytes_at_read asegs m A _ i 8 HB Hi) by (rewrite repeat_length; lia).
f_equal. rewrite skipn_repeat', firstn_repeat'. f_equal. lia.
Qed.

Lemma pim_spec : forall (Q : machine_state -> Prop) (m : mem) (p : Z)
ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
0 <= p < 2 ^ 47 ->
u8arr asegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000)) -> mem_inv asegs m ->
(forall a1' a2' a3', evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 IAP) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x67f80) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p) (Z_to_bv 64 IAP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x67edc) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros HP MAP MI K. unfold IAP in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (E47 : Z.shiftr p 47 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
zstep. rewrite E47. zstep. ifF.
assert (HQ : 0 <= Z.shiftr p 32 < 32768).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
do 3 zstep.
assert (SH3 : (p ≫ 32) ≪ 3 = 8 * (p ≫ 32)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite SH3.
pose proof (zero_run_read8 m (1041536 + 8) 262144 (8 * (p ≫ 32)) MAP ltac:(lia) ltac:(lia)) as RD.
replace (1041536 + 8 + 8 * (p ≫ 32)) with (1041536 + 8 * (p ≫ 32) + 8) in RD by lia.
zstep. change (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0).
zstep. zstep. ifT.
apply K.
Qed.
