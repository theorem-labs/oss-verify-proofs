(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from cgif_file_fuzzer lib/A/AE2q.v with AE6k.v (mc_tail, section l), AE6l.v-AE6s.v and AE3c.v (section f) for libreac/fuzz_disco's __asan_memcpy called with the source equal to the destination: x = d in place of the disjointness premise, the branch at 0x520e0 taken past the overlap check, the musl memcpy source read through the bytes it has already written (src_read, rdn_bytes1); module paths; addresses. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AB1w.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AE3c.
Import ListNotations.
#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Module C.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable bs : list byte.
Variables d s : word.
Variables mem rom : word -> option byte.
Definition D : Z := bv_unsigned d.
Definition S : Z := bv_unsigned s.
Hypothesis Hsrc : rdn tfibsegs mem s (length bs) = Some bs.
Hypothesis Hdst : store_ok tfibsegs mem d (length bs) = true.
Hypothesis Hnd : bv_unsigned d + Z.of_nat (length bs) <= 2^64.
Hypothesis Hns : bv_unsigned s + Z.of_nat (length bs) <= 2^64.
Hypothesis Hsame : s = d.
Hypothesis Hsmall : bv_unsigned d + Z.of_nat (length bs) < 2^64.
Definition M (i : nat) : word -> option byte := wbytes mem d (firstn i bs).
Definition chunk (i k : nat) : list byte := firstn k (skipn i bs).
Lemma DS_facts : D = bv_unsigned d /\ S = bv_unsigned s /\ 0 <= bv_unsigned d < 2^64 /\ 0 <= bv_unsigned s < 2^64.
Proof. pose proof (u64_range d). pose proof (u64_range s). unfold D, S. lia. Qed.
Ltac dsl := pose proof DS_facts as HDS; destruct HDS as (HD_ & HS_ & HDr & HSr).
Lemma chunk_len : forall i k, (i + k <= length bs)%nat -> length (chunk i k) = k.
Proof. intros i k H. unfold chunk. rewrite length_firstn, length_skipn. lia. Qed.
Lemma chunk1 : forall i, (i < length bs)%nat -> chunk i 1 = [nth i bs NUL].
Proof. intros i Hi. unfold chunk. rewrite (skipn_nth bs i NUL Hi). reflexivity. Qed.
Lemma nth_firstn' : forall {A} (l : list A) k j (x : A), (j < k)%nat -> nth j (firstn k l) x = nth j l x.
Proof.
intros A l k; revert l. induction k as [|k IH]; intros l j x Hj; [lia|].
destruct l as [|a l]; [destruct j; reflexivity|].
destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.
Lemma nth_chunk : forall i k j, (j < k)%nat ->
nth j (chunk i k) NUL = nth (i + j) bs NUL.
Proof.
intros i k j Hj. unfold chunk. rewrite nth_firstn' by exact Hj.
rewrite nth_skipn. reflexivity.
Qed.
Lemma chunk_shift : forall i p, (p <= 4)%nat ->
chunk (i + p) 4 = skipn p (chunk i 4) ++ firstn p (chunk (i + 4) 4).
Proof.
intros i p Hp. unfold chunk.
rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
replace (Init.Nat.min p 4) with p by lia.
rewrite (Nat.add_comm p i).
replace (firstn 4 (skipn (i + p) bs)) with (firstn (4 - p + p) (skipn (i + p) bs)) by (f_equal; lia).
rewrite <- (firstn_app_firstn_skipn (skipn (i + p) bs) (4 - p) p).
rewrite skipn_skipn. replace (4 - p + (i + p))%nat with (i + 4)%nat by lia.
reflexivity.
Qed.
Lemma src_read : forall j i k, (0 < k)%nat -> (i + k <= length bs)%nat ->
rdn tfibsegs (M j) (Z_to_bv 64 (S + Z.of_nat i)) k = Some (chunk i k).
Proof.
intros j i k Hk Hik. dsl.
assert (HSD : S = D) by (unfold S, D; rewrite Hsame; reflexivity).
assert (FULL : rdn tfibsegs (M j) d (length bs) = Some bs).
{ unfold M. destruct (Nat.lt_ge_cases j (length bs)) as [Hj|Hj].
- transitivity (Some (firstn j bs ++ skipn j bs)); [|rewrite firstn_skipn; reflexivity].
replace (length bs) with (j + (length bs - j))%nat by lia.
apply rdn_app.
+ pose proof (rdn_wbytes_hit tfibsegs (firstn j bs) mem d ltac:(rewrite length_firstn; lia)) as Hh.
rewrite length_firstn in Hh. replace (Init.Nat.min j (length bs)) with j in Hh by lia. exact Hh.
+ rewrite rdn_wbytes_disjoint by (rewrite ?length_firstn, ?word_add_nat; rewrite ?u_Z2bv by lia; lia).
rewrite <- Hsame. apply rdn_skipn; [exact Hsrc | lia].
- rewrite firstn_all2 by lia. apply rdn_wbytes_hit. exact Hnd. }
replace (Z_to_bv 64 (S + Z.of_nat i)) with (d + nat_to_word i)%bv by (rewrite word_add_nat; f_equal; lia).
unfold chunk. exact (rdn_sub tfibsegs (M j) d (length bs) bs i k FULL Hik).
Qed.
Lemma src_read1 : forall j a i, a = S + Z.of_nat i -> (i < length bs)%nat ->
rdn tfibsegs (M j) (Z_to_bv 64 a) 1 = Some [nth i bs NUL].
Proof. intros j a i -> Hi. rewrite <- chunk1 by exact Hi. apply src_read; lia. Qed.
Lemma src_read4 : forall j a i, a = S + Z.of_nat i -> (i + 4 <= length bs)%nat ->
rdn tfibsegs (M j) (Z_to_bv 64 a) 4 = Some (chunk i 4).
Proof. intros j a i -> Hi. apply src_read; lia. Qed.
Lemma dst_ok : forall j a i k, a = D + Z.of_nat i -> (0 < k)%nat -> (i + k <= length bs)%nat ->
store_ok tfibsegs (M j) (Z_to_bv 64 a) k = true.
Proof.
intros j a i k -> Hk Hik. dsl. unfold M.
eapply store_ok_mono; [apply wbytes_grows|].
eapply (store_ok_sub tfibsegs mem d _ (length bs)); [exact Hnd | exact Hdst | |];
rewrite u_Z2bv by lia; lia.
Qed.
Lemma M_app : forall i k, (i + k <= length bs)%nat ->
wbytes (M i) (Z_to_bv 64 (D + Z.of_nat i)) (chunk i k) = M (i + k).
Proof.
intros i k Hik. dsl. unfold M, chunk.
rewrite <- firstn_app_firstn_skipn, wbytes_app. f_equal.
rewrite word_add_nat, length_firstn. f_equal. lia.
Qed.
Lemma M_app1 : forall j a b, a = D + Z.of_nat j -> b = nth j bs NUL -> (j < length bs)%nat ->
wbytes (M j) (Z_to_bv 64 a) [b] = M (Datatypes.S j).
Proof.
intros j a b -> -> Hj. rewrite <- chunk1, M_app by lia. f_equal. lia.
Qed.
Lemma M_app4 : forall j a l, a = D + Z.of_nat j -> l = chunk j 4 -> (j + 4 <= length bs)%nat ->
wbytes (M j) (Z_to_bv 64 a) l = M (j + 4).
Proof. intros j a l -> -> Hj. apply M_app. exact Hj. Qed.
Lemma M_full : forall i, (length bs <= i)%nat -> M i = wbytes mem d bs.
Proof. intros i Hi. unfold M. rewrite firstn_all2 by exact Hi. reflexivity. Qed.
Definition keep (r : reg) : Prop :=
r <> 5%bv /\ r <> 6%bv /\ r <> 7%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv
/\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 28%bv.
Definition fin (regs : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
exists regs',
msteps tfibsegs (mkst regs pc m rom) (mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ forall r, keep r -> getr regs' r = getr regs r.
Lemma keep_1 : keep 1.
Proof. unfold keep. repeat split; reg_neq_tac. Qed.
Lemma fin_steps : forall regs pc m regs2 pc2 m2,
msteps tfibsegs (mkst regs pc m rom) (mkst regs2 pc2 m2 rom) ->
(forall r, keep r -> getr regs2 r = getr regs r) ->
fin regs2 pc2 m2 -> fin regs pc m.
Proof.
intros regs pc m regs2 pc2 m2 Hms Hfr (regs' & Hms' & Hfr').
exists regs'. split.
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keep_1). exact Hms'.
- intros r Hr. rewrite (Hfr' r Hr). apply Hfr. exact Hr.
Qed.
Lemma fin_done : forall regs t m,
t = v_jalr (getr regs 1) 0 -> m = wbytes mem d bs -> fin regs t m.
Proof. intros regs t m -> ->. exists regs. split; [apply mst_refl| intros; reflexivity]. Qed.
Lemma fin_pc : forall regs (pc pc' : word) m,
bv_unsigned pc = bv_unsigned pc' -> fin regs pc' m -> fin regs pc m.
Proof. intros regs pc pc' m H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let r := fresh "r" in let Hr := fresh "Hkeep" in
intros r Hr; unfold keep in Hr;
destruct Hr as (?&?&?&?&?&?&?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_apply L :=
eapply fin_pc; [ | eapply L ]; [ vm_compute; reflexivity | .. ].
Ltac rg := gr; rwH; first [ reflexivity | f_equal; lia ].
Ltac steplbu F0 D idx := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D
| gr; rwH; imm_norm; rewrite ?v_addi_lit; apply (src_read1 _ _ idx); lia ]
| step_simpl ].
Ltac steplw F0 D idx := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lw_l; [ exact F | reflexivity | exact D
| gr; rwH; imm_norm; rewrite ?v_addi_lit; apply (src_read4 _ _ idx); lia ]
| step_simpl ].
Ltac sbval :=
gr; rwH;
first [ apply sb_lbu
| rewrite sb_lwv_l by (apply chunk_len; lia); rewrite nth_chunk by lia; reflexivity
| rewrite sb_lwv_sr8_l by (apply chunk_len; lia); rewrite nth_chunk by lia; reflexivity
| rewrite sb_lwv_sr16_l by (apply chunk_len; lia); rewrite nth_chunk by lia; reflexivity ].
Ltac swval :=
gr; rwH;
first [ rewrite sw_lwv_l by (apply chunk_len; lia); first [reflexivity | f_equal; lia]
| rewrite ?sw_merge8_l, ?sw_merge16_l, ?sw_merge24_l by (apply chunk_len; lia);
lazymatch goal with
| |- skipn ?p (chunk ?o 4) ++ firstn _ (chunk ?o4 4) = chunk ?j 4 =>
replace j with (o + p)%nat by lia; replace o4 with (o + 4)%nat by lia;
symmetry; apply chunk_shift; lia
end ].
Ltac stepsb HF0 HD := let HF := litF HF0 in
lazymatch goal with
| |- msteps _ (mkst _ _ (M ?j) _) _ =>
chain_step;
[ reflexivity
| eapply step_sb_l with (a := D + Z.of_nat j);
[ exact HF | reflexivity | exact HD | val | sbval | apply (dst_ok j _ j 1); [lia|lia|lia] ]
| step_simpl; rewrite M_app1 by first [lia | f_equal; lia] ]
end.
Ltac stepsw HF0 HD := let HF := litF HF0 in
lazymatch goal with
| |- msteps _ (mkst _ _ (M ?j) _) _ =>
chain_step;
[ reflexivity
| eapply step_sw_l with (a := D + Z.of_nat j) (l := chunk j 4);
[ exact HF | reflexivity | exact HD | val | swval | apply (dst_ok j _ j 4); [lia|lia|lia] ]
| step_simpl; rewrite M_app4 by first [lia | f_equal; lia] ]
end.
Ltac finish_ret :=
lazymatch goal with
| |- msteps _ _ _ => apply mst_refl
end.
Lemma tail_3f0 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 4 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x3c0)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod4_split m) as E4. pose proof (mod2_split m) as E2.
assert (Hm2 : 0 <= m mod 2 < 2) by (apply Z.mod_pos_bound; lia).
destruct (land2_cases m) as [L2|L2]; destruct (land1_cases m) as [L1|L1].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbf F_3c4 D_3c4.
sv F_3c8 D_3c8 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbf F_3cc D_3cc.
stepret F_3d0 D_3d0.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbf F_3c4 D_3c4.
sv F_3c8 D_3c8 (Z_to_bv 64 1); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbt F_3cc D_3cc.
steplbu F_3f8 D_3f8 i.
stepsb F_3fc D_3fc.
stepret F_400 D_400.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 2); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbt F_3c4 D_3c4.
steplbu F_3d4 D_3d4 i.
steplbu F_3d8 D_3d8 (i + 1)%nat.
sv F_3dc D_3dc (Z_to_bv 64 (S + Z.of_nat i + 2)).
sv F_3e0 D_3e0 (Z_to_bv 64 (D + Z.of_nat i + 2)).
stepsb F_3e4 D_3e4.
stepsb F_3e8 D_3e8.
sv F_3ec D_3ec (Z_to_bv 64 (D + Z.of_nat i + 2)).
sv F_3f0 D_3f0 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbt F_3f4 D_3f4.
stepret F_3d0 D_3d0.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 2); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbt F_3c4 D_3c4.
steplbu F_3d4 D_3d4 i.
steplbu F_3d8 D_3d8 (i + 1)%nat.
sv F_3dc D_3dc (Z_to_bv 64 (S + Z.of_nat i + 2)).
sv F_3e0 D_3e0 (Z_to_bv 64 (D + Z.of_nat i + 2)).
stepsb F_3e4 D_3e4.
stepsb F_3e8 D_3e8.
sv F_3ec D_3ec (Z_to_bv 64 (D + Z.of_nat i + 2)).
sv F_3f0 D_3f0 (Z_to_bv 64 1); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbf F_3f4 D_3f4.
steplbu F_3f8 D_3f8 (i + 2)%nat.
stepsb F_3fc D_3fc.
stepret F_400 D_400.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
Qed.
Lemma tail_3c4 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + 4 + m mod 4 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x394)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hm4 : 0 <= m mod 4 < 4) by (apply Z.mod_pos_bound; lia).
eapply fin_steps.
- norm_pc.
steplbu F_394 D_394 i.
steplbu F_398 D_398 (i + 1)%nat.
steplbu F_39c D_39c (i + 2)%nat.
steplbu F_3a0 D_3a0 (i + 3)%nat.
sv F_3a4 D_3a4 (Z_to_bv 64 (S + Z.of_nat i + 4)).
sv F_3a8 D_3a8 (Z_to_bv 64 (D + Z.of_nat i + 4)).
stepsb F_3ac D_3ac.
stepsb F_3b0 D_3b0.
stepsb F_3b4 D_3b4.
stepsb F_3b8 D_3b8.
sv F_3bc D_3bc (Z_to_bv 64 (D + Z.of_nat i + 4)).
apply mst_refl.
- frame.
- fin_apply tail_3f0; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma test_098 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 8 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x68)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod8_split m) as E8.
destruct (land4_cases m) as [L4|L4].
- eapply fin_steps.
+ norm_pc.
sv F_068 D_068 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbf F_06c D_06c.
stepj' F_070 D_070.
apply mst_refl.
+ frame.
+ fin_apply tail_3f0; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_068 D_068 (Z_to_bv 64 4); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbt F_06c D_06c.
apply mst_refl.
+ frame.
+ fin_apply tail_3c4; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
Qed.
Lemma tail_370 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + 8 + m mod 8 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x340)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hm8 : 0 <= m mod 8 < 8) by (apply Z.mod_pos_bound; lia).
pose proof (mod8_split m) as E8.
eapply fin_steps.
- norm_pc.
steplbu F_340 D_340 i.
steplbu F_344 D_344 (i + 1)%nat.
steplbu F_348 D_348 (i + 2)%nat.
steplbu F_34c D_34c (i + 3)%nat.
steplbu F_350 D_350 (i + 4)%nat.
steplbu F_354 D_354 (i + 5)%nat.
steplbu F_358 D_358 (i + 6)%nat.
steplbu F_35c D_35c (i + 7)%nat.
sv F_360 D_360 (Z_to_bv 64 (S + Z.of_nat i + 8)).
stepsb F_364 D_364.
stepsb F_368 D_368.
stepsb F_36c D_36c.
stepsb F_370 D_370.
sv F_374 D_374 (Z_to_bv 64 (D + Z.of_nat i + 8)).
stepsb F_378 D_378.
stepsb F_37c D_37c.
stepsb F_380 D_380.
stepsb F_384 D_384.
sv F_388 D_388 (Z_to_bv 64 (D + Z.of_nat i + 8)).
apply mst_refl.
- frame.
- destruct (land4_cases m) as [L4|L4].
+ eapply fin_steps.
* norm_pc.
sv F_38c D_38c (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbt F_390 D_390.
apply mst_refl.
* frame.
* fin_apply tail_3f0; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_38c D_38c (Z_to_bv 64 4); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbf F_390 D_390.
apply mst_refl.
* frame.
* fin_apply tail_3c4; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma test_090 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 16 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x60)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod16_split m) as E16.
destruct (land8_cases m) as [L8|L8].
- eapply fin_steps.
+ norm_pc.
sv F_060 D_060 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbf F_064 D_064.
apply mst_refl.
+ frame.
+ fin_apply test_098; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_060 D_060 (Z_to_bv 64 8); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbt F_064 D_064.
apply mst_refl.
+ frame.
+ fin_apply tail_370; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
Qed.
Lemma tail_2dc : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + 16 + m mod 16 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x2ac)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hm16 : 0 <= m mod 16 < 16) by (apply Z.mod_pos_bound; lia).
pose proof (mod16_split m) as E16.
eapply fin_steps.
- norm_pc.
steplbu F_2ac D_2ac i.
steplbu F_2b0 D_2b0 (i + 1)%nat.
steplbu F_2b4 D_2b4 (i + 2)%nat.
steplbu F_2b8 D_2b8 (i + 3)%nat.
steplbu F_2bc D_2bc (i + 4)%nat.
steplbu F_2c0 D_2c0 (i + 5)%nat.
steplbu F_2c4 D_2c4 (i + 6)%nat.
steplbu F_2c8 D_2c8 (i + 7)%nat.
stepsb F_2cc D_2cc.
stepsb F_2d0 D_2d0.
stepsb F_2d4 D_2d4.
stepsb F_2d8 D_2d8.
steplbu F_2dc D_2dc (i + 8)%nat.
steplbu F_2e0 D_2e0 (i + 9)%nat.
steplbu F_2e4 D_2e4 (i + 10)%nat.
steplbu F_2e8 D_2e8 (i + 11)%nat.
stepsb F_2ec D_2ec.
stepsb F_2f0 D_2f0.
stepsb F_2f4 D_2f4.
stepsb F_2f8 D_2f8.
steplbu F_2fc D_2fc (i + 12)%nat.
steplbu F_300 D_300 (i + 13)%nat.
steplbu F_304 D_304 (i + 14)%nat.
steplbu F_308 D_308 (i + 15)%nat.
sv F_30c D_30c (Z_to_bv 64 (S + Z.of_nat i + 16)).
stepsb F_310 D_310.
stepsb F_314 D_314.
stepsb F_318 D_318.
stepsb F_31c D_31c.
sv F_320 D_320 (Z_to_bv 64 (D + Z.of_nat i + 16)).
stepsb F_324 D_324.
stepsb F_328 D_328.
stepsb F_32c D_32c.
stepsb F_330 D_330.
sv F_334 D_334 (Z_to_bv 64 (D + Z.of_nat i + 16)).
apply mst_refl.
- frame.
- destruct (land8_cases m) as [L8|L8].
+ eapply fin_steps.
* norm_pc.
sv F_338 D_338 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbt F_33c D_33c.
apply mst_refl.
* frame.
* fin_apply test_098; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_338 D_338 (Z_to_bv 64 8); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbf F_33c D_33c.
apply mst_refl.
* frame.
* fin_apply tail_370; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma test_088 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 32 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x58)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
destruct (Z_lt_le_dec m 16) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc.
sv F_058 D_058 (Z_to_bv 64 16).
stepbf F_05c D_05c.
apply mst_refl.
+ frame.
+ fin_apply test_090; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia |].
rewrite Z.mod_small by lia. lia.
- eapply fin_steps.
+ norm_pc.
sv F_058 D_058 (Z_to_bv 64 16).
stepbt F_05c D_05c.
apply mst_refl.
+ frame.
+ fin_apply tail_2dc; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia |].
replace (m mod 16) with (m - 16); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma al_1ac : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 8 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x17c)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod8_split m) as E8.
assert (Hm4 : 0 <= m mod 4 < 4) by (apply Z.mod_pos_bound; lia).
destruct (land4_cases m) as [L4|L4].
- eapply fin_steps.
+ norm_pc.
sv F_17c D_17c (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbt F_180 D_180.
apply mst_refl.
+ frame.
+ fin_apply tail_3f0; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_17c D_17c (Z_to_bv 64 4); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbf F_180 D_180.
steplw F_184 D_184 i.
sv F_188 D_188 (Z_to_bv 64 (S + Z.of_nat i + 4)).
stepsw F_18c D_18c.
sv F_190 D_190 (Z_to_bv 64 (D + Z.of_nat i + 4)).
stepj' F_194 D_194.
apply mst_refl.
+ frame.
+ fin_apply tail_3f0; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma al_18c : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 16 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x15c)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
destruct (Z_lt_le_dec m 8) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc.
sv F_15c D_15c (Z_to_bv 64 8).
stepbt F_160 D_160.
apply mst_refl.
+ frame.
+ fin_apply al_1ac; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia |].
rewrite Z.mod_small by lia. lia.
- eapply fin_steps.
+ norm_pc.
sv F_15c D_15c (Z_to_bv 64 8).
stepbf F_160 D_160.
steplw F_164 D_164 i.
steplw F_168 D_168 (i + 4)%nat.
stepsw F_16c D_16c.
stepsw F_170 D_170.
sv F_174 D_174 (Z_to_bv 64 (D + Z.of_nat i + 8)).
sv F_178 D_178 (Z_to_bv 64 (S + Z.of_nat i + 8)).
apply mst_refl.
+ frame.
+ fin_apply al_1ac; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia |].
replace (m mod 8) with (m - 8); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma al_loop : forall k regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 14 = Z_to_bv 64 15 ->
16 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x12c)) (M i).
Proof.
induction k as [|k IH]; intros regs i m H11 H13 H12 H14 Hm Hk Hi; [lia|]. dsl.
eapply fin_steps.
- norm_pc.
steplw F_12c D_12c i.
steplw F_130 D_130 (i + 4)%nat.
steplw F_134 D_134 (i + 8)%nat.
steplw F_138 D_138 (i + 12)%nat.
sv F_13c D_13c (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_140 D_140 (Z_to_bv 64 (m - 16)).
stepsw F_144 D_144.
stepsw F_148 D_148.
stepsw F_14c D_14c.
stepsw F_150 D_150.
sv F_154 D_154 (Z_to_bv 64 (D + Z.of_nat i + 16)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 15 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_158 D_158. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | lia | lia | lia].
+ eapply fin_steps.
* norm_pc. stepbf F_158 D_158. apply mst_refl.
* frame.
* fin_apply al_18c; [gr; f_equal; lia | gr; f_equal; lia | gr; reflexivity | lia | lia].
Qed.
Lemma al_150 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x120)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
destruct (Z_lt_le_dec m 16) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc.
sv F_120 D_120 (Z_to_bv 64 16).
stepbt F_124 D_124.
apply mst_refl.
+ frame.
+ fin_apply al_18c; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_120 D_120 (Z_to_bv 64 16).
stepbf F_124 D_124.
sv F_128 D_128 (Z_to_bv 64 15).
apply mst_refl.
+ frame.
+ fin_apply (al_loop (Z.to_nat m)); [gr; exact H11 | gr; exact H13 | gr; exact H12 | gr; reflexivity | lia | lia | lia].
Qed.
Lemma sh_loop2 : forall k regs o j m,
getr regs 14 = lwv (chunk o 4) ->
getr regs 11 = Z_to_bv 64 (S + Z.of_nat o + 16) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 17 ->
(j = o + 2)%nat -> 18 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat j + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0xa4)) (M j).
Proof.
induction k as [|k IH]; intros regs o j m H14 H11 H13 H12 H15 Hj Hm Hk Hi; [lia|]. dsl. subst j.
eapply fin_steps.
- norm_pc.
svsrw F_0a4 D_0a4 (v_srliw (lwv (chunk o 4)) 16).
steplw F_0a8 D_0a8 (o + 4)%nat.
steplw F_0ac D_0ac (o + 8)%nat.
steplw F_0b0 D_0b0 (o + 12)%nat.
steplw F_0b4 D_0b4 (o + 16)%nat.
sv F_0b8 D_0b8 (v_slli (lwv (chunk (o + 4) 4)) 16).
svsrw F_0bc D_0bc (v_srliw (lwv (chunk (o + 4) 4)) 16).
svor F_0c0 D_0c0 (v_or (v_slli (lwv (chunk (o + 4) 4)) 16) (v_srliw (lwv (chunk o 4)) 16)).
sv F_0c4 D_0c4 (v_slli (lwv (chunk (o + 8) 4)) 16).
svsrw F_0c8 D_0c8 (v_srliw (lwv (chunk (o + 8) 4)) 16).
svor F_0cc D_0cc (v_or (v_slli (lwv (chunk (o + 8) 4)) 16) (v_srliw (lwv (chunk (o + 4) 4)) 16)).
sv F_0d0 D_0d0 (v_slli (lwv (chunk (o + 12) 4)) 16).
svsrw F_0d4 D_0d4 (v_srliw (lwv (chunk (o + 12) 4)) 16).
svor F_0d8 D_0d8 (v_or (v_slli (lwv (chunk (o + 12) 4)) 16) (v_srliw (lwv (chunk (o + 8) 4)) 16)).
sv F_0dc D_0dc (v_slli (lwv (chunk (o + 16) 4)) 16).
svor F_0e0 D_0e0 (v_or (v_slli (lwv (chunk (o + 16) 4)) 16) (v_srliw (lwv (chunk (o + 12) 4)) 16)).
sv F_0e4 D_0e4 (Z_to_bv 64 (m - 16)).
stepsw F_0e8 D_0e8.
stepsw F_0ec D_0ec.
stepsw F_0f0 D_0f0.
stepsw F_0f4 D_0f4.
sv F_0f8 D_0f8 (Z_to_bv 64 (D + Z.of_nat o + 18)).
sv F_0fc D_0fc (Z_to_bv 64 (S + Z.of_nat o + 32)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 17 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_100 D_100. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia | lia].
+ destruct (Z_lt_le_dec (m - 16) 16) as [Hl|Hh].
* eapply fin_steps.
-- norm_pc. stepbf F_100 D_100.
sv F_104 D_104 (Z_to_bv 64 (S + Z.of_nat o + 18)).
sv F_108 D_108 (Z_to_bv 64 16).
stepbt F_10c D_10c. apply mst_refl.
-- frame.
-- fin_apply test_090; [rg | rg | rg | lia | rewrite Z.mod_small by lia; lia].
* eapply fin_steps.
-- norm_pc. stepbf F_100 D_100.
sv F_104 D_104 (Z_to_bv 64 (S + Z.of_nat o + 18)).
sv F_108 D_108 (Z_to_bv 64 16).
stepbf F_10c D_10c.
stepj' F_110 D_110. apply mst_refl.
-- frame.
-- fin_apply tail_2dc; [rg | rg | rg | lia | ].
replace ((m - 16) mod 16) with (m - 32); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma sh_loop3 : forall k regs o j m,
getr regs 14 = lwv (chunk o 4) ->
getr regs 11 = Z_to_bv 64 (S + Z.of_nat o + 16) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 18 ->
(j = o + 1)%nat -> 19 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat j + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x1ac)) (M j).
Proof.
induction k as [|k IH]; intros regs o j m H14 H11 H13 H12 H15 Hj Hm Hk Hi; [lia|]. dsl. subst j.
eapply fin_steps.
- norm_pc.
svsrw F_1ac D_1ac (v_srliw (lwv (chunk o 4)) 8).
steplw F_1b0 D_1b0 (o + 4)%nat.
steplw F_1b4 D_1b4 (o + 8)%nat.
steplw F_1b8 D_1b8 (o + 12)%nat.
steplw F_1bc D_1bc (o + 16)%nat.
sv F_1c0 D_1c0 (v_slli (lwv (chunk (o + 4) 4)) 24).
svsrw F_1c4 D_1c4 (v_srliw (lwv (chunk (o + 4) 4)) 8).
svor F_1c8 D_1c8 (v_or (v_slli (lwv (chunk (o + 4) 4)) 24) (v_srliw (lwv (chunk o 4)) 8)).
sv F_1cc D_1cc (v_slli (lwv (chunk (o + 8) 4)) 24).
svsrw F_1d0 D_1d0 (v_srliw (lwv (chunk (o + 8) 4)) 8).
svor F_1d4 D_1d4 (v_or (v_slli (lwv (chunk (o + 8) 4)) 24) (v_srliw (lwv (chunk (o + 4) 4)) 8)).
sv F_1d8 D_1d8 (v_slli (lwv (chunk (o + 12) 4)) 24).
svsrw F_1dc D_1dc (v_srliw (lwv (chunk (o + 12) 4)) 8).
svor F_1e0 D_1e0 (v_or (v_slli (lwv (chunk (o + 12) 4)) 24) (v_srliw (lwv (chunk (o + 8) 4)) 8)).
sv F_1e4 D_1e4 (v_slli (lwv (chunk (o + 16) 4)) 24).
svor F_1e8 D_1e8 (v_or (v_slli (lwv (chunk (o + 16) 4)) 24) (v_srliw (lwv (chunk (o + 12) 4)) 8)).
sv F_1ec D_1ec (Z_to_bv 64 (m - 16)).
stepsw F_1f0 D_1f0.
stepsw F_1f4 D_1f4.
stepsw F_1f8 D_1f8.
stepsw F_1fc D_1fc.
sv F_200 D_200 (Z_to_bv 64 (D + Z.of_nat o + 1 + 16)).
sv F_204 D_204 (Z_to_bv 64 (S + Z.of_nat o + 32)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 18 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_208 D_208. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia | lia].
+ destruct (Z_lt_le_dec (m - 16) 16) as [Hl|Hh].
* eapply fin_steps.
-- norm_pc. stepbf F_208 D_208.
sv F_20c D_20c (Z_to_bv 64 (S + Z.of_nat o + 17)).
sv F_210 D_210 (Z_to_bv 64 16).
stepbt F_214 D_214. apply mst_refl.
-- frame.
-- fin_apply test_090; [rg | rg | rg | lia | rewrite Z.mod_small by lia; lia].
* eapply fin_steps.
-- norm_pc. stepbf F_208 D_208.
sv F_20c D_20c (Z_to_bv 64 (S + Z.of_nat o + 17)).
sv F_210 D_210 (Z_to_bv 64 16).
stepbf F_214 D_214.
stepj' F_218 D_218. apply mst_refl.
-- frame.
-- fin_apply tail_2dc; [rg | rg | rg | lia | ].
replace ((m - 16) mod 16) with (m - 32); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma sh_loop1 : forall k regs o j m,
getr regs 14 = lwv (chunk o 4) ->
getr regs 11 = Z_to_bv 64 (S + Z.of_nat o + 16) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 16 ->
(j = o + 3)%nat -> 17 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat j + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x240)) (M j).
Proof.
induction k as [|k IH]; intros regs o j m H14 H11 H13 H12 H15 Hj Hm Hk Hi; [lia|]. dsl. subst j.
eapply fin_steps.
- norm_pc.
svsrw F_240 D_240 (v_srliw (lwv (chunk o 4)) 24).
steplw F_244 D_244 (o + 4)%nat.
steplw F_248 D_248 (o + 8)%nat.
steplw F_24c D_24c (o + 12)%nat.
steplw F_250 D_250 (o + 16)%nat.
sv F_254 D_254 (v_slli (lwv (chunk (o + 4) 4)) 8).
svsrw F_258 D_258 (v_srliw (lwv (chunk (o + 4) 4)) 24).
svor F_25c D_25c (v_or (v_slli (lwv (chunk (o + 4) 4)) 8) (v_srliw (lwv (chunk o 4)) 24)).
sv F_260 D_260 (v_slli (lwv (chunk (o + 8) 4)) 8).
svsrw F_264 D_264 (v_srliw (lwv (chunk (o + 8) 4)) 24).
svor F_268 D_268 (v_or (v_slli (lwv (chunk (o + 8) 4)) 8) (v_srliw (lwv (chunk (o + 4) 4)) 24)).
sv F_26c D_26c (v_slli (lwv (chunk (o + 12) 4)) 8).
svsrw F_270 D_270 (v_srliw (lwv (chunk (o + 12) 4)) 24).
svor F_274 D_274 (v_or (v_slli (lwv (chunk (o + 12) 4)) 8) (v_srliw (lwv (chunk (o + 8) 4)) 24)).
sv F_278 D_278 (v_slli (lwv (chunk (o + 16) 4)) 8).
svor F_27c D_27c (v_or (v_slli (lwv (chunk (o + 16) 4)) 8) (v_srliw (lwv (chunk (o + 12) 4)) 24)).
sv F_280 D_280 (Z_to_bv 64 (m - 16)).
stepsw F_284 D_284.
stepsw F_288 D_288.
stepsw F_28c D_28c.
stepsw F_290 D_290.
sv F_294 D_294 (Z_to_bv 64 (D + Z.of_nat o + 3 + 16)).
sv F_298 D_298 (Z_to_bv 64 (S + Z.of_nat o + 32)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 16 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_29c D_29c. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia | lia].
+ destruct (Z_lt_le_dec (m - 16) 16) as [Hl|Hh].
* eapply fin_steps.
-- norm_pc. stepbf F_29c D_29c.
sv F_2a0 D_2a0 (Z_to_bv 64 (S + Z.of_nat o + 19)).
sv F_2a4 D_2a4 (Z_to_bv 64 16).
stepbt F_2a8 D_2a8. apply mst_refl.
-- frame.
-- fin_apply test_090; [rg | rg | rg | lia | rewrite Z.mod_small by lia; lia].
* eapply fin_steps.
-- norm_pc. stepbf F_29c D_29c.
sv F_2a0 D_2a0 (Z_to_bv 64 (S + Z.of_nat o + 19)).
sv F_2a4 D_2a4 (Z_to_bv 64 16).
stepbf F_2a8 D_2a8.
apply mst_refl.
-- frame.
-- fin_apply tail_2dc; [rg | rg | rg | lia | ].
replace ((m - 16) mod 16) with (m - 32); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma sh_0a4 : forall regs i m r,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 r ->
0 < r < 4 -> 32 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x74)) (M i).
Proof.
intros regs i m r H11 H13 H12 H15 Hr Hm Hi. dsl.
assert (Hr3 : r = 1 \/ r = 2 \/ r = 3) by lia.
destruct Hr3 as [Hr1|[Hr2|Hr3]]; subst r.
-
eapply fin_steps.
+ norm_pc.
steplw F_074 D_074 i.
sv F_078 D_078 (Z_to_bv 64 3).
stepbf F_07c D_07c.
sv F_080 D_080 (Z_to_bv 64 2).
stepbt F_084 D_084.
sv F_21c D_21c (v_srli (lwv (chunk i 4)) 8).
sv F_220 D_220 (v_srli (lwv (chunk i 4)) 16).
sv F_224 D_224 (Z_to_bv 64 (m - 3)).
stepsb F_228 D_228.
stepsb F_22c D_22c.
stepsb F_230 D_230.
sv F_234 D_234 (Z_to_bv 64 (D + Z.of_nat i + 3)).
sv F_238 D_238 (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_23c D_23c (Z_to_bv 64 16).
apply mst_refl.
+ frame.
+ fin_apply (sh_loop1 (Z.to_nat m)); [rg | rg | rg | rg | rg | lia | lia | lia | lia].
-
eapply fin_steps.
+ norm_pc.
steplw F_074 D_074 i.
sv F_078 D_078 (Z_to_bv 64 3).
stepbf F_07c D_07c.
sv F_080 D_080 (Z_to_bv 64 2).
stepbf F_084 D_084.
sv F_088 D_088 (v_srli (lwv (chunk i 4)) 8).
sv F_08c D_08c (Z_to_bv 64 (m - 2)).
stepsb F_090 D_090.
stepsb F_094 D_094.
sv F_098 D_098 (Z_to_bv 64 (D + Z.of_nat i + 2)).
sv F_09c D_09c (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_0a0 D_0a0 (Z_to_bv 64 17).
apply mst_refl.
+ frame.
+ fin_apply (sh_loop2 (Z.to_nat m)); [rg | rg | rg | rg | rg | lia | lia | lia | lia].
-
eapply fin_steps.
+ norm_pc.
steplw F_074 D_074 i.
sv F_078 D_078 (Z_to_bv 64 3).
stepbt F_07c D_07c.
stepsb F_198 D_198.
sv F_19c D_19c (Z_to_bv 64 (D + Z.of_nat i + 1)).
sv F_1a0 D_1a0 (Z_to_bv 64 (m - 1)).
sv F_1a4 D_1a4 (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_1a8 D_1a8 (Z_to_bv 64 18).
apply mst_refl.
+ frame.
+ fin_apply (sh_loop3 (Z.to_nat m)); [rg | rg | rg | rg | rg | lia | lia | lia | lia].
Qed.
Lemma mid_080 : forall regs i m r,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 r ->
0 < r < 4 -> 0 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x50)) (M i).
Proof.
intros regs i m r H11 H13 H12 H15 Hr Hm Hi. dsl.
destruct (Z_lt_le_dec m 32) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc. sv F_050 D_050 (Z_to_bv 64 32). stepbf F_054 D_054. apply mst_refl.
+ frame.
+ fin_apply test_088; [rg | rg | rg | lia | lia].
- eapply fin_steps.
+ norm_pc. sv F_050 D_050 (Z_to_bv 64 32). stepbt F_054 D_054. apply mst_refl.
+ frame.
+ fin_apply sh_0a4; [rg | rg | rg | rg | lia | lia | lia].
Qed.
Lemma mid_078 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
0 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x48)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hr : 0 <= (D + Z.of_nat i) mod 4 < 4) by (apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec ((D + Z.of_nat i) mod 4) 0) as [Hz|Hnz].
- eapply fin_steps.
+ norm_pc.
sv F_048 D_048 (Z_to_bv 64 0); [rewrite and3_mod4, Hz; reflexivity|].
stepbt F_04c D_04c. apply mst_refl.
+ frame.
+ fin_apply al_150; [rg | rg | rg | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_048 D_048 (Z_to_bv 64 ((D + Z.of_nat i) mod 4)); [rewrite and3_mod4; reflexivity|].
stepbf F_04c D_04c. apply mst_refl.
+ frame.
+ fin_apply mid_080; [rg | rg | rg | rg | lia | lia | lia].
Qed.
Lemma ph1_loop : forall k regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 14 = Z_to_bv 64 (S + Z.of_nat i + 1) ->
getr regs 15 = Z_to_bv 64 1 ->
1 <= m -> m <= Z.of_nat k ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x18)) (M i).
Proof.
induction k as [|k IH]; intros regs i m H11 H13 H12 H14 H15 Hm Hk Hi; [lia|]. dsl.
assert (Hr : 0 <= (S + Z.of_nat i + 1) mod 4 < 4) by (apply Z.mod_pos_bound; lia).
eapply fin_steps.
- norm_pc.
steplbu F_018 D_018 i.
sv F_01c D_01c (Z_to_bv 64 m).
sv F_020 D_020 (Z_to_bv 64 (S + Z.of_nat i + 1)).
sv F_024 D_024 (Z_to_bv 64 ((S + Z.of_nat i + 1) mod 4)); [rewrite and3_mod4; reflexivity|].
stepsb F_028 D_028.
sv F_02c D_02c (Z_to_bv 64 (D + Z.of_nat i + 1)).
sv F_030 D_030 (Z_to_bv 64 (m - 1)).
apply mst_refl.
- frame.
- destruct (Z.eq_dec ((S + Z.of_nat i + 1) mod 4) 0) as [Hz|Hnz].
+
eapply fin_steps.
* norm_pc. stepbt F_034 D_034. apply mst_refl.
* frame.
* fin_apply mid_078; [rg | rg | rg | lia | lia].
+ destruct (Z.eq_dec m 1) as [H1|Hn1].
*
eapply fin_steps.
-- norm_pc. stepbf F_034 D_034.
sv F_038 D_038 (Z_to_bv 64 (S + Z.of_nat i + 2)).
stepbf F_03c D_03c.
stepj' F_040 D_040. apply mst_refl.
-- frame.
-- fin_apply mid_078; [rg | rg | rg | lia | lia].
* eapply fin_steps.
-- norm_pc. stepbf F_034 D_034.
sv F_038 D_038 (Z_to_bv 64 (S + Z.of_nat i + 2)).
stepbt F_03c D_03c. apply mst_refl.
-- frame.
-- fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia].
Qed.
Lemma entry_030 : forall regs,
getr regs 10 = d -> getr regs 11 = s ->
getr regs 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
fin regs (Z_to_bv 64 (tfib_A_memcpy_libc + 0x0)) (M 0).
Proof.
intros regs H10' H11' H12. dsl.
assert (H10 : getr regs 10 = Z_to_bv 64 (D + Z.of_nat 0))
by (rewrite H10', HD_, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (H11 : getr regs 11 = Z_to_bv 64 (S + Z.of_nat 0))
by (rewrite H11', HS_, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
clear H10' H11'.
assert (HSm : 0 <= S mod 4 < 4) by (apply Z.mod_pos_bound; lia).
assert (HDm : 0 <= D mod 4 < 4) by (apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec (S mod 4) 0) as [HSz|HSnz].
-
destruct (Z.eq_dec (D mod 4) 0) as [HDz|HDnz].
+ eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 0); [rewrite and3_mod4; rewrite <- HSz; f_equal; f_equal; lia|].
stepbt F_004 D_004.
sv F_114 D_114 (Z_to_bv 64 (D + Z.of_nat 0)).
sv F_118 D_118 (Z_to_bv 64 0); [rewrite and3_mod4; rewrite <- HDz; f_equal; f_equal; lia|].
stepbf F_11c D_11c. apply mst_refl.
* frame.
* fin_apply al_150; [rg | rg | rg | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 0); [rewrite and3_mod4; rewrite <- HSz; f_equal; f_equal; lia|].
stepbt F_004 D_004.
sv F_114 D_114 (Z_to_bv 64 (D + Z.of_nat 0)).
sv F_118 D_118 (Z_to_bv 64 (D mod 4)); [rewrite and3_mod4; f_equal; f_equal; lia|].
stepbt F_11c D_11c. apply mst_refl.
* frame.
* fin_apply mid_080; [rg | rg | rg | rg | lia | lia | lia].
- destruct (Nat.eq_dec (length bs) 0) as [HL0|HLnz].
+
eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 (S mod 4)); [rewrite and3_mod4; f_equal; f_equal; lia|].
stepbf F_004 D_004.
stepbt F_008 D_008.
sv F_044 D_044 (Z_to_bv 64 (D + Z.of_nat 0)).
apply mst_refl.
* frame.
* fin_apply mid_078; [rg | rg | rg | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 (S mod 4)); [rewrite and3_mod4; f_equal; f_equal; lia|].
stepbf F_004 D_004.
stepbf F_008 D_008.
sv F_00c D_00c (Z_to_bv 64 (S + Z.of_nat 0 + 1)).
sv F_010 D_010 (Z_to_bv 64 1).
sv F_014 D_014 (Z_to_bv 64 (D + Z.of_nat 0)).
apply mst_refl.
* frame.
* fin_apply (ph1_loop (length bs)); [rg | rg | rg | rg | rg | lia | lia | lia].
Qed.
End f.
Theorem tfib_memcpy_same :
forall (bs : list byte) (d s n : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = n ->
bv_unsigned n = Z.of_nat (length bs) ->
rdn tfibsegs mem s (length bs) = Some bs ->
store_ok tfibsegs mem d (length bs) = true ->
bv_unsigned d + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned s + Z.of_nat (length bs) <= 2^64 ->
s = d -> bv_unsigned d + Z.of_nat (length bs) < 2^64 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_memcpy_libc) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv ->
r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs' r = getr regs r).
Proof.
intros bs d s n mem rom regs H10 H11 H12 Hn Hsrc Hdst Hnd Hns Hsame Hsmall.
change (Z_to_bv 64 tfib_A_memcpy_libc) with (Z_to_bv 64 (tfib_A_memcpy_libc + 0x0)).
assert (H12' : getr regs 12 = Z_to_bv 64 (Z.of_nat (length bs)))
by (rewrite H12, <- Hn, Z_to_bv_bv_unsigned; reflexivity).
destruct (entry_030 bs d s mem rom Hsrc Hdst Hnd Hns Hsame Hsmall regs H10 H11 H12') as (regs' & Hms & Hfr).
exists regs'. split; [exact Hms|]. split.
- rewrite Hfr; [exact H10|]. unfold keep. repeat split; reg_neq_tac.
- intros. apply Hfr. unfold keep. repeat split; assumption.
Qed.
End e.
End C.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3c AE20 AE2y AE6k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import AcpySameDef.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition q1_0oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_0o_e0 BC_EQ (RG q1_0o_e0 10) (RG q1_0o_e0 11))).
Lemma r_q1_0oC_0 : RUN (AC q1_0o_e0 BC_EQ (RG q1_0o_e0 10) (RG q1_0o_e0 11)) = (q1_0oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_0oC_canon : DROPC q1_0oC_e0 = q1_0_c. Proof. reflexivity. Qed.
Definition q1_1oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_1o_e0 BC_EQ (RG q1_1o_e0 10) (RG q1_1o_e0 11))).
Lemma r_q1_1oC_0 : RUN (AC q1_1o_e0 BC_EQ (RG q1_1o_e0 10) (RG q1_1o_e0 11)) = (q1_1oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_1oC_canon : DROPC q1_1oC_e0 = q1_1_c. Proof. reflexivity. Qed.
Definition q1_2oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_2o_e0 BC_EQ (RG q1_2o_e0 10) (RG q1_2o_e0 11))).
Lemma r_q1_2oC_0 : RUN (AC q1_2o_e0 BC_EQ (RG q1_2o_e0 10) (RG q1_2o_e0 11)) = (q1_2oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_2oC_canon : DROPC q1_2oC_e0 = q1_2_c. Proof. reflexivity. Qed.
Definition q1_3oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_3o_e0 BC_EQ (RG q1_3o_e0 10) (RG q1_3o_e0 11))).
Lemma r_q1_3oC_0 : RUN (AC q1_3o_e0 BC_EQ (RG q1_3o_e0 10) (RG q1_3o_e0 11)) = (q1_3oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_3oC_canon : DROPC q1_3oC_e0 = q1_3_c. Proof. reflexivity. Qed.
Definition q1_4oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_4o_e0 BC_EQ (RG q1_4o_e0 10) (RG q1_4o_e0 11))).
Lemma r_q1_4oC_0 : RUN (AC q1_4o_e0 BC_EQ (RG q1_4o_e0 10) (RG q1_4o_e0 11)) = (q1_4oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_4oC_canon : DROPC q1_4oC_e0 = q1_4_c. Proof. reflexivity. Qed.
Definition q1_5oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_5o_e0 BC_EQ (RG q1_5o_e0 10) (RG q1_5o_e0 11))).
Lemma r_q1_5oC_0 : RUN (AC q1_5o_e0 BC_EQ (RG q1_5o_e0 10) (RG q1_5o_e0 11)) = (q1_5oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_5oC_canon : DROPC q1_5oC_e0 = q1_5_c. Proof. reflexivity. Qed.
Definition q1_6oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_6o_e0 BC_EQ (RG q1_6o_e0 10) (RG q1_6o_e0 11))).
Lemma r_q1_6oC_0 : RUN (AC q1_6o_e0 BC_EQ (RG q1_6o_e0 10) (RG q1_6o_e0 11)) = (q1_6oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_6oC_canon : DROPC q1_6oC_e0 = q1_6_c. Proof. reflexivity. Qed.
Definition q1_7oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_7o_e0 BC_EQ (RG q1_7o_e0 10) (RG q1_7o_e0 11))).
Lemma r_q1_7oC_0 : RUN (AC q1_7o_e0 BC_EQ (RG q1_7o_e0 10) (RG q1_7o_e0 11)) = (q1_7oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_7oC_canon : DROPC q1_7oC_e0 = q1_7_c. Proof. reflexivity. Qed.
Definition q1_8oC_e0 : sstate := Eval vm_compute in fst (RUN (AC q1_8o_e0 BC_EQ (RG q1_8o_e0 10) (RG q1_8o_e0 11))).
Lemma r_q1_8oC_0 : RUN (AC q1_8o_e0 BC_EQ (RG q1_8o_e0 10) (RG q1_8o_e0 11)) = (q1_8oC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q1_8oC_canon : DROPC q1_8oC_e0 = q1_8_c. Proof. reflexivity. Qed.
Definition q2LoC_e0 : sstate := Eval vm_compute in fst (RUN (AC q2Lo_e0 BC_EQ (RG q2Lo_e0 10) (RG q2Lo_e0 11))).
Lemma r_q2LoC_0 : RUN (AC q2Lo_e0 BC_EQ (RG q2Lo_e0 10) (RG q2Lo_e0 11)) = (q2LoC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q2LoC_canon : DROPC q2LoC_e0 = q2L_c. Proof. reflexivity. Qed.
Definition q2HoC_e0 : sstate := Eval vm_compute in fst (RUN (AC q2Ho_e0 BC_EQ (RG q2Ho_e0 10) (RG q2Ho_e0 11))).
Lemma r_q2HoC_0 : RUN (AC q2Ho_e0 BC_EQ (RG q2Ho_e0 10) (RG q2Ho_e0 11)) = (q2HoC_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 11 0) (SLit (-1))) (SOff 12 0))). Proof. vm_compute. reflexivity. Qed.
Lemma q2HoC_canon : DROPC q2HoC_e0 = q2H_c. Proof. reflexivity. Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma mc_tail_same : forall ly S (W : world tfibsegs) regs mem md (regs1 : bvmap 5 word) (mem1 : word -> option byte) mat1 d x n,
ecall_pre tfibsegs B ly S W regs mem md ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 -> 0 <= x -> x + n <= 2 ^ 63 ->
dest_ok tfibsegs B ly S W regs mem d n -> src_ok tfibsegs W regs mem x n -> x = d ->
getr regs1 10 = w64 d -> getr regs1 11 = w64 x -> getr regs1 12 = w64 n ->
getr regs1 1 = w64 MC_RA -> getr regs1 2 = w64 (spZ regs - 2144) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 24 = getr regs 24 -> getr regs1 25 = getr regs 25 -> getr regs1 26 = getr regs 26 -> getr regs1 27 = getr regs 27 ->
(forall z : word, ~ (spZ regs - MC_SCR <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, spZ regs - MC_SCR <= a < spZ regs -> apresent (w_H W) mem1 a) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs - 72) 8 (bv_unsigned (getr regs 23)) ->
SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 MC_REAL) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat1 md))
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) mem (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regs1 mem1 mat1 d x n HPRE Hn Hd Hdn Hx0 Hxn HDST HSRC HSAME G10 G11 G12 G1 G2 G3 G4 G24 G25 G26 G27
MEQ1 PRS1 V0 V1 V2 V3 V4 V5 V6 V7 V8.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. unfold ESTACK, MC_SCR in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
assert (DW : forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. destruct (HDST a Ha) as (Hw & _ & Hns). unfold ESTACK in Hns.
assert (Hw1 : writable_at tfibsegs (mrestrict H mem1) a).
{ apply (writable_at_same (mrestrict H mem) (mrestrict H mem1) a); [|exact Hw].
unfold mrestrict. rewrite (MEQ1 (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. unfold sp0 in *. lia. }
split; [exact Hw1|]. destruct (H (Z_to_bv 64 a)) eqn:Hh; [|reflexivity].
exfalso. exact (hidden_not_writable W mem1 a ltac:(lia) Hh Hw1). }
assert (SRCM : forall a, x <= a < x + n -> mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. destruct (HSRC a Ha) as [_ Hns]. unfold ESTACK in Hns. apply MEQ1. rewrite unsigned_lit_small by lia. unfold sp0 in *. lia. }
destruct (rdn_of_vis (mrestrict H mem1) x (Z.to_nat n) ltac:(lia) ltac:(lia)) as (bs & RDN & LEN & BS).
{ intros i Hi. rewrite (AF0x.mbyte_mrestrict_same H mem mem1 (x + i) (SRCM (x + i) ltac:(lia))).
exact (proj1 (aview_vis H mem (x + i)) (proj1 (HSRC (x + i) ltac:(lia)))). }
assert (SOK : store_ok tfibsegs (mrestrict H mem1) (w64 d) (length bs) = true).
{ rewrite LEN. apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by lia; [lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. exact Wz. }
destruct (C.tfib_memcpy_same bs (w64 d) (w64 x) (w64 n) (mrestrict H mem1) (seg_rom tfibsegs) regs1 G10 G11 G12
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) ltac:(rewrite LEN; exact RDN) SOK
ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia) ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia)
ltac:(rewrite HSAME; reflexivity) ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia))
as (regs2 & Hms & A10 & Hkeep).
rewrite G1 in Hms. replace (v_jalr (w64 MC_RA) 0) with (Z_to_bv 64 MC_RA : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
change (Z_to_bv 64 tfib_A_memcpy_libc) with (Z_to_bv 64 MC_REAL) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 d) bs) in Hms.
assert (KEEP : forall r : bv 5, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs2 r = getr regs1 r) by (intros r; apply Hkeep).
set (mem2 := munrestrict H mem1 m2r).
assert (LENZ : Z.of_nat (length bs) = n) by lia.
assert (M2out : forall z : word, ~ (d <= bv_unsigned z < d + n) -> mem2 z = mem1 z).
{ intros z Hz. subst mem2 m2r. unfold munrestrict. destruct (H z) eqn:Hh; [reflexivity|].
assert (Ew : wbytes m1r (w64 d) bs z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) d) as [L|L].
- apply wbytes_below; unfold w64; rewrite ?LENZ, unsigned_lit_small by lia; lia.
- apply wbytes_above. unfold w64. rewrite LENZ, unsigned_lit_small by lia. lia. }
rewrite Ew. subst m1r. unfold mrestrict. rewrite Hh. reflexivity. }
assert (M2in : forall i, 0 <= i < n -> mem2 (Z_to_bv 64 (d + i)) = Some (nth (Z.to_nat i) bs 0%bv)).
{ intros i Hi. subst mem2. unfold munrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))).
subst m2r. rewrite (wbytes_inside bs m1r (w64 d) (Z_to_bv 64 (d + i)));
unfold w64; rewrite ?LENZ, ?unsigned_lit_small by lia; [|lia|lia].
replace (Z.to_nat (d + i - d)) with (Z.to_nat i) by lia. apply nth_error_nth'. lia. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 - 2216 <= a < sp0) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Ha Hs. apply aview_same. rewrite (M2out (Z_to_bv 64 a)), (MEQ1 (Z_to_bv 64 a)); [reflexivity| |];
rewrite unsigned_lit_small by lia; [exact Hs | exact Ha]. }
assert (MS2 : forall z : word, sp0 - 2216 <= bv_unsigned z < sp0 -> mem2 z = mem1 z).
{ intros z Hz. apply M2out. intros Hd'. destruct (HDST (bv_unsigned z) Hd') as (_ & _ & Hns). unfold ESTACK in Hns. apply Hns. unfold sp0 in *. lia. }
assert (A2 : getr regs2 2 = w64 (sp0 - 2144)) by (rewrite KEEP by (intros H'; discriminate H'); exact G2).
set (E2 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23]).
assert (E2_2 : bv_unsigned (ew E2 2) = sp0 - 2144).
{ subst E2. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), A2. unfold w64. apply unsigned_lit_small. lia. }
assert (VM : forall a v, val_mem tfibsegs (mrestrict H mem1) a 8 v -> sp0 - 2216 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H mem2) a 8 v).
{ intros a v Hv Hlo Hhi. apply (val_mem_frame H mem1 mem2 a 8 v); [|exact Hv]. intros k Hk. apply MS2. rewrite unsigned_lit_small by lia. lia. }
assert (HSe : st_ok tfibsegs E2 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 MC_RA) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23]) with E2.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E2 (Some 2%nat)) with (sp0 - 2144) by (symmetry; exact E2_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold stkD_chunks.
assert (CK : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23] (Z_to_bv 64 0) = getr regs r ->
off = 2136 - 8 * Z.of_nat j -> Z.of_nat j < 9 ->
val_mem tfibsegs (mrestrict H mem1) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E2 (mrestrict H mem2) (sp0 - 2144) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E2 _ (sp0 - 2144) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E2. rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 2144 + (2136 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. apply VM; [exact Hv | lia | lia]. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by lia; exact V0].
+ apply (CK 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact V1].
+ apply (CK 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact V2].
+ apply (CK 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact V3].
+ apply (CK 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact V4].
+ apply (CK 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact V5].
+ apply (CK 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact V6].
+ apply (CK 7%nat 22%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 7) with (sp0 - 64) by lia; exact V7].
+ apply (CK 8%nat 23%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 8) with (sp0 - 72) by lia; exact V8].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2144) with (spZ regs + (-134) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb md model' Hsbm). cbn [ms_mem mkst].
change (unrestrict H mem1 (mkst regs2 (Z_to_bv 64 MC_RA) m2r (seg_rom tfibsegs))) with (mkst regs2 (Z_to_bv 64 MC_RA) mem2 (seg_rom tfibsegs)).
eapply SRr_bind; [apply (icpt_phase W E2 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W1 c1 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E2); [exact HS3 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (MEQ3 : forall z, ms_mem ms3 z = mem2 z) by (intros z; apply HF3; intros Hin; destruct (in_wrange_windows E2 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (2%bv : bv 5) Q2. rreg HS3 (10%bv : bv 5) Q10.
rreg HS3 (8%bv : bv 5) Q8. rreg HS3 (9%bv : bv 5) Q9. rreg HS3 (18%bv : bv 5) Q18. rreg HS3 (19%bv : bv 5) Q19.
rreg HS3 (20%bv : bv 5) Q20. rreg HS3 (21%bv : bv 5) Q21. rreg HS3 (22%bv : bv 5) Q22. rreg HS3 (23%bv : bv 5) Q23. rreg HS3 (24%bv : bv 5) Q24.
rreg HS3 (3%bv : bv 5) Q3. rreg HS3 (4%bv : bv 5) Q4.
rreg HS3 (25%bv : bv 5) Q25. rreg HS3 (26%bv : bv 5) Q26. rreg HS3 (27%bv : bv 5) Q27.
assert (X32 : ew E2 32 = getr regs 1) by (subst E2; exact (ew_Ereg_extra regs2 _ 0)).
rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
split; [reflexivity|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
assert (AV3 : forall a, aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply MEQ3).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
-   apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms3) _ HAR).
+ intros a Hr Hown. rewrite AV3. apply AV2; [exact Hr | intros Hd'; exact (proj1 (proj2 (HDST a Hd')) Hown) |].
intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite AV3. rewrite (AE2y.aview_mod _ mem2 a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ unfold aview, mbyte, mrestrict. rewrite (proj2 (DW a' ltac:(lia))). replace a' with (d + (a' - d)) by lia. rewrite (M2in (a' - d)) by lia. discriminate. }
all: destruct (Z_lt_le_dec a' (sp0 - 2216)) as [L3|L3]; [rewrite AV2 by lia; exact Hv|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4]; [| rewrite AV2 by lia; exact Hv].
all: apply aview_some_of_apresent; apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(rewrite unsigned_lit_small by lia; lia))); apply PRS1; lia.
+ apply MF. + apply MF. + apply MF.
+ exact (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_trans _ _ _ _ (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold ESTACK, MC_SCR; lia) ltac:(lia)) (AE2y.hs_kept_unrestrict _ _ _)) (AE2y.hs_kept_eq _ _ _ MEQ3)).
-
intros r Hr. unfold acallee_saved in Hr.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23] (Z_to_bv 64 0) = getr regs rr -> ew E2 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E2; rewrite (ew_Ereg_extra regs2 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E2 i = getr regs2 rr) by (intros ii rr Hnth; subst E2; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
+ replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq. rewrite Z_to_bv_unsigned, E2_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
+ replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (Y 3%nat 3%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G3.
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (Y 4%nat 4%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G4.
+ replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. exact (X 1%nat 8%bv eq_refl).
+ replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9. exact (X 2%nat 9%bv eq_refl).
+ assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
* replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18. exact (X 3%nat 18%bv eq_refl).
* replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19. exact (X 4%nat 19%bv eq_refl).
* replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20. exact (X 5%nat 20%bv eq_refl).
* replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21. exact (X 6%nat 21%bv eq_refl).
* replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q22. exact (X 7%nat 22%bv eq_refl).
* replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q23. exact (X 8%nat 23%bv eq_refl).
* replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q24, (Y 24%nat 24%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G24.
* replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q25, (Y 25%nat 25%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G25.
* replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q26, (Y 26%nat 26%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G26.
* replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q27, (Y 27%nat 27%bv eq_refl), KEEP by (intros H'; discriminate H'). exact G27.
- apply with_vm_backing_same.
- rewrite Q10. subst E2. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact A10.
- intros i Hi. rewrite AV3. rewrite <- (aview_same H mem mem1 (x + i) (SRCM (x + i) ltac:(lia))).
unfold aview. replace (mbyte tfibsegs (mrestrict H mem2) (d + i)) with (Some (nth (Z.to_nat i) bs 0%bv)).
2:{ unfold mbyte, mrestrict. rewrite (proj2 (DW (d + i) ltac:(lia))), (M2in i Hi). reflexivity. }
subst m1r. replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. rewrite (BS (Z.to_nat i) ltac:(lia)). reflexivity.
- intros a Hr Hd' Hs. rewrite AV3. apply AV2; [exact Hr | exact Hd' | unfold sp0 in *; lia].
- intros a Hp. pose proof Hp as [Hh [b Hb]].
assert (Hr : apresent H (ms_mem ms3) a <-> apresent H (ms_mem ms3) (a mod 2 ^ 64)).
{ unfold apresent. rewrite <- (AE2y.Z_to_bv64_of_mod a). tauto. }
apply (proj2 Hr). clear Hr.
assert (Hp' : apresent H mem (a mod 2 ^ 64)) by (unfold apresent; rewrite (AE2y.Z_to_bv64_of_mod a); exact Hp).
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
apply (apresent_same H mem2 (ms_mem ms3) a' (MEQ3 _)).
destruct (Z_lt_le_dec a' d) as [L1|L1]; [| destruct (Z_lt_le_dec a' (d + n)) as [L2|L2]].
2:{ split; [exact (proj2 (DW a' ltac:(lia)))|]. eexists. replace a' with (d + (a' - d)) by lia. apply M2in. lia. }
all: destruct (Z_lt_le_dec a' (sp0 - 2216)) as [L3|L3];
[apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp']|].
all: destruct (Z_lt_le_dec a' sp0) as [L4|L4];
[| apply (apresent_same H mem mem2 a'); [rewrite (M2out (Z_to_bv 64 a')), (MEQ1 (Z_to_bv 64 a')) by (rewrite unsigned_lit_small by lia; lia); reflexivity | exact Hp']].
all: apply (apresent_same H mem1 mem2 a' (MS2 (Z_to_bv 64 a') ltac:(rewrite unsigned_lit_small by lia; lia))); apply PRS1; lia.
Qed.
End h.
Section l.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfibsegs B ly S W regs mem d n.
Hypothesis HAM : amem_range d n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis HSRC : src_ok tfibsegs W regs mem x n.
Hypothesis HSAME : x = d.
Hypothesis HAMX : amem_range x n.
Hypothesis HRAX : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis HHULLX : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0s : Z := x / 8.
Let g1s : Z := (x + n - 1) / 8.
Let dus : Z := (x + 7) / 8 * 8.
Let des : Z := (x + n) / 8 * 8.
Let gus : Z := (x + 7) / 8.
Let ges : Z := (x + n) / 8.
Let g0d : Z := d / 8.
Let g1d : Z := (d + n - 1) / 8.
Let dud : Z := (d + 7) / 8 * 8.
Let ded : Z := (d + n) / 8 * 8.
Let gud : Z := (d + 7) / 8.
Let ged : Z := (d + n) / 8.
Local Notation Env := (AE2y.Env regs).
Local Notation POSTc := (AE6k.POSTc B ly S W regs mem md d x n).
Local Notation SV := (AE6k.SV regs).
Local Notation MIDP := (AE6k.MIDP W regs mem d x n).
Local Notation MIDQ := (AE6k.MIDQ W regs mem md d x n).
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 4096 <= sp0 /\ sp0 mod 16 = 0 /\ d + n <= 2 ^ 47 - 1 /\ x + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 4096 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfibsegs H mem).
Proof.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, ESTACK in *. subst sp0 H.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HpresE | exact (proj1 HAR)].
Qed.
Lemma shape_regs : forall E ss ms (r : bv 5) v, st_ok tfibsegs E ss (restrict H ms) -> reg_is ss (bv_unsigned r) v = true ->
getr (ms_regs ms) r = sv_denot E v.
Proof.
intros E ss ms r v HS Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H E ss ms r HS).
Qed.
Lemma shape_chunk : forall E ss ms r0 rest off i spv, st_ok tfibsegs E ss (restrict H ms) -> ss_mem ss = r0 :: rest ->
YP09.r_base r0 = Some 2%nat -> bv_unsigned (ew E 2) = spv -> has_chunk ss off (SOff i 0) = true ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) (spv + off) 8 (bv_unsigned (ew E i)).
Proof.
intros E ss ms r0 rest off i spv HS Hmem Hbase E2 Hc. unfold has_chunk in Hc. rewrite Hmem in Hc. apply existsb_exists in Hc as (c & Hin & Hc).
apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E2 in Hck.
apply (val_of_chunk_ok tfibsegs E _ _ off 8 (SOff i 0) (bv_unsigned (ew E i)) Hck).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (ew E i)). zside.
- zside.
Qed.
Lemma finishD : forall E (regsm : bvmap 5 word) ss ms mat,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeD ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regsm r) ->
(forall j, (j < 10)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j SV 0)) ->
getr regsm 2 = w64 (sp0 - 2144) -> getr regsm 10 = w64 d -> getr regsm 11 = w64 x -> getr regsm 12 = w64 n ->
getr regsm 3 = getr regs 3 -> getr regsm 4 = getr regs 4 -> getr regsm 24 = getr regs 24 -> getr regsm 25 = getr regs 25 -> getr regsm 26 = getr regs 26 -> getr regsm 27 = getr regs 27 ->
(forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MC_SCR <= a < sp0 - MC_STK -> apresent H (ms_mem ms) a) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POSTc.
Proof.
intros E regsm ss ms mat HS Hrv Hsh HE HSVv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27 MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold MC_SCR, MC_STK in *.
unfold shapeD in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24].
apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0 - 2144) by (rewrite (HE 2%nat 2%bv eq_refl), M2; unfold w64; apply unsigned_lit_small; lia).
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regsm r).
{ intros r i Hi Hr. rewrite (shape_regs E ss ms r _ HS Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j az off, nth_error SAVEDD j = Some (az, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms)) (sp0 - 2144 + off) 8 (nth j SV 0)).
{ intros j az off Hj. rewrite forallb_forall in HSV. specialize (HSV (az, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hj10 : (j < 10)%nat /\ az = 32 + Z.of_nat j) by (do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; split; [lia|reflexivity] |]); destruct j; discriminate).
destruct Hj10 as [Hj10 ->]. replace (Z.to_nat (32 + Z.of_nat j)) with (32 + j)%nat in HSV by lia.
pose proof (shape_chunk E ss ms r0 rest off (32 + j) (sp0 - 2144) HS Hmem Hbase E2 HSV) as V.
rewrite (HSVv j Hj10) in V. rewrite unsigned_lit_small in V; [exact V|].
do 10 (destruct j as [|j]; [cbn; apply u64_range|]). lia. }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
apply (mc_tail_same B LAWS ly S W regs mem md (ms_regs ms) (ms_mem ms) mat d x n HPRE Hn Hd Hdn Hx0 Hxn HDST HSRC HSAME).
- rewrite (shape_regs E ss ms 10%bv _ HS R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M10.
- rewrite (shape_regs E ss ms 11%bv _ HS R11). cbn [sv_denot]. rewrite (HE 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M11.
- rewrite (shape_regs E ss ms 12%bv _ HS R12). cbn [sv_denot]. rewrite (HE 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M12.
- rewrite (shape_regs E ss ms 1%bv _ HS R1). reflexivity.
- rewrite (shape_regs E ss ms 2%bv _ HS R2). cbn [sv_denot]. rewrite (HE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact M2.
- rewrite (RA 3%bv 3%nat eq_refl R3). exact M3. - rewrite (RA 4%bv 4%nat eq_refl R4). exact M4.
- rewrite (RA 24%bv 24%nat eq_refl R24). exact M24. - rewrite (RA 25%bv 25%nat eq_refl R25). exact M25. - rewrite (RA 26%bv 26%nat eq_refl R26). exact M26. - rewrite (RA 27%bv 27%nat eq_refl R27). exact M27.
- unfold MC_SCR. exact MEQ.
- intros a Ha. unfold MC_SCR in Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [apply PRS; lia|].
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. lia.
- replace (spZ regs - 8) with (spZ regs - 2144 + 2136) by lia. exact (CK 0%nat 32 2136 eq_refl).
- replace (spZ regs - 16) with (spZ regs - 2144 + 2128) by lia. exact (CK 1%nat 33 2128 eq_refl).
- replace (spZ regs - 24) with (spZ regs - 2144 + 2120) by lia. exact (CK 2%nat 34 2120 eq_refl).
- replace (spZ regs - 32) with (spZ regs - 2144 + 2112) by lia. exact (CK 3%nat 35 2112 eq_refl).
- replace (spZ regs - 40) with (spZ regs - 2144 + 2104) by lia. exact (CK 4%nat 36 2104 eq_refl).
- replace (spZ regs - 48) with (spZ regs - 2144 + 2096) by lia. exact (CK 5%nat 37 2096 eq_refl).
- replace (spZ regs - 56) with (spZ regs - 2144 + 2088) by lia. exact (CK 6%nat 38 2088 eq_refl).
- replace (spZ regs - 64) with (spZ regs - 2144 + 2080) by lia. exact (CK 7%nat 39 2080 eq_refl).
- replace (spZ regs - 72) with (spZ regs - 2144 + 2072) by lia. exact (CK 8%nat 40 2072 eq_refl).
Qed.
Lemma midS : forall E ss ms,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeS ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - MC_SCR <= a < sp0 - MC_STK -> apresent H (ms_mem ms) a) ->
MIDP ms.
Proof.
intros E ss ms HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold MC_SCR, MC_STK in *.
unfold shapeS in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh R27]. apply andb_prop in Hsh as [Hsh R26]. apply andb_prop in Hsh as [Hsh R25]. apply andb_prop in Hsh as [Hsh R24].
apply andb_prop in Hsh as [Hsh R4]. apply andb_prop in Hsh as [Hsh R3]. apply andb_prop in Hsh as [Hsh R22]. apply andb_prop in Hsh as [Hsh R19].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 d) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (rewrite (HE 12%nat 12%bv eq_refl); exact G12).
assert (RA : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> reg_is ss (bv_unsigned r) (SOff i 0) = true -> getr (ms_regs ms) r = getr regs r).
{ intros r i Hi Hr. rewrite (shape_regs E ss ms r _ HS Hr). cbn [sv_denot]. rewrite (HE i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
unfold MIDP. unfold MC_SCR.
split; [pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape; rewrite Hpc in Hshape; exact Hshape|].
split; [rewrite (RA 10%bv 10%nat eq_refl R10); exact G10|]. split; [rewrite (RA 11%bv 11%nat eq_refl R11); exact G11|]. split; [rewrite (RA 12%bv 12%nat eq_refl R12); exact G12|].
split; [rewrite (shape_regs E ss ms 2%bv _ HS R2); cbn [sv_denot]; rewrite (HE 2%nat 2%bv eq_refl); reflexivity|].
split.
{ rewrite (shape_regs E ss ms 19%bv _ HS R19). rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (bv_unsigned (sv_denot E ?v)) with (U E v). rewrite (U_add2 E 10 12 d n E10 E12) by lia. reflexivity. }
split; [rewrite (shape_regs E ss ms 22%bv _ HS R22); cbn [sv_denot]; rewrite E12, unsigned_lit_small by lia; reflexivity|].
split; [exact (RA 3%bv 3%nat eq_refl R3)|]. split; [exact (RA 4%bv 4%nat eq_refl R4)|].
split; [exact (RA 24%bv 24%nat eq_refl R24)|]. split; [exact (RA 25%bv 25%nat eq_refl R25)|]. split; [exact (RA 26%bv 26%nat eq_refl R26)|]. split; [exact (RA 27%bv 27%nat eq_refl R27)|].
split; [exact MEQ|]. split.
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 2208)) as [L|L]; [apply PRS; lia|].
apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold MC_STK. lia. }
intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
rewrite <- (HE (Z.to_nat rz) (Z_to_bv 5 rz)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
exact (shape_chunk E ss ms r0 rest off (Z.to_nat rz) sp0 HS Hmem Hbase E2 HSV).
Qed.
Lemma EnvS_reg : forall extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env extra) i = getr regs r.
Proof. intros. apply AE2y.Env_reg. assumption. Qed.
Lemma EnvS_x : forall extra j z, nth_error extra j = Some z -> ew (Env extra) (32 + j) = Z_to_bv 64 z.
Proof. intros. apply AE2y.Env_x. assumption. Qed.
Lemma EnvS2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. intros extra. rewrite (EnvS_reg extra 2 2%bv eq_refl). reflexivity. Qed.
Lemma EnvS10 : forall extra, ew (Env extra) 10 = Z_to_bv 64 d.
Proof. intros extra. rewrite (EnvS_reg extra 10 10%bv eq_refl). exact G10. Qed.
Lemma EnvS11 : forall extra, ew (Env extra) 11 = Z_to_bv 64 x.
Proof. intros extra. rewrite (EnvS_reg extra 11 11%bv eq_refl). exact G11. Qed.
Lemma EnvS12 : forall extra, ew (Env extra) 12 = Z_to_bv 64 n.
Proof. intros extra. rewrite (EnvS_reg extra 12 12%bv eq_refl). exact G12. Qed.
Lemma entS_stk : forall extra, region_ok tfibsegs (Env extra) (mrestrict H mem) stkS.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold stkS, MC_STK.
apply (region_ok_stack tfibsegs (Env extra) _ 2 sp0 (- 2208)); [exact (EnvS2 extra) | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Bpres. lia.
Qed.
Lemma entS_ro : forall extra, Forall (region_ok tfibsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros extra. pose proof basics as (_ & _ & _ & _ & _ & _ & BM). exact (icpt_rodata_ok B TB ly S H mem (Env extra) BM). Qed.
Definition EnvD (ms : machine_state) (extra : list Z) : env := AE2y.Env (ms_regs ms) (SV ++ extra).
Lemma EnvD_reg : forall ms extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (EnvD ms extra) i = getr (ms_regs ms) r.
Proof. intros. unfold EnvD. apply AE2y.Env_reg. assumption. Qed.
Lemma EnvD_sv : forall ms extra j, (j < 10)%nat -> ew (EnvD ms extra) (32 + j) = Z_to_bv 64 (nth j SV 0).
Proof.
intros ms extra j Hj. unfold EnvD. apply AE2y.Env_x. rewrite nth_error_app1 by (cbn; lia).
apply nth_error_nth'. cbn. lia.
Qed.
Lemma EnvD_x : forall ms extra j z, nth_error extra j = Some z -> ew (EnvD ms extra) (42 + j) = Z_to_bv 64 z.
Proof.
intros ms extra j z Hj. unfold EnvD. replace (42 + j)%nat with (32 + (10 + j))%nat by lia. apply AE2y.Env_x.
rewrite nth_error_app2 by (cbn; lia). replace (10 + j - length SV)%nat with j by (cbn; lia). exact Hj.
Qed.
Lemma EnvD2 : forall ms extra, MIDP ms -> bv_unsigned (ew (EnvD ms extra) 2) = sp0 - 2144.
Proof.
intros ms extra HM. rewrite (EnvD_reg ms extra 2 2%bv eq_refl). rewrite (proj1 (proj2 (proj2 (proj2 (proj2 HM))))).
pose proof basics as (Bsp & _). unfold w64. apply unsigned_lit_small. lia.
Qed.
Lemma EnvD10 : forall ms extra, MIDP ms -> ew (EnvD ms extra) 10 = Z_to_bv 64 d.
Proof. intros ms extra HM. rewrite (EnvD_reg ms extra 10 10%bv eq_refl). exact (proj1 (proj2 HM)). Qed.
Lemma EnvD11 : forall ms extra, MIDP ms -> ew (EnvD ms extra) 11 = Z_to_bv 64 x.
Proof. intros ms extra HM. rewrite (EnvD_reg ms extra 11 11%bv eq_refl). exact (proj1 (proj2 (proj2 HM))). Qed.
Lemma EnvD12 : forall ms extra, MIDP ms -> ew (EnvD ms extra) 12 = Z_to_bv 64 n.
Proof. intros ms extra HM. rewrite (EnvD_reg ms extra 12 12%bv eq_refl). exact (proj1 (proj2 (proj2 (proj2 HM)))). Qed.
Lemma entD_stk : forall ms extra, MIDP ms -> region_ok tfibsegs (EnvD ms extra) (mrestrict H (ms_mem ms)) stkD.
Proof.
intros ms extra HM. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEQ & PRS & SAV). unfold MC_SCR in *.
unfold stkD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val (EnvD ms extra) (Some 2%nat)) with (bv_unsigned (ew (EnvD ms extra) 2)). rewrite (EnvD2 ms extra HM).
split; [lia|]. split; [lia|]. split; [intros o Ho; apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia | apply PRS; lia]|].
unfold stkD_chunks.
assert (CK : forall (j : nat) off rz soff, nth_error SAVED j = Some (rz, soff) -> off = 2144 + soff -> (j < 10)%nat ->
YP09.chunk_ok tfibsegs (EnvD ms extra) (mrestrict H (ms_mem ms)) (sp0 - 2144) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off rz soff Hj Hoff Hj10. eapply (chunk_ok_val tfibsegs (EnvD ms extra) _ (sp0 - 2144) off 8 _ (nth j SV 0)).
- cbn [sv_denot]. rewrite (EnvD_sv ms extra j Hj10), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- do 10 (destruct j as [|j]; [cbn; apply u64_range|]). lia.
- zside.
- subst off. replace (sp0 - 2144 + (2144 + soff)) with (sp0 + soff) by lia.
replace (nth j SV 0) with (bv_unsigned (getr regs (Z_to_bv 5 rz))); [exact (SAV j rz soff Hj)|].
do 9 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; reflexivity|]). destruct j; discriminate. }
repeat apply Forall_cons; try apply Forall_nil.
+ exact (CK 0%nat 2136 1 (-8) eq_refl eq_refl ltac:(lia)).
+ exact (CK 1%nat 2128 8 (-16) eq_refl eq_refl ltac:(lia)).
+ exact (CK 2%nat 2120 9 (-24) eq_refl eq_refl ltac:(lia)).
+ exact (CK 3%nat 2112 18 (-32) eq_refl eq_refl ltac:(lia)).
+ exact (CK 4%nat 2104 19 (-40) eq_refl eq_refl ltac:(lia)).
+ exact (CK 5%nat 2096 20 (-48) eq_refl eq_refl ltac:(lia)).
+ exact (CK 6%nat 2088 21 (-56) eq_refl eq_refl ltac:(lia)).
+ exact (CK 7%nat 2080 22 (-64) eq_refl eq_refl ltac:(lia)).
+ exact (CK 8%nat 2072 23 (-72) eq_refl eq_refl ltac:(lia)).
Qed.
Lemma entD_ro : forall ms extra, MIDP ms -> Forall (region_ok tfibsegs (EnvD ms extra) (mrestrict H (ms_mem ms))) (map ro_region icpt_rodata).
Proof.
intros ms extra HM. pose proof basics as (Bsp & Bhi & _ & _ & _ & _ & BM).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MEQ & _). unfold MC_SCR in MEQ.
pose proof (icpt_rodata_ok B TB ly S H mem (EnvD ms extra) BM) as F0.
assert (WF : regions_wf (map ro_region icpt_rodata) = true) by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) F0 r Hr) as Hr0.
pose proof (regions_wf_In _ r WF Hr) as Hwf. apply region_wf_facts in Hwf as (_ & _ & Hci).
assert (Hlit : exists e, In e icpt_rodata /\ r = ro_region e) by (apply in_map_iff in Hr as (e & <- & He); exists e; auto).
destruct Hlit as (e & He & ->).
assert (Hrange : 0 <= fst (fst e) /\ fst (fst e) + snd (fst e) <= 0x200000).
{ cbn in He. repeat (destruct He as [<-|He]; [cbn; lia|]). destruct He. }
eapply (region_ok_transport tfibsegs (EnvD ms extra) (EnvD ms extra)); [exact Hr0 | reflexivity | | | | exact Hci].
- intros c Hc. unfold ro_region in Hc. cbn [YP09.r_chunks] in Hc. apply in_map_iff in Hc as (cc & <- & _). cbn. reflexivity.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
apply AF0x.mbyte_mrestrict_same. apply MEQ. rewrite unsigned_lit_small by lia. unfold kHighMemBeg in *. lia.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
Qed.
Lemma entD1_0 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 0 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 0) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 0 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 0)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 0 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_1 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 1) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 1 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 1)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 1 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_2 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 2 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 2) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 2 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 2)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 2 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_0 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 0 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_0 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_0_e0 13) (RG w1_0_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_0_e1 13) (RG w1_0_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_0_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450880 E42) by lia. f_equal. subst h2. replace (g0d + 2147450880) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_0_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_0_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 0%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_1 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_1 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_1_e0 13) (RG w1_1_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_1_e1 13) (RG w1_1_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_1_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450881 E42) by lia. f_equal. subst h2. replace (g0d + 2147450881) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_1_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_1_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 1%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_2 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 2 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_2 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_2_e0 13) (RG w1_2_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_2_e1 13) (RG w1_2_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_2_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450882 E42) by lia. f_equal. subst h2. replace (g0d + 2147450882) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_2_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_2_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 2%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD1_3 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 3 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 3) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 3 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 3)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 3 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_4 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 4 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 4) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 4 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 4)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 4 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_5 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 5 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 5) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 5 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 5)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 5 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_3 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 3 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_3 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_3_e0 13) (RG w1_3_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_3_e1 13) (RG w1_3_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_3_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450883 E42) by lia. f_equal. subst h2. replace (g0d + 2147450883) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_3_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_3_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_3_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_3_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 3%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_4 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 4 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_4 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_4_e0 13) (RG w1_4_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_4_e1 13) (RG w1_4_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_4_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450884 E42) by lia. f_equal. subst h2. replace (g0d + 2147450884) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_4_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_4_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_4_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_4_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 4%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_5 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 5 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_5 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_5_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_5_e0 13) (RG w1_5_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_5_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_5_e1 13) (RG w1_5_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_5_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_5_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450885 E42) by lia. f_equal. subst h2. replace (g0d + 2147450885) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_5_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_5_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_5_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_5_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_5z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_5_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_5n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 5%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_5n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD1_6 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 6 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 6) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 6 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 6)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 6 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_7 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 7 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 7) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 7 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 7)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 7 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD1_8 : forall ms b1 q1 q2, MIDP ms -> 1 <= n <= 64 -> g1d - g0d = 8 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; q1; q2]) (ssD1 8) (restrict H ms).
Proof.
intros ms b1 q1 q2 HM Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; q1; q2]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; q1; q2] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; q1; q2] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; q1; q2] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; q1; q2] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shreg1 42 8 :: map ro_region icpt_rodata) None (mkFacts factsD1 [] (aliases1 10 42 8)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; q1; q2]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply (entD_ro ms _ HM)]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; unfold mbyte; rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia); fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i));
rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n (g0d + i) HRA ltac:(lia) Hd); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkD, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E44, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; try apply Z.mod_1_r.
all: match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom_off EE 42 g0d 8 E42) by lia. subst g0d g1d. lia. }
unfold ssD1. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD1_6 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 6 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_6 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_6_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_6_e0 13) (RG w1_6_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_6_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_6_e1 13) (RG w1_6_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_6_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_6_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450886 E42) by lia. f_equal. subst h2. replace (g0d + 2147450886) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_6_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_6_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_6_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_6_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_6z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_6z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_6_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_6n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_6n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 6%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_6n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_6n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_7 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 7 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_7 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_7_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_7_e0 13) (RG w1_7_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_7_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_7_e1 13) (RG w1_7_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_7_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_7_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450887 E42) by lia. f_equal. subst h2. replace (g0d + 2147450887) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_7_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_7_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_7_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_7_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_7z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_7z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_7_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_7n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_7n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 7%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_7n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_7n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD1_8 : forall ms0 mat0, MIDP ms0 -> 1 <= n <= 64 -> g1d - g0d = 8 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0d + 2147450880) / 8 * 8). set (h2 := (g1d + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0d + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1d + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1d + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1d + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0d; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1d; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (ED := EnvD ms0 [g0d; g1d; b1; q1; q2]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; q1; q2] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; q1; q2] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; q1; q2] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; q1; q2] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E45 : ew ED 45 = Z_to_bv 64 q1) by (apply (EnvD_x ms0 _ 3); reflexivity).
assert (E46 : ew ED 46 = Z_to_bv 64 q2) by (apply (EnvD_x ms0 _ 4); reflexivity).
pose proof (entD1_8 ms0 b1 q1 q2 HM Hn64 Ht Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w1_8_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w1_8_e0 13) (RG w1_8_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w1_8_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w1_8_e1 13) (RG w1_8_e1 22) HS2 (br_cls_small ED n ED12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w1_8_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew ED 45))).
{ rewrite E45, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (w1_8_e2) ms3 _ 15%bv 15%bv 505731 h1 45 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr ED 42 g0d 2147450880 E42 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot ED (SAlu ALU_AND (SOff 42 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr ED 42 g0d 2147450888 E42) by lia. f_equal. subst h2. replace (g0d + 2147450888) with (g1d + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew ED 46))).
{ rewrite E46, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W ED (set_regs_pc w1_8_e2 [((15%bv : bv 5), SOff 45 0)] (ss_pc w1_8_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 46 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5 r_w1_8_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_NE (RG w1_8_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_8z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply (finishD ED (ms_regs ms0) w1_8z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_NE (RG w1_8_e3 15) (SLit 0) HS6 (eq_trans (br_hull ED 45 46 q1 q2 E45 E46 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w1_8n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w1_8n_e0 13) (SLit 0) HS7 (qc_flag_zero ED 8%nat 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS7' r_w1_8n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED (ms_regs ms0) w1_8n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EDreg EDsv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entD2L : forall ms b1, MIDP ms -> 64 < n -> d + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2L (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E43 : ew EE 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms _ 1); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
assert (E47 : ew EE 47 = Z_to_bv 64 dud) by (apply (EnvD_x ms _ 5); reflexivity).
assert (E48 : ew EE 48 = Z_to_bv 64 ded) by (apply (EnvD_x ms _ 6); reflexivity).
assert (E49 : ew EE 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms _ 7); reflexivity).
assert (E50 : ew EE 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms _ 8); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2L [] (aliases2 10 42)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply Forall_cons; [| apply (entD_ro ms _ HM)]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia).
fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0d HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 43%nat)) with (bv_unsigned (ew EE 43)). rewrite E43, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, E43, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E43, E44, E47, E48, E49, E50, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; apply Z_mod_mult
| match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 43 g1d E43) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 47 dud E47) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 48 ded E48) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 47 dud E47), (U_atom EE 49 gud E49) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 48 ded E48), (U_atom EE 50 ged E50) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity. }
unfold ssD2L. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma entD2H : forall ms b1, MIDP ms -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1d) = Some b1 -> saddr_ok (d + n - 1) b1 ->
st_ok tfibsegs (EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]) ssD2H (restrict H ms).
Proof.
intros ms b1 HM Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ & PRS & SAV). unfold MC_SCR in MEQ, PRS.
set (EE := EnvD ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (E42 : ew EE 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms _ 0); reflexivity).
assert (E43 : ew EE 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms _ 1); reflexivity).
assert (E44 : ew EE 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms _ 2); reflexivity).
assert (E47 : ew EE 47 = Z_to_bv 64 dud) by (apply (EnvD_x ms _ 5); reflexivity).
assert (E48 : ew EE 48 = Z_to_bv 64 ded) by (apply (EnvD_x ms _ 6); reflexivity).
assert (E49 : ew EE 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms _ 7); reflexivity).
assert (E50 : ew EE 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms _ 8); reflexivity).
pose proof (EnvD2 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E2. pose proof (EnvD10 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E10.
pose proof (EnvD11 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E11. pose proof (EnvD12 ms [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (MEM : forall a, a < sp0 - 4096 -> 0 <= a -> mrestrict H (ms_mem ms) (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a)).
{ intros a Ha Ha0. unfold mrestrict. rewrite (MEQ (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
rewrite Hms. rewrite restrict_mkst_fx.
assert (HS0 : st_ok tfibsegs EE (mkSS MC_MID sr_atoms (stkD :: shregs2 42 ++ map ro_region icpt_rodata) None (mkFacts factsD2H [] (aliases2 10 42)))
(mkst (ms_regs ms) (Z_to_bv 64 MC_MID) (mrestrict H (ms_mem ms)) (seg_rom tfibsegs))).
{ unfold EE, EnvD, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg (ms_regs ms) (map (Z_to_bv 64) (SV ++ [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]))) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply (entD_stk ms _ HM) | apply Forall_cons; [| apply Forall_cons; [| apply (entD_ro ms _ HM)]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 42%nat)) with (bv_unsigned (ew EE 42)). rewrite E42, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. unfold mbyte. rewrite (MEM (g0d + 2147450880 + i)) by (unfold kHighMemBeg in *; lia).
fold (mbyte tfibsegs (mrestrict H mem) (g0d + 2147450880 + i)). rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) d n g0d HRA ltac:(lia) Hd). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 43%nat)) with (bv_unsigned (ew EE 43)). rewrite E43, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1d _ 1 (SOff 44 0) b1); [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply (val_mem_frame H mem (ms_mem ms)); [intros k Hk; apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); unfold kHighMemBeg in *; lia|].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkD, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E42, E43, !unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsD2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E42, E43, E44, E47, E48, E49, E50, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [ rewrite (proj2 Hgu); rewrite Z.mul_comm; apply Z_mod_mult | rewrite (proj2 Hge); rewrite Z.mul_comm; apply Z_mod_mult
| match goal with |- (?a - 2144) mod 16 = 0 => replace (a - 2144) with (a + (-134) * 16) by lia end; rewrite Z_mod_plus_full; exact Bal ].
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 10 d E10), (U_atom EE 42 g0d E42) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 10 12 d n E10 E12), (U_atom EE 43 g1d E43) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 10 d 7 E10), (U_atom EE 47 dud E47) by lia. pose proof (Z.div_mod (d + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 10 12 d n E10 E12), (U_atom EE 48 ded E48) by lia. pose proof (Z.div_mod (d + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 47 dud E47), (U_atom EE 49 gud E49) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 48 ded E48), (U_atom EE 50 ged E50) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity. }
unfold ssD2H. apply (st_ok_regs tfibsegs EE _ _ sr_mid HS0). apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| apply U_inj; rewrite (U_add2 EE 10 12 d n E10 E12) by lia; symmetry; apply (U_atom EE 19 (d + n)); [subst EE; rewrite (EnvD_reg ms _ 19 19%bv eq_refl); exact M19 | lia]
| cbn [sv_denot]; rewrite E12; subst EE; rewrite (EnvD_reg ms _ 22 22%bv eq_refl), M22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity ] |]).
destruct Hr.
Qed.
Lemma pathD2L : forall ms0 mat0, MIDP ms0 -> 64 < n -> d + n <= kLowMemEnd - 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
set (ED := EnvD ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms0 _ 1); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E49 : ew ED 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms0 _ 7); reflexivity).
assert (E50 : ew ED 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms0 _ 8); reflexivity).
assert (E42u : bv_unsigned (ew ED 42) = g0d) by (rewrite E42; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew ED 43) = g1d) by (rewrite E43; apply unsigned_lit_small; lia).
pose proof (entD2L ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w2L_e0 13) (RG w2L_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_GEU (SLit 2147450879) (RG w2L_e1 18) HS2 (br_end_low ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2L_e2 8) (RG w2L_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_zero ED 44 ltac:(rewrite E44, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Lz_e0 19) (RG w2Lz_e0 10) HS5 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Lz_e1 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Lz_e1 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Lz_e1 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Lz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Lz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Lz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Lz_e1 1) = Z_to_bv 64 347520).
{ change (sv_denot ED (RG w2Lz_e1 1)) with (sv_denot ED (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Lz_e1)).
{ cbn [ss_mem w2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Lz_e1 ms6 _ 56 (ss_mem w2Lz_e1) (gud + SB) (ged - gud) (sp0 - 2208) 347520 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED' (ms_regs ms0) w2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_EQ (RG w2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 44 b1 E44 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_LT (RG w2Ln_e0 12) (RG w2Ln_e0 11) HS5 (rp_blt_last ED 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Ln_e1 19) (RG w2Ln_e1 10) HS6 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Ln_e2 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Ln_e2 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Ln_e2 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Ln_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Ln_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Ln_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Ln_e2 1) = Z_to_bv 64 347520).
{ change (sv_denot ED (RG w2Ln_e2 1)) with (sv_denot ED (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Ln_e2)).
{ cbn [ss_mem w2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Ln_e2 ms7 _ 56 (ss_mem w2Ln_e2) (gud + SB) (ged - gud) (sp0 - 2208) 347520 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply (finishD ED' (ms_regs ms0) w2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma pathD2H : forall ms0 mat0, MIDP ms0 -> 64 < n -> kHighMemBeg <= d /\ d + n <= kHighMemEnd - 1 ->
SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
pose proof HM as (Hms & M10 & M11 & M12 & M2 & M19 & M22 & M3 & M4 & M24 & M25 & M26 & M27 & MEQ0 & PRS0 & SAV). unfold MC_SCR in MEQ0, PRS0.
assert (MEQ0' : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms0 z = mem z) by (unfold MC_SCR; exact MEQ0).
clear MEQ0. rename MEQ0' into MEQ0.
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms0 z <> None).
{ intros z Hz. unfold MC_SCR, MC_STK in Hz. destruct (PRS0 (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0d /\ 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1d < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gud <= d + 7 < 8 * gud + 8 /\ dud = 8 * gud) by (subst gud dud; pose proof (Z.div_mod (d + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ged <= d + n < 8 * ged + 8 /\ ded = 8 * ged) by (subst ged ded; pose proof (Z.div_mod (d + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n) 8 ltac:(lia)); lia).
set (ED := EnvD ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged]).
assert (EDreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED i = getr (ms_regs ms0) r) by (intros; apply EnvD_reg; assumption).
assert (EDsv : forall j, (j < 10)%nat -> ew ED (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros; apply EnvD_sv; assumption).
pose proof (EnvD2 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED2. pose proof (EnvD10 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED10. pose proof (EnvD11 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED11. pose proof (EnvD12 ms0 [g0d; g1d; b1; 0; 0; dud; ded; gud; ged] HM) as ED12.
fold ED in ED2, ED10, ED11, ED12.
assert (E42 : ew ED 42 = Z_to_bv 64 g0d) by (apply (EnvD_x ms0 _ 0); reflexivity).
assert (E43 : ew ED 43 = Z_to_bv 64 g1d) by (apply (EnvD_x ms0 _ 1); reflexivity).
assert (E44 : ew ED 44 = Z_to_bv 64 b1) by (apply (EnvD_x ms0 _ 2); reflexivity).
assert (E49 : ew ED 49 = Z_to_bv 64 gud) by (apply (EnvD_x ms0 _ 7); reflexivity).
assert (E50 : ew ED 50 = Z_to_bv 64 ged) by (apply (EnvD_x ms0 _ 8); reflexivity).
assert (E42u : bv_unsigned (ew ED 42) = g0d) by (rewrite E42; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew ED 43) = g1d) by (rewrite E43; apply unsigned_lit_small; lia).
pose proof (entD2H ms0 b1 HM Hn64 Hrg Hb1 Hok) as HS0. fold ED in HS0.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS0 r_w2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (RG w2H_e0 13) (RG w2H_e0 12) HS1 (br_ovf_false ED 10 12 d n ED10 ED12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS1' r_w2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_LTU (SLit 140737488355327) (RG w2H_e1 18) HS2 (br_end_high ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS2' r_w2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2H_e2 8) (RG w2H_e2 18) HS3 (br_beg_lt_end ED 10 12 d n ED10 ED12 Hd ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS3' r_w2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_zero ED 44 ltac:(rewrite E44, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Hz_e0 19) (RG w2Hz_e0 10) HS5 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Hz_e1 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Hz_e1 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Hz_e1 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Hz_e1 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Hz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Hz_e1 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Hz_e1 1) = Z_to_bv 64 347520).
{ change (sv_denot ED (RG w2Hz_e1 1)) with (sv_denot ED (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Hz_e1)).
{ cbn [ss_mem w2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Hz_e1 ms6 _ 56 (ss_mem w2Hz_e1) (gud + SB) (ged - gud) (sp0 - 2208) 347520 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS7 r_w2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply (finishD ED' (ms_regs ms0) w2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (d + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_EQ (RG w2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero ED 44 b1 E44 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS4' r_w2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs ED _ _ BC_LT (RG w2Hn_e0 12) (RG w2Hn_e0 11) HS5 (rp_blt_last ED 10 12 44 d n b1 ED10 ED12 E44 Hd ltac:(lia) Hdn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS5' r_w2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs ED _ _ BC_GEU (RG w2Hn_e1 19) (RG w2Hn_e1 10) HS6 (br_sbeg_lt_send ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W ED _ _ _ _ _ HS6' r_w2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gud + SB <= a < gud + SB + (ged - gud) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) d n (a - SB) HRA); [unfold SB in *; lia | exact Hd]. }
assert (R10 : sv_denot ED (RG w2Hn_e2 10) = Z_to_bv 64 (gud + SB)).
{ change (sv_denot ED (RG w2Hn_e2 10)) with (sv_denot ED (SOff 49 SB)). cbn [sv_denot]. rewrite E49, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot ED (RG w2Hn_e2 11) = Z_to_bv 64 (ged - gud)).
{ change (sv_denot ED (RG w2Hn_e2 11)) with (sv_denot ED (SAlu ALU_ADD (SMd M_MUL (SOff 49 0) (SLit (-1))) (SOff 50 0))). exact (U_mz_len ED 49 50 gud ged E49 E50 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot ED (RG w2Hn_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot ED (RG w2Hn_e2 2)) with (sv_denot ED (SOff 2 (-64))). cbn [sv_denot]. rewrite ED2. f_equal; lia. }
assert (R1 : sv_denot ED (RG w2Hn_e2 1) = Z_to_bv 64 347520).
{ change (sv_denot ED (RG w2Hn_e2 1)) with (sv_denot ED (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val ED (YP09.r_base r) + YP09.r_lo r /\ base_val ED (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val ED (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val ED (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem w2Hn_e2)).
{ cbn [ss_mem w2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?ED2, ?E42u, ?E43u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W ED w2Hn_e2 ms7 _ 56 (ss_mem w2Hn_e2) (gud + SB) (ged - gud) (sp0 - 2208) 347520 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (ED' := havoc ED 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (ED'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew ED' i = getr (ms_regs ms0) r).
{ intros i r Hi. subst ED'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EDreg. exact Hi. }
assert (ED'2 : bv_unsigned (ew ED' 2) = (sp0 - 2144)) by (subst ED'; rewrite ew_havoc_old by lia; exact ED2).
assert (ED'sv : forall j, (j < 10)%nat -> ew ED' (32 + j) = Z_to_bv 64 (nth j SV 0)) by (intros j Hj; subst ED'; rewrite ew_havoc_old by lia; apply EDsv; exact Hj).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase W ED' _ _ _ _ _ HS8 r_w2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b ED' _ (bv_unsigned z) 2 (-64) 2144 (sp0 - 2144) _ ED'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply (finishD ED' (ms_regs ms0) w2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) ED'reg ED'sv M2 M10 M11 M12 M3 M4 M24 M25 M26 M27).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma entS1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 0 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 0) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 0 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 1) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 1 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 2 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 2) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 2 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_0 : 1 <= n <= 64 -> g1s - g0s = 0 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_0_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_0_e0 13) (RG q1_0_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_0_e1 13) (RG q1_0_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_0_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450880 E32) by lia. f_equal. subst h2. replace (g0s + 2147450880) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_0_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_0_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_0z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_0_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 0%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_0n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_0o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_0o_e0 10) (RG q1_0o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_0oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_0oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS1_1 : 1 <= n <= 64 -> g1s - g0s = 1 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_1_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_1_e0 13) (RG q1_1_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_1_e1 13) (RG q1_1_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_1_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450881 E32) by lia. f_equal. subst h2. replace (g0s + 2147450881) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_1_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_1_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_1z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_1_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 1%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_1n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_1o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_1o_e0 10) (RG q1_1o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_1oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_1oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS1_2 : 1 <= n <= 64 -> g1s - g0s = 2 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_2_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_2_e0 13) (RG q1_2_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_2_e1 13) (RG q1_2_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_2_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450882 E32) by lia. f_equal. subst h2. replace (g0s + 2147450882) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_2_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_2_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_2z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_2_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 2%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_2n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_2o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_2o_e0 10) (RG q1_2o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_2oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_2oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma entS1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 3 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 3) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 3 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 4 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 4) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 4 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 5 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 5) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 5 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_3 : 1 <= n <= 64 -> g1s - g0s = 3 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_3_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_3_e0 13) (RG q1_3_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_3_e1 13) (RG q1_3_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_3_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450883 E32) by lia. f_equal. subst h2. replace (g0s + 2147450883) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_3_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_3_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_3_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_3z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_3_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 3%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_3n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_3o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_3o_e0 10) (RG q1_3o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_3oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_3oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS1_4 : 1 <= n <= 64 -> g1s - g0s = 4 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_4_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_4_e0 13) (RG q1_4_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_4_e1 13) (RG q1_4_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_4_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450884 E32) by lia. f_equal. subst h2. replace (g0s + 2147450884) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_4_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_4_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_4_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_4z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_4_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 4%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_4n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_4o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_4o_e0 10) (RG q1_4o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_4oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_4oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS1_5 : 1 <= n <= 64 -> g1s - g0s = 5 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_5_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_5_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_5_e0 13) (RG q1_5_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_5_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_5_e1 13) (RG q1_5_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_5_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_5_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450885 E32) by lia. f_equal. subst h2. replace (g0s + 2147450885) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_5_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_5_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_5_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_5_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_5z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_5z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_5_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_5n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_5n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 5%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_5n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_5n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_5o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_5o_e0 10) (RG q1_5o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_5oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_5oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma entS1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 6 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 6) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 6 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 7 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 7) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 7 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma entS1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1s - g0s = 8 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; q1; q2]) (ssS1 8) (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
set (EE := Env [g0s; g1s; b1; q1; q2]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as E2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as E10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as E11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS1. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; q1; q2])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply entS_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app Nat.add].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n (g0s + i) HRAX ltac:(lia) Hx0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkS, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom_off EE 32 g0s 8 E32) by lia. subst g0s g1s. lia.
Qed.
Lemma pathS1_6 : 1 <= n <= 64 -> g1s - g0s = 6 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_6_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_6_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_6_e0 13) (RG q1_6_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_6_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_6_e1 13) (RG q1_6_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_6_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_6_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450886 E32) by lia. f_equal. subst h2. replace (g0s + 2147450886) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_6_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_6_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_6_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_6_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_6z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_6z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_6_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_6n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_6n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 6%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_6n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_6n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_6o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_6o_e0 10) (RG q1_6o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_6oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_6oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS1_7 : 1 <= n <= 64 -> g1s - g0s = 7 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_7_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_7_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_7_e0 13) (RG q1_7_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_7_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_7_e1 13) (RG q1_7_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_7_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_7_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450887 E32) by lia. f_equal. subst h2. replace (g0s + 2147450887) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_7_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_7_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_7_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_7_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_7z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_7z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_7_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_7n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_7n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 7%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_7n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_7n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_7o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_7o_e0 10) (RG q1_7o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_7oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_7oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS1_8 : 1 <= n <= 64 -> g1s - g0s = 8 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Ht. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULLX ltac:(lia)) as HH.
set (h1 := (g0s + 2147450880) / 8 * 8). set (h2 := (g1s + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0s + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1s + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1s + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1s + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr x / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0s; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (x + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1s; f_equal; f_equal; lia).
destruct (hull_rdword H mem x n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem x n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0s; g1s; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; q1; q2]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; q1; q2]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; q1; q2]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (EnvS_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (EnvS_x _ 4); reflexivity).
pose proof (entS1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q1_8_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q1_8_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q1_8_e0 13) (RG q1_8_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_8_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q1_8_e1 13) (RG q1_8_e1 22) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q1_8_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (q1_8_e2) ms3 _ 15%bv 15%bv 505731 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0s 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0s 2147450888 E32) by lia. f_equal. subst h2. replace (g0s + 2147450888) with (g1s + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MC_STK, MC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc q1_8_e2 [((15%bv : bv 5), SOff 35 0)] (ss_pc q1_8_e2 + 4)) ms4 _ 16%bv 16%bv 538627 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_q1_8_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG q1_8_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS6' r_q1_8z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. split; [reflexivity|]. exists ms7, mat7. split; [reflexivity|].
apply (midS EE q1_8z_e0 ms7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG q1_8_e3 15) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q1_8n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_8n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 8%nat 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE MC_MID _ _ _ _ _ HS7' r_q1_8n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE q1_8n_e1 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q1_8o_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q1_8o_e0 10) (RG q1_8o_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q1_8oC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q1_8oC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma entS2L : forall b1, 64 < n -> x + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2L (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 dus) by (apply (EnvS_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 des) by (apply (EnvS_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E10.
pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS2L. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; 0; 0; dus; des; gus; ges])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply Forall_cons; [| apply entS_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n g0s HRAX ltac:(lia) Hx0). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkS, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom EE 33 g1s E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 11 x 7 E11), (U_atom EE 37 dus E37) by lia. pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 11 12 x n E11 E12), (U_atom EE 38 des E38) by lia. pose proof (Z.div_mod (x + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 dus E37), (U_atom EE 39 gus E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 des E38), (U_atom EE 40 ges E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma entS2H : forall b1, 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1s) = Some b1 -> saddr_ok (x + n - 1) b1 ->
st_ok tfibsegs (Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) ssS2H (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 dus) by (apply (EnvS_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 des) by (apply (EnvS_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E10.
pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as E12.
fold EE in E2, E10, E11, E12.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssS2H. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0s; g1s; b1; 0; 0; dus; des; gus; ges])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply entS_stk | apply Forall_cons; [| apply Forall_cons; [| apply entS_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) x n g0s HRAX ltac:(lia) Hx0). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Nat.add].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1s _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkS, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N Nat.add]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold MC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E12, E32, E33, E34, E37, E38, E39, E40, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok Nat.add]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 11 x E11), (U_atom EE 32 g0s E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 11 12 x n E11 E12), (U_atom EE 33 g1s E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 11 x 7 E11), (U_atom EE 37 dus E37) by lia. pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 11 12 x n E11 E12), (U_atom EE 38 des E38) by lia. pose proof (Z.div_mod (x + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 dus E37), (U_atom EE 39 gus E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 des E38), (U_atom EE 40 ges E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma pathS2L : 64 < n -> x + n <= kLowMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0s) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1s) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (entS2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q2L_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2L_e0 13) (RG q2L_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG q2L_e1 18) HS2 (br_end_low EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2L_e2 8) (RG q2L_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Lz_e0 19) (RG q2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Lz_e1 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Lz_e1 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Lz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Lz_e1 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Lz_e1 1) = Z_to_bv 64 347520).
{ change (sv_denot EE (RG q2Lz_e1 1)) with (sv_denot EE (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Lz_e1)).
{ cbn [ss_mem q2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Lz_e1 ms6 _ 56 (ss_mem q2Lz_e1) (gus + SB) (ges - gus) (sp0 - 2208) 347520 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS7 r_q2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE' q2Lz_e2 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG q2Ln_e0 12) (RG q2Ln_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Ln_e1 19) (RG q2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Ln_e2 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Ln_e2 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Ln_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Ln_e2 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Ln_e2 1) = Z_to_bv 64 347520).
{ change (sv_denot EE (RG q2Ln_e2 1)) with (sv_denot EE (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Ln_e2)).
{ cbn [ss_mem q2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Ln_e2 ms7 _ 56 (ss_mem q2Ln_e2) (gus + SB) (ges - gus) (sp0 - 2208) 347520 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS8 r_q2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. split; [reflexivity|]. exists ms9, mat9. split; [reflexivity|].
apply (midS EE' q2Ln_e3 ms9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2Lo_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2Lo_e0 10) (RG q2Lo_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2LoC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q2LoC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma pathS2H : 64 < n -> kHighMemBeg <= x /\ x + n <= kHighMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn64 Hrg. set (QQ := MIDQ).
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bxn & Bpres & BM).
unfold cfg_at. change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold MC_SCR, MC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0s /\ 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; split; [apply Z.div_pos; lia | pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1s < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) x n HRAX ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gus <= x + 7 < 8 * gus + 8 /\ dus = 8 * gus) by (subst gus dus; pose proof (Z.div_mod (x + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ges <= x + n < 8 * ges + 8 /\ des = 8 * ges) by (subst ges des; pose proof (Z.div_mod (x + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)); lia).
set (EE := Env [g0s; g1s; b1; 0; 0; dus; des; gus; ges]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply EnvS_reg; assumption).
pose proof (EnvS2 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE2. pose proof (EnvS10 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE10. pose proof (EnvS11 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE11. pose proof (EnvS12 [g0s; g1s; b1; 0; 0; dus; des; gus; ges]) as EE12. fold EE in EE2, EE10, EE11, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0s) by (apply (EnvS_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1s) by (apply (EnvS_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (EnvS_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gus) by (apply (EnvS_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ges) by (apply (EnvS_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0s) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1s) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (entS2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
assert (CONT : forall msq matq, st_ok tfibsegs EE q2H_c (restrict H msq) ->
(forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem msq z = mem z) ->
(forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem msq z <> None) ->
SRr tfibsegs W (mkCfg msq (with_vm_backing (m_vm_lazy md) matq md)) QQ).
{ intros ms0 mat0 HSc MEQ0' PSL0'. clear MEQ0 PSL0. rename MEQ0' into MEQ0. rename PSL0' into PSL0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HSc r_q2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG q2H_e0 13) (RG q2H_e0 12) HS1 (br_ovf_false EE 11 12 x n EE11 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG q2H_e1 18) HS2 (br_end_high EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_q2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2H_e2 8) (RG q2H_e2 18) HS3 (br_beg_lt_end EE 11 12 x n EE11 EE12 Hx0 ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_q2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Hz_e0 19) (RG q2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Hz_e1 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Hz_e1 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Hz_e1 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Hz_e1 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Hz_e1 1) = Z_to_bv 64 347520).
{ change (sv_denot EE (RG q2Hz_e1 1)) with (sv_denot EE (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Hz_e1)).
{ cbn [ss_mem q2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Hz_e1 ms6 _ 56 (ss_mem q2Hz_e1) (gus + SB) (ges - gus) (sp0 - 2208) 347520 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ7 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold MC_SCR in *; lia). apply MEQ6. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold MC_SCR, MC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS7 r_q2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. split; [reflexivity|]. exists ms8, mat8. split; [reflexivity|].
apply (midS EE' q2Hz_e2 ms8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG q2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_q2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG q2Hn_e0 12) (RG q2Hn_e0 11) HS5 (rp_blt_last EE 11 12 34 x n b1 EE11 EE12 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_q2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG q2Hn_e1 19) (RG q2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_q2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 2208 - 8 <= z < sp0 - 2208 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold MC_SCR, MC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gus + SB <= a < gus + SB + (ges - gus) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold MC_STK, MC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) x n (a - SB) HRAX); [unfold SB in *; lia | exact Hx0]. }
assert (R10 : sv_denot EE (RG q2Hn_e2 10) = Z_to_bv 64 (gus + SB)).
{ change (sv_denot EE (RG q2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG q2Hn_e2 11) = Z_to_bv 64 (ges - gus)).
{ change (sv_denot EE (RG q2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gus ges E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG q2Hn_e2 2) = Z_to_bv 64 (sp0 - 2208)).
{ change (sv_denot EE (RG q2Hn_e2 2)) with (sv_denot EE (SOff 2 (-2208))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG q2Hn_e2 1) = Z_to_bv 64 347520).
{ change (sv_denot EE (RG q2Hn_e2 1)) with (sv_denot EE (SLit 347520)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 2208 - 8 \/ sp0 - 2208 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem q2Hn_e2)).
{ cbn [ss_mem q2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold MC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE q2Hn_e2 ms7 _ 56 (ss_mem q2Hn_e2) (gus + SB) (ges - gus) (sp0 - 2208) 347520 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 347520 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (MEQ8 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold MC_SCR in *; lia). apply MEQ7. unfold MC_SCR, MC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold MC_SCR, MC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' MC_MID _ _ _ _ _ HS8 r_q2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - MC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. split; [reflexivity|]. exists ms9, mat9. split; [reflexivity|].
apply (midS EE' q2Hn_e3 ms9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold MC_SCR, MC_STK in *. lia.
- intros a Ha. unfold MC_SCR, MC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
}
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_q2Ho_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG q2Ho_e0 10) (RG q2Ho_e0 11) HS1 (eq_trans (br_eq_atoms EE 10 11 d x EE10 EE11 ltac:(lia) ltac:(lia)) (proj2 (Z.eqb_eq _ _) (eq_sym HSAME)))) as HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_q2HoC_0)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MC_STK, MC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - MC_SCR <= bv_unsigned z < sp0 - MC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MC_STK, MC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_dropc EE _ _ HS2) as HSq. rewrite q2HoC_canon in HSq. exact (CONT ms2 mat2 HSq MEQ2 PSL2).
Qed.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. lia. Qed.
Lemma pathD : forall ms0 mat0, MIDP ms0 -> 0 < n -> SRr tfibsegs W (mkCfg ms0 (with_vm_backing (m_vm_lazy md) mat0 md)) POSTc.
Proof.
intros ms0 mat0 HM Hn0. destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by lia.
assert (Hg0 : 8 * g0d <= d < 8 * g0d + 8) by (subst g0d; pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1d <= d + n - 1 < 8 * g1d + 8) by (subst g1d; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
destruct (t_cases (g1d - g0d) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply pathD1_0 | apply pathD1_1 | apply pathD1_2 | apply pathD1_3 | apply pathD1_4 | apply pathD1_5 | apply pathD1_6 | apply pathD1_7 | apply pathD1_8]; assumption.
- destruct HAM as [HL|HH]; [apply pathD2L; [exact HM | lia | exact HL] | apply pathD2H; [exact HM | lia | exact HH]].
Qed.
Lemma pathS : 0 < n -> SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) MIDQ.
Proof.
intros Hn0. destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hn64 : 1 <= n <= 64) by lia.
assert (Hg0 : 8 * g0s <= x < 8 * g0s + 8) by (subst g0s; pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1s <= x + n - 1 < 8 * g1s + 8) by (subst g1s; pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
destruct (t_cases (g1s - g0s) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply pathS1_0 | apply pathS1_1 | apply pathS1_2 | apply pathS1_3 | apply pathS1_4 | apply pathS1_5 | apply pathS1_6 | apply pathS1_7 | apply pathS1_8]; assumption.
- destruct HAMX as [HL|HH]; [apply pathS2L; [lia | exact HL] | apply pathS2H; [lia | exact HH]].
Qed.
Theorem acpy_same_srr : SRr tfibsegs W (cfg_at tfibsegs MC_ENTRY regs mem md) POSTc.
Proof using All.
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
- assert (HD0 : d + n <= x \/ x + n <= d) by (left; lia).
exact (AE6k.pathS0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM Hx0 Hxn HSRC HD0 HAMX Hn0).
- eapply SRr_bind; [apply pathS; lia|].
cbv beta. intros W1 c1 _ (-> & ms & mat & -> & HM). apply (pathD ms mat HM). lia.
Qed.
End l.
Theorem acpy_same_icpt : forall B, AR_laws tfibsegs B -> TfibSyms B -> acpy_same_realizes tfibsegs B 0x52090.
Proof.
intros B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL (Hx0 & Hxn & HSRC & HSAME & HAMX & HRAX & HHULLX).
exact (acpy_same_srr B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM HRA HHULL Hx0 Hxn HSRC HSAME HAMX HRAX HHULLX).
Qed.
End f.
