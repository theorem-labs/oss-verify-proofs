(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0j3 X0hi X0hh X0hn X0j0 X0hb X0il X0gp X0h2 X0j4 X0hf
X0id X0fy X0fg X0da X0g4 X0d8 X0fq X0f0 X0e4 X0e8 X0d9 X0e5
X0de X0dk X0dq X0fd X0fc X0fe X0c7.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X19m X183 X182 X188 X19k X17w X196 X17a X17n X19n X180 X18y X16j X161 X13v X16p X13t X16b X15l X14p X14t X13u X14q X13z X145 X14b X15y X15x X15z X12s.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X145 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15z OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12s.
Import ListNotations.
Open Scope Z_scope.

Lemma rz_le2048 : forall n, rz_size n <= 2048.
Proof. intros n. unfold rz_size, rz_log. repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia. Qed.

Lemma pq_fit : forall Σ c i n, rt_wf0 Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
1 <= n /\ rz_size n + n <= ClassSize c.
Proof.
intros Σ c i n HW Hc Hi. pose proof HW as (_ & (HR & _) & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi)) as (X1 & X2 & _). split; assumption.
Qed.

Lemma pq_in_prb : forall Σ c i n, rt_wf0 Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
l_PRB (lay Σ) <= p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 < l_PRB (lay Σ) + 0x2000011000.
Proof.
intros Σ c i n HW Hc Hi. pose proof (geo_of_wf0 Σ HW) as HG.
pose proof (fk_slot Σ HG c i _ Hc Hi) as (Y1 & Y2 & Y3 & _). pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
pose proof (rz_facts n) as (_ & R2). pose proof (rz_le2048 n) as R3. pose proof (ClassSize_range c Hc) as ((CS1 & _) & _).
unfold rb, kUserCap in *. unfold p_abeg in *. clear - Y1 Y2 Y3 P3 P4 R2 R3 Hc CS1. lia.
Qed.

Lemma hdr_unique : forall Σ M n n', rt_wf0 Σ -> qent_ok Σ (M, n) -> qent_ok Σ (M, n') -> n = n'.
Proof.
intros Σ M n n' HW H1 H2. pose proof (geo_of_wf0 Σ HW) as HG.
destruct H1 as [(c & i & Hc & Hi & E)|(t & Ht & Htq & Htn & Et)]; destruct H2 as [(c' & i' & Hc' & Hi' & E')|(t' & Ht' & Htq' & Htn' & Et')];
cbn [fst snd] in *.
- destruct (Z.eq_dec c c') as [<-|Hcc]; [destruct (Nat.eq_dec i i') as [<-|Hii]|].
+ rewrite Hi in Hi'. injection Hi' as <-. reflexivity.
+ exfalso. pose proof (g_slot_apart Σ HG c i c i' _ _ Hc Hc Hi Hi' (or_intror Hii)) as Y.
pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (pq_fit Σ c i' n' HW Hc Hi') as (G1 & G2).
pose proof (rz_facts n) as (_ & R1). pose proof (rz_facts n') as (_ & R1'). clear - Y E E' F1 F2 G1 G2 R1 R1'. lia.
+ exfalso. pose proof (g_slot_apart Σ HG c i c' i' _ _ Hc Hc' Hi Hi' (or_introl Hcc)) as Y.
pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (pq_fit Σ c' i' n' HW Hc' Hi') as (G1 & G2).
pose proof (rz_facts n) as (_ & R1). pose proof (rz_facts n') as (_ & R1'). clear - Y E E' F1 F2 G1 G2 R1 R1'. lia.
- exfalso. pose proof (pq_in_prb Σ c i n HW Hc Hi) as PE. destruct (In_nth_error _ _ Ht') as (k' & Hk').
pose proof (fk_map Σ HG k' t' Hk') as (X1 & _ & _ & _ & XP & _). pose proof (smsz_room (s_n t') ltac:(lia)) as SR.
unfold apart in XP. clear - PE XP SR X1 E Et'. lia.
- exfalso. pose proof (pq_in_prb Σ c' i' n' HW Hc' Hi') as PE. destruct (In_nth_error _ _ Ht) as (k & Hk).
pose proof (fk_map Σ HG k t Hk) as (X1 & _ & _ & _ & XP & _). pose proof (smsz_room (s_n t) ltac:(lia)) as SR.
unfold apart in XP. clear - PE XP SR X1 E' Et. lia.
- destruct (In_nth_error _ _ Ht) as (k & Hk). destruct (In_nth_error _ _ Ht') as (k' & Hk').
destruct (Nat.eq_dec k k') as [<-|Hkk]; [rewrite Hk in Hk'; injection Hk' as <-; rewrite <- Htn, <- Htn'; reflexivity|].
exfalso. pose proof (fk_map Σ HG k t Hk) as (X1 & _ & _ & _ & _ & _ & _ & _ & _ & X10). pose proof (X10 k' t' Hk' ltac:(intros E; exact (Hkk (eq_sym E)))) as Y.
pose proof (smsz_room (s_n t) ltac:(lia)) as SR. pose proof (fk_map Σ HG k' t' Hk') as (Y1 & _).
pose proof (smsz_room (s_n t') ltac:(lia)) as SR'. unfold apart in Y. clear - Y SR SR' X1 Y1 Et Et'. lia.
Qed.

Lemma pend_refill_e : forall Σ1 M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> pend_e (refillΣ Σ1 24) M n.
Proof.
intros Σ1 M n HW (QE & FR & RC1 & RC2). split; [|split; [exact FR|split]].
- destruct QE as [(c & i & Hc & Hi & E)|X]; [left|right; exact X].
exists c, i. split; [exact Hc|]. split; [exact (rfs_keep Σ1 24 ltac:(lia) HW c i _ Hi) | exact E].
- intros c' i' n' Hc' Hi' Hne. destruct (rfs_st Σ1 24 ltac:(lia) HW c' i' _ Hi') as [Hi0|(_ & E & _)]; [exact (RC1 c' i' n' Hc' Hi0 Hne) | discriminate E].
- exact RC2.
Qed.

Lemma pend_room_e : forall Σ1 M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> ca Σ1 24 = [] -> refill_room Σ1 24.
Proof.
intros Σ1 M n HW (QE & FR & RC1 & RC2) HCA. pose proof (geo_of_wf0 Σ1 HW) as HG.
apply (carved_room_gen Σ1 24 (Z.to_nat ((M - rb (l_SB (lay Σ1)) 24) / 8192)) HW ltac:(lia) HCA).
intros i' n' Hi' Hne. apply (RC1 24 i' n' ltac:(lia) Hi'). intros E. apply Hne.
pose proof (pq_fit Σ1 24 i' n' HW ltac:(lia) Hi') as (F1 & F2). change (ClassSize 24) with 8192 in F2.
pose proof (rz_facts n') as (_ & R1). rewrite <- E. unfold p_abeg, rb. change (ClassSize 24) with 8192.
replace (l_SB (lay Σ1) + 24 * 2 ^ 32 + Z.of_nat i' * 8192 + rz_size n' - 16 - (l_SB (lay Σ1) + 24 * 2 ^ 32))
with (rz_size n' - 16 + Z.of_nat i' * 8192) by ring.
rewrite Z.div_add by lia. rewrite Z.div_small by (clear - F1 F2 R1; lia). rewrite Z.add_0_l. symmetry. apply Nat2Z.id.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma rz_le2048 : forall n, rz_size n <= 2048.
Proof. intros n. unfold rz_size, rz_log. repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; lia. Qed.

Lemma pq_fit : forall Σ c i n, rt_wf0 Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
1 <= n /\ rz_size n + n <= ClassSize c.
Proof.
intros Σ c i n HW Hc Hi. pose proof HW as (_ & (HR & _) & _). pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi)) as (X1 & X2 & _). split; assumption.
Qed.

Lemma pq_in_prb : forall Σ c i n, rt_wf0 Σ -> 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkQuar n) ->
l_PRB (lay Σ) <= p_abeg (l_SB (lay Σ)) c i + rz_size n - 16 < l_PRB (lay Σ) + 0x2000011000.
Proof.
intros Σ c i n HW Hc Hi. pose proof (geo_of_wf0 Σ HW) as HG.
pose proof (fk_slot Σ HG c i _ Hc Hi) as (Y1 & Y2 & Y3 & _). pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
pose proof (rz_facts n) as (_ & R2). pose proof (rz_le2048 n) as R3. pose proof (ClassSize_range c Hc) as ((CS1 & _) & _).
unfold rb, kUserCap in *. unfold p_abeg in *. clear - Y1 Y2 Y3 P3 P4 R2 R3 Hc CS1. lia.
Qed.

Lemma hdr_unique : forall Σ M n n', rt_wf0 Σ -> qent_ok Σ (M, n) -> qent_ok Σ (M, n') -> n = n'.
Proof.
intros Σ M n n' HW H1 H2. pose proof (geo_of_wf0 Σ HW) as HG.
destruct H1 as [(c & i & Hc & Hi & E)|(t & Ht & Htq & Htn & Et)]; destruct H2 as [(c' & i' & Hc' & Hi' & E')|(t' & Ht' & Htq' & Htn' & Et')];
cbn [fst snd] in *.
- destruct (Z.eq_dec c c') as [<-|Hcc]; [destruct (Nat.eq_dec i i') as [<-|Hii]|].
+ rewrite Hi in Hi'. injection Hi' as <-. reflexivity.
+ exfalso. pose proof (g_slot_apart Σ HG c i c i' _ _ Hc Hc Hi Hi' (or_intror Hii)) as Y.
pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (pq_fit Σ c i' n' HW Hc Hi') as (G1 & G2).
pose proof (rz_facts n) as (_ & R1). pose proof (rz_facts n') as (_ & R1'). clear - Y E E' F1 F2 G1 G2 R1 R1'. lia.
+ exfalso. pose proof (g_slot_apart Σ HG c i c' i' _ _ Hc Hc' Hi Hi' (or_introl Hcc)) as Y.
pose proof (pq_fit Σ c i n HW Hc Hi) as (F1 & F2). pose proof (pq_fit Σ c' i' n' HW Hc' Hi') as (G1 & G2).
pose proof (rz_facts n) as (_ & R1). pose proof (rz_facts n') as (_ & R1'). clear - Y E E' F1 F2 G1 G2 R1 R1'. lia.
- exfalso. pose proof (pq_in_prb Σ c i n HW Hc Hi) as PE. destruct (In_nth_error _ _ Ht') as (k' & Hk').
pose proof (fk_map Σ HG k' t' Hk') as (X1 & _ & _ & _ & XP & _). pose proof (smsz_room (s_n t') ltac:(lia)) as SR.
unfold apart in XP. clear - PE XP SR X1 E Et'. lia.
- exfalso. pose proof (pq_in_prb Σ c' i' n' HW Hc' Hi') as PE. destruct (In_nth_error _ _ Ht) as (k & Hk).
pose proof (fk_map Σ HG k t Hk) as (X1 & _ & _ & _ & XP & _). pose proof (smsz_room (s_n t) ltac:(lia)) as SR.
unfold apart in XP. clear - PE XP SR X1 E' Et. lia.
- destruct (In_nth_error _ _ Ht) as (k & Hk). destruct (In_nth_error _ _ Ht') as (k' & Hk').
destruct (Nat.eq_dec k k') as [<-|Hkk]; [rewrite Hk in Hk'; injection Hk' as <-; rewrite <- Htn, <- Htn'; reflexivity|].
exfalso. pose proof (fk_map Σ HG k t Hk) as (X1 & _ & _ & _ & _ & _ & _ & _ & _ & X10). pose proof (X10 k' t' Hk' ltac:(intros E; exact (Hkk (eq_sym E)))) as Y.
pose proof (smsz_room (s_n t) ltac:(lia)) as SR. pose proof (fk_map Σ HG k' t' Hk') as (Y1 & _).
pose proof (smsz_room (s_n t') ltac:(lia)) as SR'. unfold apart in Y. clear - Y SR SR' X1 Y1 Et Et'. lia.
Qed.

Lemma pend_refill_e : forall Σ1 M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> pend_e (refillΣ Σ1 24) M n.
Proof.
intros Σ1 M n HW (QE & FR & RC1 & RC2). split; [|split; [exact FR|split]].
- destruct QE as [(c & i & Hc & Hi & E)|X]; [left|right; exact X].
exists c, i. split; [exact Hc|]. split; [exact (rfs_keep Σ1 24 ltac:(lia) HW c i _ Hi) | exact E].
- intros c' i' n' Hc' Hi' Hne. destruct (rfs_st Σ1 24 ltac:(lia) HW c' i' _ Hi') as [Hi0|(_ & E & _)]; [exact (RC1 c' i' n' Hc' Hi0 Hne) | discriminate E].
- exact RC2.
Qed.

Lemma pend_room_e : forall Σ1 M n, rt_wf0 Σ1 -> pend_e Σ1 M n -> ca Σ1 24 = [] -> refill_room Σ1 24.
Proof.
intros Σ1 M n HW (QE & FR & RC1 & RC2) HCA. pose proof (geo_of_wf0 Σ1 HW) as HG.
apply (carved_room_gen Σ1 24 (Z.to_nat ((M - rb (l_SB (lay Σ1)) 24) / 8192)) HW ltac:(lia) HCA).
intros i' n' Hi' Hne. apply (RC1 24 i' n' ltac:(lia) Hi'). intros E. apply Hne.
pose proof (pq_fit Σ1 24 i' n' HW ltac:(lia) Hi') as (F1 & F2). change (ClassSize 24) with 8192 in F2.
pose proof (rz_facts n') as (_ & R1). rewrite <- E. unfold p_abeg, rb. change (ClassSize 24) with 8192.
replace (l_SB (lay Σ1) + 24 * 2 ^ 32 + Z.of_nat i' * 8192 + rz_size n' - 16 - (l_SB (lay Σ1) + 24 * 2 ^ 32))
with (rz_size n' - 16 + Z.of_nat i' * 8192) by ring.
rewrite Z.div_add by lia. rewrite Z.div_small by (clear - F1 F2 R1; lia). rewrite Z.add_0_l. symmetry. apply Nat2Z.id.
Qed.
