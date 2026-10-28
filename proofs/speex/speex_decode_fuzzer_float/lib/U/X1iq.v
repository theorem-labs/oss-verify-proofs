(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0om X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1ik X1ij X1im X1ip.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8).
+ rewrite Z.mod_pow2_bits_low, Z.lor_spec, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
+ rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (testbit_high_false _ 8); lia.
- replace (Z.lor (bv_unsigned b) (bytes_le_to_Z bs ≪ 8) ≫ 8) with (bytes_le_to_Z bs); [exact IH|].
rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. cbn [Z.sub Z.pos_sub]. rewrite Z.shiftl_0_r.
rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.

Lemma bytes_regroup4 : forall n (bs : list byte), length bs = (4 * n)%nat -> exists ws, u32s ws = bs /\ length ws = n.
Proof.
induction n as [|n IH]; intros bs H.
- exists []. destruct bs; [split; reflexivity| cbn in H; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 bs']]]]; cbn in H; try lia.
destruct (IH bs' ltac:(lia)) as (ws & E & L).
exists (le_bytes_to_word [b0; b1; b2; b3] :: ws). cbn [u32s length]. rewrite E, L. split; [|reflexivity].
change (b0 :: b1 :: b2 :: b3 :: bs') with ([b0; b1; b2; b3] ++ bs'). f_equal.
unfold le4, le_bytes_to_word. rewrite unsigned_lit.
2:{ pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]). pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as X. cbn [length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia. }
apply (Z_to_le_bytes_of_bytes [b0; b1; b2; b3]).
Qed.

Lemma bytes_regroup8 : forall n (bs : list byte), length bs = (8 * n)%nat -> exists ws, u64s ws = bs /\ length ws = n.
Proof.
induction n as [|n IH]; intros bs H.
- exists []. destruct bs; [split; reflexivity| cbn in H; lia].
- destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 bs']]]]]]]]; cbn in H; try lia.
destruct (IH bs' ltac:(lia)) as (ws & E & L).
exists (le_bytes_to_word [b0; b1; b2; b3; b4; b5; b6; b7] :: ws). cbn [u64s length]. rewrite E, L. split; [|reflexivity].
change (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs') with ([b0; b1; b2; b3; b4; b5; b6; b7] ++ bs'). f_equal.
unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite unsigned_lit.
2:{ pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3; b4; b5; b6; b7]). pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3; b4; b5; b6; b7]) as X. cbn [length Z.of_nat Z.mul Pos.mul Pos.of_succ_nat Pos.succ] in X. lia. }
apply (Z_to_le_bytes_of_bytes [b0; b1; b2; b3; b4; b5; b6; b7]).
Qed.

Lemma u32arr_chunk : forall m A ws n, u32arr rsegs m A ws -> Z.of_nat (length ws) = n ->
rw_cells rsegs m A [CB (Z.to_nat (n * 4)) (u32s ws)].
Proof.
intros m A ws n H Hl. replace (Z.to_nat (n * 4)) with (length (u32s ws)) by (rewrite u32s_length; lia).
apply rw_cells_of_u8arr. destruct H as [HB HW]. split; [exact HB|]. rewrite u32s_length, Nat2Z.inj_mul. exact HW.
Qed.
Lemma u64arr_chunk : forall m A ws n, u64arr rsegs m A ws -> Z.of_nat (length ws) = n ->
rw_cells rsegs m A [CB (Z.to_nat (n * 8)) (u64s ws)].
Proof.
intros m A ws n H Hl. replace (Z.to_nat (n * 8)) with (length (u64s ws)) by (rewrite u64s_length; lia).
apply rw_cells_of_u8arr. destruct H as [HB HW]. split; [exact HB|]. rewrite u64s_length, Nat2Z.inj_mul. exact HW.
Qed.
Lemma chunk_u32arr : forall m A ws junk n k, rw_cells rsegs m A [CB k (u32s ws ++ junk)] -> k = Z.to_nat (n * 4) -> 0 <= n ->
(length ws <= Z.to_nat n)%nat -> exists ws', u32arr rsegs m A (ws ++ ws') /\ Z.of_nat (length (ws ++ ws')) = n.
Proof.
intros m A ws junk n k H -> Hn Hle. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _]. rewrite app_length, u32s_length in LEN.
destruct (bytes_regroup4 (Z.to_nat n - length ws) junk ltac:(lia)) as (ws' & E & L).
exists ws'. split.
- apply u8arr_of_rw_cells in H. rewrite <- E, <- u32s_app in H. destruct H as [HB HW]. split; [exact HB|].
rewrite u32s_length, Nat2Z.inj_mul in HW. exact HW.
- rewrite app_length. lia.
Qed.
Lemma chunk_u64arr : forall m A ws junk n k, rw_cells rsegs m A [CB k (u64s ws ++ junk)] -> k = Z.to_nat (n * 8) -> 0 <= n ->
(length ws <= Z.to_nat n)%nat -> exists ws', u64arr rsegs m A (ws ++ ws') /\ Z.of_nat (length (ws ++ ws')) = n.
Proof.
intros m A ws junk n k H -> Hn Hle. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [LEN _]. rewrite app_length, u64s_length in LEN.
destruct (bytes_regroup8 (Z.to_nat n - length ws) junk ltac:(lia)) as (ws' & E & L).
exists ws'. split.
- apply u8arr_of_rw_cells in H. rewrite <- E, <- u64s_app in H. destruct H as [HB HW]. split; [exact HB|].
rewrite u64s_length, Nat2Z.inj_mul in HW. exact HW.
- rewrite app_length. lia.
Qed.

Lemma bptr_eqb_refl : forall p : bptr, bptr_eqb p p = true.
Proof. intros p. unfold bptr_eqb, aptr_eqb. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.
Lemma lb_remove_neq : forall p LB b, In b (lb_remove p LB) -> blk_id b <> p.
Proof.
intros p LB b H E. unfold lb_remove in H. induction LB as [|x LB IH]; cbn in H; [exact H|].
destruct (bptr_eqb (blk_id x) p) eqn:BX; cbn in H.
- apply IH. exact H.
- destruct H as [->|H]; [| apply IH; exact H]. rewrite E, bptr_eqb_refl in BX. discriminate.
Qed.

Lemma stream_blocks_newlacing : forall LB (os : stream_st bptr) Bd L Gv pl q L' n' ls' g,
stream_blocks LB os Bd L Gv -> os_lacing_vals os = Some pl -> os_granule_vals os = g ->
List.NoDup (q :: map blk_id (lb_remove pl LB)) ->
stream_blocks ((q, L', n') :: lb_remove pl LB)
(set_blocks os (os_body_data os) (os_body_storage os) (Some q) g ls') Bd L' Gv.
Proof.
intros LB os Bd L Gv pl q L' n' ls' g SB Hpl <- ND.
apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
first [ sf_destruct 6%nat SB as SB1 SB2 SB3 D12 D13 D23 | sf_fb; destruct SB as (SB1 & SB2 & SB3 & D12 & D13 & D23) ]. unfold stream_blocks. destruct os; cbn in *. subst.
split. { destruct os_body_data as [p1|]; [| exact SB1]. destruct SB1 as [n1 IN1]. exists n1. right.
apply lb_remove_keep; [exact IN1| cbn; intros EQ; eapply D12; [reflexivity| reflexivity| exact EQ]]. }
split; [exists n'; left; reflexivity|].
split. { destruct os_granule_vals as [p3|]; [| exact SB3]. destruct SB3 as [n3 IN3]. exists n3. right.
apply lb_remove_keep; [exact IN3| cbn; intros EQ; eapply D23; [reflexivity| reflexivity| symmetry; exact EQ]]. }
split. { intros p q' -> Hq ->. injection Hq as ->. apply NI. destruct SB1 as [n1 IN1].
apply (in_map_blk_id (q', Bd, n1)). apply lb_remove_keep; [exact IN1| cbn; intros EQ; eapply D12; [reflexivity| reflexivity| exact EQ]]. }
split; [exact D13|].
intros p q' Hp -> ->. injection Hp as ->. apply NI. destruct SB3 as [n3 IN3].
apply (in_map_blk_id (q', Gv, n3)). apply lb_remove_keep; [exact IN3| cbn; intros EQ; eapply D23; [reflexivity| reflexivity| symmetry; exact EQ]].
Qed.

Lemma stream_blocks_newgranule : forall LB (os : stream_st bptr) Bd L Gv pg q Gv' n' ls' l,
stream_blocks LB os Bd L Gv -> os_granule_vals os = Some pg -> os_lacing_vals os = l ->
List.NoDup (q :: map blk_id (lb_remove pg LB)) ->
stream_blocks ((q, Gv', n') :: lb_remove pg LB)
(set_blocks os (os_body_data os) (os_body_storage os) l (Some q) ls') Bd L Gv'.
Proof.
intros LB os Bd L Gv pg q Gv' n' ls' l SB Hpg <- ND.
apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
first [ sf_destruct 6%nat SB as SB1 SB2 SB3 D12 D13 D23 | sf_fb; destruct SB as (SB1 & SB2 & SB3 & D12 & D13 & D23) ]. unfold stream_blocks. destruct os; cbn in *. subst.
split. { destruct os_body_data as [p1|]; [| exact SB1]. destruct SB1 as [n1 IN1]. exists n1. right.
apply lb_remove_keep; [exact IN1| cbn; intros EQ; eapply D13; [reflexivity| reflexivity| exact EQ]]. }
split. { destruct os_lacing_vals as [p2|]; [| exact SB2]. destruct SB2 as [n2 IN2]. exists n2. right.
apply lb_remove_keep; [exact IN2| cbn; intros EQ; eapply D23; [reflexivity| reflexivity| exact EQ]]. }
split; [exists n'; left; reflexivity|].
split; [exact D12|].
split. { intros p q' -> Hq ->. injection Hq as ->. apply NI. destruct SB1 as [n1 IN1].
apply (in_map_blk_id (q', Bd, n1)). apply lb_remove_keep; [exact IN1| cbn; intros EQ; eapply D13; [reflexivity| reflexivity| exact EQ]]. }
intros p q' -> Hq ->. injection Hq as ->. apply NI. destruct SB2 as [n2 IN2].
apply (in_map_blk_id (q', L, n2)). apply lb_remove_keep; [exact IN2| cbn; intros EQ; eapply D23; [reflexivity| reflexivity| exact EQ]].
Qed.

Lemma clear_LB_after_newlacing : forall LB (os : stream_st bptr) Bd L Gv (pl pg ql : bptr) L' n bs ls,
stream_blocks LB os Bd L Gv -> os_lacing_vals os = Some pl ->
List.NoDup (map blk_id ((ql, L', n) :: lb_remove pl LB)) ->
stream_clear_LB ((ql, L', n) :: lb_remove pl LB) (set_blocks os (os_body_data os) bs (Some ql) (Some pg) ls)
= lb_remove pg (lb_remove pl (lb_remove_opt (os_body_data os) LB)).
Proof.
intros LB os Bd L Gv pl pg ql L' n bs ls SB Hpl ND1.
unfold stream_clear_LB. replace (os_granule_vals (set_blocks os (os_body_data os) bs (Some ql) (Some pg) ls)) with (Some pg) by (destruct os; reflexivity).
replace (os_lacing_vals (set_blocks os (os_body_data os) bs (Some ql) (Some pg) ls)) with (Some ql) by (destruct os; reflexivity).
replace (os_body_data (set_blocks os (os_body_data os) bs (Some ql) (Some pg) ls)) with (os_body_data os) by (destruct os; reflexivity).
cbn [lb_remove_opt]. f_equal.
cbn in ND1. inversion ND1 as [|x l NI NDr]; subst.
pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as SBb _ _ D12 _ _ | sf_fb; destruct sfP_ as (SBb & _ & _ & D12 & _ & _) ].
destruct (os_body_data os) as [pbo|].
- destruct SBb as [nb HINb]. assert (NEbl : pbo <> pl) by (eapply D12; [reflexivity| exact Hpl]).
assert (NEbq : pbo <> ql).
{ intros ->. apply NI. apply (in_map blk_id) in HINb. unfold blk_id in HINb at 1. cbn [fst] in HINb.
apply in_map_iff in HINb. destruct HINb as (bq & Eq & Hbq). rewrite <- Eq. apply in_map. apply lb_remove_keep; [exact Hbq| rewrite Eq; congruence]. }
cbn [lb_remove_opt]. rewrite (lbr_hd_other pbo) by (cbn; congruence). rewrite lbr_hd_same.
rewrite (lbr_notin ql).
2:{ intros HI. apply NI. apply in_map_iff in HI. destruct HI as (bq & Eq & Hbq). rewrite <- Eq. apply in_map. eapply lb_remove_sub. exact Hbq. }
apply lbr_comm.
- cbn [lb_remove_opt]. rewrite lbr_hd_same. rewrite (lbr_notin ql) by exact NI. reflexivity.
Qed.

Section LEXP.
Context {RCEIL : RunCeiling}.
Variable rhdr_known : PState -> bptr -> Prop.
Hypothesis rhdr_known_indep : forall s s' p, rhdr_known s p -> rhdr_known s' p.
Hypothesis HR : ogg_realloc_stmt rhdr_known.
Hypothesis HF : rfree_stmt.

Definition lacing_expand_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (os : stream_st bptr) (pl pg : bptr) (needed A Bd L Gv lo B : Z) (hdr : list byte)
(lws gws : list word) (m : mem)
(r : Z * stream_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (fst r)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with (rc, os') =>
(rc = 0 /\ exists (ql qg : bptr) (L' Gv' : Z) (ljunk gjunk : list word) (LB' : list block),
os' = set_blocks os (os_body_data os) (os_body_storage os) (Some ql) (Some qg) (os_lacing_storage os')
/\ os_lacing_storage os <= os_lacing_storage os' /\ os_lacing_fill os + needed < os_lacing_storage os'
/\ (os_lacing_storage os' = os_lacing_storage os \/ os_lacing_storage os' * 8 < MMAP_THRESHOLD)
/\ Z.of_nat (length (lws ++ ljunk)) = os_lacing_storage os' /\ Z.of_nat (length (gws ++ gjunk)) = os_lacing_storage os'
/\ RHEAP s' LB' m' /\ (forall b, In b (lb_remove pg (lb_remove pl LB)) -> In b LB')
/\ In (ql, L', os_lacing_storage os' * 4) LB' /\ In (qg, Gv', os_lacing_storage os' * 8) LB'
/\ stream_blocks LB' os' Bd L' Gv' /\ rhdr_known s' ql /\ rhdr_known s' qg
/\ (forall b, In b LB -> blk_id b <> pl -> blk_id b <> pg -> blk_id b <> ql /\ blk_id b <> qg)
/\ rblock_range L' (os_lacing_storage os' * 4) /\ rblock_range Gv' (os_lacing_storage os' * 8)
/\ cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 408)] (lb_remove pg (lb_remove pl LB)) (bv_unsigned sp) m m'
/\ rw_cells rsegs m' A (stream_cells Bd L' Gv' hdr os')
/\ u32arr rsegs m' L' (lws ++ ljunk) /\ u64arr rsegs m' Gv' (gws ++ gjunk)
/\ Permutation LB' ((ql, L', os_lacing_storage os' * 4) :: (qg, Gv', os_lacing_storage os' * 8) :: lb_remove pg (lb_remove pl LB)))
\/ (rc = -1 /\ os' = stream_zero /\ exists LB', RHEAP s' LB' m'
/\ (forall b, In b LB' -> In b LB)
/\ (forall b, In b LB -> Some (blk_id b) <> os_body_data os -> blk_id b <> pl -> blk_id b <> pg -> In b LB')
/\ cmod [(bv_unsigned sp - 32, bv_unsigned sp); (A, A + 408)] LB' (bv_unsigned sp) m m'
/\ rw_cells rsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero)
/\ LB' = lb_remove pg (lb_remove pl (lb_remove_opt (os_body_data os) LB)))
end.

#[using="rhdr_known_indep HR HF"] Lemma os_lacing_expand_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (os : stream_st bptr) (pl pg : bptr) (needed A Bd L Gv lo B : Z) (hdr : list byte)
(lws gws : list word) (errv : word),
RHEAP s LB m -> stream_blocks LB os Bd L Gv -> length hdr = 284%nat ->
os_lacing_vals os = Some pl -> os_granule_vals os = Some pg ->
In (pl, L, os_lacing_storage os * 4) LB -> In (pg, Gv, os_lacing_storage os * 8) LB ->
rhdr_known s pl -> rhdr_known s pg ->
u32arr rsegs m L lws -> u64arr rsegs m Gv gws ->
Z.of_nat (length lws) = os_lacing_storage os -> Z.of_nat (length gws) = os_lacing_storage os ->
0 <= needed < 2^59 -> 0 <= os_lacing_storage os < 2^59 -> 0 <= os_lacing_fill os < 2^63 ->
os_lacing_fill os <= os_lacing_storage os -> 1024 <= os_lacing_storage os ->
(os_lacing_storage os - needed <= os_lacing_fill os -> (os_lacing_storage os + needed + 32) * 8 < MMAP_THRESHOLD) ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - OGG_REALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 needed -> rw_cells rsegs m A (stream_cells Bd L Gv hdr os) ->
implM rsegs (os_lacing_expand raw_realloc raw_free os needed) s
(lacing_expand_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB os pl pg needed A Bd L Gv lo B hdr lws gws m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP SB HL Hpl Hpg HINl HINg HKl HKg ARRl ARRg LENl LENg Hnd Hls Hlf Hfs HBIG Hbound AUX SPB SPA AB ST CEIL LO ERR MI TP -> -> OS.
unfold A_os_lacing_expand. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold OGG_REALLOC_STACK in LO.
pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as SB1 SB2 SB3 D12 D13 D23 | sf_fb; destruct sfP_ as (SB1 & SB2 & SB3 & D12 & D13 & D23) ].
assert (NEQ : pl <> pg) by (eapply D23; [exact Hpl| exact Hpg]).
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (RHEAP_block_range_proof _ _ _ _ HP HINl) as BRl. cbn [blk_addr blk_size fst snd] in BRl.
pose proof BRl as sfP_; first [ sf_destruct 5%nat sfP_ as Bl1 Bl2 Bl3 Bl4 Bl5 | sf_fb; destruct sfP_ as (Bl1 & Bl2 & Bl3 & Bl4 & Bl5) ]. unfold alloc_ceiling in Bl4.
pose proof (RHEAP_block_range_proof _ _ _ _ HP HINg) as BRg. cbn [blk_addr blk_size fst snd] in BRg.
pose proof BRg as sfP_; first [ sf_destruct 5%nat sfP_ as Bg1 Bg2 Bg3 Bg4 Bg5 | sf_fb; destruct sfP_ as (Bg1 & Bg2 & Bg3 & Bg4 & Bg5) ]. unfold alloc_ceiling in Bg4.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold os_lacing_expand. unfold implM. iprefix.
carve_frame 32%nat ST.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. if_cases CN1; zify_cond CN1; rewrite !zb_signed_small in CN1 by lia.

2:{ replace (os_lacing_fill os <? os_lacing_storage os - needed) with true by (symmetry; apply Z.ltb_lt; lia).

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
apply evt_done. cbv beta iota. apply impl_ret_ok. apply evt_done. cbn [fst snd].
unfold lacing_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split; [reflexivity|]. split; [reflexivity|].
cbn [fst snd]. left. split; [reflexivity|]. first [ unshelve sf_eexists 7%nat; [ exact (pl) | exact (pg) | exact (L) | exact (Gv) | exact ((@nil word)) | exact ((@nil word)) | exact (LB) | ] | sf_fb; exists pl, pg, L, Gv, (@nil word), (@nil word), LB ].
rewrite !app_nil_r.
split. { rewrite <- Hpl, <- Hpg. destruct os; reflexivity. }
split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [exact LENl|]. split; [exact LENg|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split; [intros b Hb; do 2 apply lb_remove_sub in Hb; exact Hb|].
split; [exact HINl|]. split; [exact HINg|]. split; [exact SB|]. split; [exact HKl|]. split; [exact HKg|].
split; [intros b _ N1 N2; split; [exact N1| exact N2]|].
split; [exact BRl|]. split; [exact BRg|].
split. { apply cmod_of_munch; [exact MU| exact WM]. }
split; [exact OS|].
split; [exact ARRl|]. split; [exact ARRg|].
cbn [os_lacing_storage set_blocks].
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as ND0.
assert (NElg : pl <> pg) by (pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as _ _ _ _ _ D23' | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & D23') ]; eapply D23'; eassumption).
eapply Permutation_trans; [apply (perm_hd_lbr pl L (os_lacing_storage os * 4) LB ND0 HINl)|]. apply perm_skip.
apply perm_hd_lbr; [apply nodup_ids_lbr; exact ND0| apply lb_remove_keep; [exact HINg| cbn; congruence]]. }

replace (os_lacing_fill os <? os_lacing_storage os - needed) with false by (symmetry; apply Z.ltb_ge; lia).
specialize (Hbound ltac:(lia)). unfold MMAP_THRESHOLD in Hbound.

zstep. zstep. zstep. zstep. if_cases CN2; zify_cond CN2.
all: rewrite lxor_ones63 in CN2 by lia; rewrite !zb_signed_small in CN2 by lia.
2:{ exfalso. lia. }
replace (LONG_MAX - needed <? os_lacing_storage os) with false by (symmetry; apply Z.ltb_ge; unfold LONG_MAX; lia).
rewrite Hpl, Hpg.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
replace (os_lacing_storage os + needed + 2^63 <? 18446744073709551583) with true by (symmetry; apply Z.ltb_lt; lia).
replace (os_lacing_storage os + needed <? LONG_MAX - 32) with true by (symmetry; apply Z.ltb_lt; unfold LONG_MAX; lia).
change (Z.b2z true ≪ 5) with 32.
set (n' := os_lacing_storage os + needed + 32).
assert (Hn' : os_lacing_storage os + needed + 32 <= n' /\ n' * 8 < MMAP_THRESHOLD) by (subst n'; unfold MMAP_THRESHOLD; lia).
replace (Z.land n' 18446744073709551615 ≪ 2) with (n' * 4)
by (rewrite Z.shiftl_mul_pow2, land_ones64, Z.mod_small by (unfold MMAP_THRESHOLD in Hn'; lia); reflexivity).
unfold SIZEOF_INT, SIZEOF_INT64.
pose proof (u32arr_chunk _ _ _ _ ARRl LENl) as BLKl.

zstep. apply evt_done.
eapply (realloc_site rhdr_known HR _ _ s LB pl L (os_lacing_storage os * 4) (n' * 4) (bv_unsigned sp + -32) 0x30418 A lo B errv (u32s lws) _ _ gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact BLKl | exact OS | exact FR | exact ERR]
| |- In _ _ => exact HINl
| |- rhdr_known _ _ => exact HKl
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- _ mod 2 = 0 => reflexivity
| |- forall m', _ => idtac
| |- _ => try (unfold OGG_REALLOC_STACK, MMAP_THRESHOLD in *; lia)
end.
clear AUX ST ERR MI FR OS BLKl. rename MU into MU0. rename WM into WM0.
intros m2 s2' r errv2 y5 y6 y7 va0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 AUX ST ERR MI HPR1 FA2 SO2 FR OS RES.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 408)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.

lazymatch type of ARRg with u64arr _ ?mx _ _ =>
pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HPR1 (u64arr_chunk _ _ _ _ ARRg LENg)
ltac:(eapply (rclient_range_block _ _ pg Gv (os_lacing_storage os * 8)); [apply lb_remove_keep; [exact HINg| cbn; congruence]| lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as BLKg end.
clear ARRl ARRg.
destruct r as [ql|].
+
first [ sf_destruct 8%nat RES as L' junk1 -> BRl' HP1 BLK1 HKl' SAME1 | sf_fb; destruct RES as (L' & junk1 & -> & BRl' & HP1 & BLK1 & HKl' & SAME1) ].
pose proof BRl' as sfP_; first [ sf_destruct 5%nat sfP_ as P1 P2 P3 P4 P5 | sf_fb; destruct sfP_ as (P1 & P2 & P3 & P4 & P5) ]. unfold alloc_ceiling in P4.
rewrite Z.min_r in BLK1 by lia.
replace (Z.to_nat (os_lacing_storage os * 4)) with (length (u32s lws)) in BLK1 by (rewrite u32s_length; lia). rewrite firstn_all in BLK1.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP1) as ND1. cbn [map blk_id fst] in ND1.
unfold implM. iprefix.

zstep. if_cases CN3; zify_cond CN3; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN3 by lia; [exfalso; lia|].
zstep. lstep. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 n' 3) by lia. change (2^3) with 8.

zstep. apply evt_done.
eapply (realloc_site rhdr_known HR _ _ s2' ((ql, L', n' * 4) :: lb_remove pl LB) pg Gv (os_lacing_storage os * 8) (n' * 8)
(bv_unsigned sp + -32) 0x30430 A lo B errv2 (u64s gws) _ _ gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact BLKg | exact OS | exact FR | exact ERR]
| |- In _ _ => right; apply lb_remove_keep; [exact HINg| cbn; congruence]
| |- rhdr_known _ _ => eapply rhdr_known_indep; exact HKg
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP1| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- _ mod 2 = 0 => reflexivity
| |- forall m', _ => idtac
| |- _ => try (unfold OGG_REALLOC_STACK, MMAP_THRESHOLD in *; lia)
end.
clear AUX ST ERR MI FR OS BLKg. rename MU into MU1. rename WM into WM1.
intros m3 s3' r2 errv3 z5 z6 z7 va1 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 AUX ST ERR MI HPR2 FA3 SO3 FR OS RES.
pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (A, A + 408)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
assert (NEQ1 : ql <> pg).
{ intros ->. apply List.NoDup_cons_iff in ND1. destruct ND1 as [NI _]. apply NI.
apply (in_map_blk_id (pg, Gv, os_lacing_storage os * 8)). apply lb_remove_keep; [exact HINg| cbn; congruence]. }

apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR2) in BLK1.
2:{ eapply (rclient_range_block _ _ ql L' (n' * 4)); [apply lb_remove_keep; [left; reflexivity| cbn; exact NEQ1]| lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
destruct r2 as [qg|].
*
first [ sf_destruct 8%nat RES as Gv' junk2 -> BRg' HP2 BLK2 HKg' SAME2 | sf_fb; destruct RES as (Gv' & junk2 & -> & BRg' & HP2 & BLK2 & HKg' & SAME2) ].
pose proof BRg' as sfP_; first [ sf_destruct 5%nat sfP_ as R1 R2 R3 R4 R5 | sf_fb; destruct sfP_ as (R1 & R2 & R3 & R4 & R5) ]. unfold alloc_ceiling in R4.
rewrite Z.min_r in BLK2 by lia.
replace (Z.to_nat (os_lacing_storage os * 8)) with (length (u64s gws)) in BLK2 by (rewrite u64s_length; lia). rewrite firstn_all in BLK2.
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP2) as ND2. cbn [map blk_id fst] in ND2.
unfold implM. iprefix.

zstep. if_cases CN4; zify_cond CN4; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN4 by lia; [exfalso; lia|].
zstep. lstep. lstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp).
zstep.
apply evt_done. cbv beta iota. apply impl_ret_ok. apply evt_done. cbn [fst snd].
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
destruct (chunk_u32arr mx L' lws junk1 n' _ BLK1 eq_refl ltac:(lia) ltac:(lia)) as (ljunk & ARRl' & LENl');
destruct (chunk_u64arr mx Gv' gws junk2 n' _ BLK2 eq_refl ltac:(lia) ltac:(lia)) as (gjunk & ARRg' & LENg') end.
unfold lacing_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split; [congruence|]. split; [congruence|].
left. split; [reflexivity|]. first [ unshelve sf_eexists 7%nat; [ exact (ql) | exact (qg) | exact (L') | exact (Gv') | exact (ljunk) | exact (gjunk) | exact (((qg, Gv', n' * 8) :: lb_remove pg ((ql, L', n' * 4) :: lb_remove pl LB))) | ] | sf_fb; exists ql, qg, L', Gv', ljunk, gjunk, ((qg, Gv', n' * 8) :: lb_remove pg ((ql, L', n' * 4) :: lb_remove pl LB)) ].
split; [destruct os; reflexivity|].
split; [cbn; lia|]. split; [cbn; lia|]. split; [right; cbn; unfold MMAP_THRESHOLD in *; lia|]. split; [exact LENl'|]. split; [exact LENg'|].
split. { eapply RHEAP_frame_proof; [exact HP2| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split. { intros b Hb. right. pose proof (lb_remove_neq _ _ _ Hb) as NB. apply lb_remove_sub in Hb.
apply lb_remove_keep; [right; exact Hb| exact NB]. }
split. { right. apply lb_remove_keep; [left; reflexivity| cbn; exact NEQ1]. }
split; [left; reflexivity|].
split. { apply (stream_blocks_newgranule _ (set_blocks os (os_body_data os) (os_body_storage os) (Some ql) (os_granule_vals os) (os_lacing_storage os)) Bd L' Gv pg).
- apply (stream_blocks_newlacing LB os Bd L Gv pl); [exact SB| exact Hpl| first [exact Hpg | reflexivity]| exact ND1].
- cbn [os_granule_vals set_blocks]. first [exact Hpg | reflexivity].
- reflexivity.
- exact ND2. }
split; [eapply rhdr_known_indep; exact HKl'|]. split; [exact HKg'|].
split. { intros b Hb N1 N2. split.
- intros E. pose proof ND1 as NDc. apply List.NoDup_cons_iff in NDc. destruct NDc as [NI _]. apply NI. rewrite <- E.
apply in_map_blk_id. apply lb_remove_keep; [exact Hb| exact N1].
- intros E. pose proof ND2 as NDc. apply List.NoDup_cons_iff in NDc. destruct NDc as [NI _]. apply NI. rewrite <- E.
apply in_map_blk_id. apply lb_remove_keep; [| exact N2]. right. apply lb_remove_keep; [exact Hb| exact N1]. }
split; [exact BRl'|]. split; [exact BRg'|].
split. { eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR1| lia| intros b Hb; apply lb_remove_sub in Hb; exact Hb| intros x Hx; exact Hx]|].
eapply cmod_trans; [eapply cmod_of_munch; [exact MU1| exact WM1]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR2| lia| | intros x Hx; exact Hx]|].
{ intros b Hb. pose proof (lb_remove_neq _ _ _ Hb) as NB. apply lb_remove_sub in Hb. apply lb_remove_keep; [right; exact Hb| exact NB]. }
apply cmod_of_munch; [exact MU| exact WM]. }
split; [exact OS|]. split; [exact ARRl'|]. split; [exact ARRg'|].
cbn [os_lacing_storage set_blocks]. rewrite (lbr_hd_other pg) by (cbn; exact NEQ1). apply perm_swap.
*
first [ sf_destruct 4%nat RES as -> HP2 BLK2 HK2 | sf_fb; destruct RES as (-> & HP2 & BLK2 & HK2) ].
unfold implM. iprefix.
zstep. if_cases CN4; zify_cond CN4; [| exfalso; apply CN4; reflexivity].

zstep. zstep. apply evt_done. cbv beta iota. eapply implM_bind.
{ lazymatch goal with OSx : rw_cells rsegs ?mx A _ |- implM _ (ogg_stream_clear _ ?osv) _ _ _ =>
eapply (ogg_stream_clear_spec HF) with (s := s3') (LB := (ql, L', n' * 4) :: lb_remove pl LB) (os := osv) (A := A) (Bd := Bd) (L := L') (Gv := Gv) (hdr := hdr);
[ eapply RHEAP_frame_proof; [exact HP2| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| apply (stream_blocks_newlacing LB os Bd L Gv pl); [exact SB| exact Hpl| exact Hpg| exact ND1]
| exact HL
| eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| lia
| rewrite unsigned_lit by lia; exact ST
| exact CEIL
| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR
| exact MI
| exact TP
| reflexivity
| exact OSx ] end. }
clear AUX ST ERR MI. rename MU into MU2. rename WM into WM2.
intros osr ps4 ms4 PO.
first [ sf_destruct 26%nat PO as q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 m5 -> MI5 ST ERR AUX CMc FA4 SO4 HP5 -> OSZ | sf_fb; destruct PO as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m5 & -> & MI5 & ST & ERR & AUX & CMc & FA4 & SO4 & HP5 & -> & OSZ) ].
rewrite unsigned_lit in ST, CMc by lia.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
repeat match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -32) _ |- _ =>
apply (cmod_rw_cells _ _ _ _ _ _ _ CMc) in FRx; [| left; cbn; lia| cbn; lia] end.
apply implM_ret.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -32) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
zstep.
lazymatch type of HP5 with RHEAP _ ?LBf _ =>
assert (SUB1 : forall b, In b LBf -> In b (lb_remove pl LB))
by (intros b Hb; pose proof Hb as Hb0; unfold stream_clear_LB in Hb; do 3 apply lb_remove_opt_sub in Hb; destruct Hb as [<-|Hb];
[ exfalso; unfold stream_clear_LB in Hb0; cbn [os_lacing_vals os_granule_vals set_blocks lb_remove_opt] in Hb0;
apply lb_remove_sub in Hb0; apply lb_remove_neq in Hb0; apply Hb0; reflexivity
| exact Hb]) end.
assert (SUBf : forall b, In b (stream_clear_LB ((ql, L', n' * 4) :: lb_remove pl LB)
(set_blocks os (os_body_data os) (os_body_storage os) (Some ql) (Some pg) (os_lacing_storage os))) -> In b LB)
by (intros b Hb; eapply lb_remove_sub; apply SUB1; exact Hb).
apply evt_done. unfold lacing_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split; [exact AUX|].
split; [congruence|]. split; [congruence|].
right. split; [reflexivity|]. split; [reflexivity|].
lazymatch type of HP5 with RHEAP _ ?LBf _ => exists LBf end.
split; [exact HP5|]. split; [exact SUBf|].
split. { intros b Hb NBb NBl NBg. unfold stream_clear_LB. cbn [os_body_data os_lacing_vals os_granule_vals set_blocks].
apply lb_remove_opt_keep; [| exact NBg]. apply lb_remove_opt_keep.
2:{ intros E. apply List.NoDup_cons_iff in ND1. destruct ND1 as [NI _]. apply NI. rewrite <- E.
apply in_map_blk_id. apply lb_remove_keep; [exact Hb| exact NBl]. }
apply lb_remove_opt_keep; [| destruct (os_body_data os) as [pb|]; [intros E; apply NBb; rewrite E; reflexivity| exact I]].
right. apply lb_remove_keep; [exact Hb| exact NBl]. }
split. { eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR1| lia| | intros x Hx; exact Hx]|].
{ exact SUB1. }
eapply cmod_trans; [eapply cmod_of_munch; [exact MU1| exact WM1]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR2| lia| | intros x Hx; exact Hx]|].
{ intros b Hb. unfold stream_clear_LB in Hb. cbn [os_lacing_vals os_granule_vals set_blocks lb_remove_opt] in Hb.
pose proof (lb_remove_neq _ _ _ Hb) as NBg. apply lb_remove_sub in Hb. apply lb_remove_sub in Hb. apply lb_remove_opt_sub in Hb.
apply lb_remove_keep; [exact Hb| exact NBg]. }
eapply cmod_trans; [eapply cmod_of_munch; [exact MU2| exact WM2]|].
eapply (cmod_weaken [(A, A + 408)] _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[ eapply (cmod_drop_low (bv_unsigned sp + -32 - 16) (bv_unsigned sp + -32)); [exact CMc| lia| lia|];
intros bq Hbq; left;
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 Hbq) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ X4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & X4 & _) ]; unfold alloc_ceiling in X4; lia
| lia | intros b Hb; exact Hb | intros xq Hxq; cbn in Hxq |- *; tauto ]. }
split; [exact OSZ|].
eapply clear_LB_after_newlacing; [exact SB| exact Hpl| exact ND1].
+
first [ sf_destruct 4%nat RES as -> HP1 BLK1 HK1 | sf_fb; destruct RES as (-> & HP1 & BLK1 & HK1) ].
unfold implM. iprefix.
zstep. if_cases CN3; zify_cond CN3; [| exfalso; apply CN3; reflexivity].

zstep. zstep. apply evt_done. cbv beta iota. eapply implM_bind.
{ lazymatch goal with OSx : rw_cells rsegs ?mx A _ |- _ =>
eapply (ogg_stream_clear_spec HF) with (s := s2') (LB := LB) (os := os) (A := A) (Bd := Bd) (L := L) (Gv := Gv) (hdr := hdr);
[ eapply RHEAP_frame_proof; [exact HP1| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| exact SB
| exact HL
| eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia
| lia
| rewrite unsigned_lit by lia; exact ST
| exact CEIL
| rewrite unsigned_lit by lia; unfold RFREE_STACK; lia
| rewrite TP, unsigned_lit by (unfold RATP; lia); unfold RATP; exact ERR
| exact MI
| exact TP
| reflexivity
| exact OSx ] end. }
clear AUX ST ERR MI. rename MU into MU1. rename WM into WM1.
intros osr ps4 ms4 PO.
first [ sf_destruct 26%nat PO as q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 m5 -> MI5 ST ERR AUX CMc FA4 SO4 HP5 -> OSZ | sf_fb; destruct PO as (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & m5 & -> & MI5 & ST & ERR & AUX & CMc & FA4 & SO4 & HP5 & -> & OSZ) ].
rewrite unsigned_lit in ST, CMc by lia.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
repeat match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -32) _ |- _ =>
apply (cmod_rw_cells _ _ _ _ _ _ _ CMc) in FRx; [| left; cbn; lia| cbn; lia] end.
apply implM_ret.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -32) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
zstep.
assert (SUB1 : forall b, In b (stream_clear_LB LB os) -> In b (lb_remove pl LB)).
{ intros b Hb. unfold stream_clear_LB in Hb. rewrite Hpl, Hpg in Hb. cbn [lb_remove_opt] in Hb.
apply lb_remove_sub in Hb. pose proof (lb_remove_neq _ _ _ Hb) as NBl. apply lb_remove_sub in Hb. apply lb_remove_opt_sub in Hb.
apply lb_remove_keep; [exact Hb| exact NBl]. }
assert (SUBf : forall b, In b (stream_clear_LB LB os) -> In b LB) by (intros b Hb; eapply lb_remove_sub; apply SUB1; exact Hb).
apply evt_done. unfold lacing_expand_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end. eexists.
split; [reflexivity|]. split; [assumption|]. split; [exact ST|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR. }
split; [exact AUX|].
split; [congruence|]. split; [congruence|].
right. split; [reflexivity|]. split; [reflexivity|].
exists (stream_clear_LB LB os).
split; [exact HP5|]. split; [exact SUBf|].
split. { intros b Hb NBb NBl NBg. unfold stream_clear_LB. rewrite Hpl, Hpg. cbn [lb_remove_opt].
apply lb_remove_keep; [| exact NBg]. apply lb_remove_keep; [| exact NBl].
apply lb_remove_opt_keep; [exact Hb| destruct (os_body_data os) as [pb|]; [intros E; apply NBb; rewrite E; reflexivity| exact I]]. }
split. { eapply cmod_trans; [eapply cmod_of_munch; [exact MU0| exact WM0]|].
eapply cmod_trans; [eapply (cmod_weaken _ _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[eapply cmod_of_rheap_pres; exact HPR1| lia| exact SUB1| intros x Hx; exact Hx]|].
eapply cmod_trans; [eapply cmod_of_munch; [exact MU1| exact WM1]|].
eapply (cmod_weaken [(A, A + 408)] _ _ _ (bv_unsigned sp + -32) (bv_unsigned sp));
[ eapply (cmod_drop_low (bv_unsigned sp + -32 - 16) (bv_unsigned sp + -32)); [exact CMc| lia| lia|];
intros bq Hbq; left;
pose proof (RHEAP_block_range_proof _ _ _ _ HP5 Hbq) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ X4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & X4 & _) ]; unfold alloc_ceiling in X4; lia
| lia | intros b Hb; exact Hb | intros xq Hxq; cbn in Hxq |- *; tauto ]. }
split; [exact OSZ|].
unfold stream_clear_LB. rewrite Hpl, Hpg. reflexivity.
Qed.
End LEXP.
