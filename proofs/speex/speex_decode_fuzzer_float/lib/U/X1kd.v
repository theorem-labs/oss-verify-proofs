(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1nl X1h7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1o8 X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.

Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.

Notation rph := Ubsan.M.phdrs.

Section Agree.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.

Definition agree_on (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> P a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
#[using="Type"] Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
#[using="Type"] Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

#[using="Type"] Lemma bytes_at_agree : forall P m m' A bs,
agree_on P m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
bytes_at segs m' A bs.
Proof.
intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma wr_at_agree : forall P m m' A n,
agree_on P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rw_cells_agree : forall P m m' A cs,
agree_on P m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
rw_cells segs m' A cs.
Proof.
intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply wr_at_agree; eauto.
Qed.
End Agree.

Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> agree_on rsegs (fun a => outside W a) m m'.
Proof.
intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Lemma implM_of_enode : forall {A} (n : node) (pl : resp -> option A) (P : A -> machine_state -> Prop) (s : PState) ms,
impl rsegs (at_node rsegs) (enode n pl) (epost P) ms ->
implM rsegs (msys n pl) s (fun a s' ms' => P a ms' /\ s' = s) ms.
Proof.
intros A n pl P s ms H. unfold implM, msys, enode in *. cbn in *.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. intros a. unfold zbytes. apply length_map. Qed.

Lemma zbytes_map_unsigned' : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. intros bs. rewrite map_map. induction bs as [|b bs IH]; cbn; [reflexivity|]. rewrite IH. f_equal. apply (@definitions.Z_to_bv_bv_unsigned 8). Qed.

Lemma map_unsigned_range : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn; constructor; [| exact IH].
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma map_unsigned_pos : forall bs : list byte, ~ In (Z_to_bv 8 0) bs -> Forall (fun c => 0 < c < 256) (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; cbn; intros H; constructor.
- pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
assert (bv_unsigned b <> 0); [| lia]. intros E. apply H. left. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. rewrite E. reflexivity.
- apply IH. intros X. apply H. right. exact X.
Qed.

Lemma ceil8_le : forall e E, E mod 8 = 0 -> e <= E -> e + (- e) mod 8 <= E.
Proof. intros e E H1 H2. Z.div_mod_to_equations. lia. Qed.

Section Pieces.
Context {RCEIL : RunCeiling}.
Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem).
Notation usp := (bv_unsigned sp).
Hypothesis IMG : bytes_at rsegs m usp (build_stack_bytes rph sp argv envp uid hw rnd).

#[using="IMG"] Lemma stack_pieces :
bytes_at rsegs m usp (le8 (Z_to_bv 64 (argc argv))) /\
bytes_at rsegs m (usp + 8) (u64s (argv_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
bytes_at rsegs m (usp + 8 * (argc argv + 2)) (u64s (envp_ptrs sp argv envp ++ [Z_to_bv 64 0])) /\
bytes_at rsegs m (usp + 8 * (argc argv + envc envp + 3)) (u64s (auxv_words rph sp argv envp uid hw)) /\
bytes_at rsegs m (str_base sp argv envp) (flatten_strings argv) /\
bytes_at rsegs m (env_base sp argv envp) (flatten_strings envp) /\
bytes_at rsegs m (rnd_addr sp argv envp) (rnd_bytes rnd).
Proof.
pose proof IMG as B. rewrite build_stack_bytes_eq in B.
unfold raw_bytes in B. remember (auxv_words rph sp argv envp uid hw) as AW eqn:EAW. cbn [u64s app] in B.
rewrite u64s_app in B. cbn [u64s app] in B. rewrite u64s_app in B. cbn [u64s app] in B.
repeat rewrite <- app_assoc in B. cbn [app] in B.
pose proof (raw_len_nonneg argv envp) as RN.
pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
apply bytes_at_app in B. destruct B as [B0 B]. rewrite length_le8 in B.
apply bytes_at_app in B. destruct B as [B1 B]. rewrite u64s_length in B. unfold argv_ptrs in B. rewrite map_length, str_ptrs_length in B.
apply bytes_at_app in B. destruct B as [B2 B]. rewrite length_le8 in B.
apply bytes_at_app in B. destruct B as [B3 B]. rewrite u64s_length in B. unfold envp_ptrs in B. rewrite map_length, str_ptrs_length in B.
apply bytes_at_app in B. destruct B as [B4 B]. rewrite length_le8 in B.
apply bytes_at_app in B. destruct B as [B5 B]. rewrite u64s_length in B. replace (length AW) with 20%nat in B by (subst AW; reflexivity).
apply bytes_at_app in B. destruct B as [B6 B].
apply bytes_at_app in B. destruct B as [B7 B].
apply bytes_at_app in B. destruct B as [B8 B]. rewrite repeat_length in B.
repeat match goal with |- _ /\ _ => split end.
- exact B0.
- rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app rsegs m _ _ _)). split; [exact B1|].
rewrite u64s_length. unfold argv_ptrs at 1. rewrite map_length, str_ptrs_length.
replace (usp + 8 + Z.of_nat (8 * length argv))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv))%Z by lia. exact B2.
- rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply (proj2 (bytes_at_app rsegs m _ _ _)). split.
+ replace (usp + 8 * (argc argv + 2))%Z with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8)%Z by (unfold argc; lia). exact B3.
+ rewrite u64s_length. unfold envp_ptrs at 1. rewrite map_length, str_ptrs_length.
replace (usp + 8 * (argc argv + 2) + Z.of_nat (8 * length envp))%Z
with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp))%Z by (unfold argc; lia). exact B4.
- replace (usp + 8 * (argc argv + envc envp + 3))%Z
with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8)%Z by (unfold argc, envc; lia). exact B5.
- replace (str_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20))%Z
by (unfold str_base, struct_size, argc, envc; lia). exact B6.
- replace (env_base sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20) + Z.of_nat (length (flatten_strings argv)))%Z
by (unfold env_base, str_base, struct_size, argc, envc; lia). exact B7.
- replace (rnd_addr sp argv envp) with (usp + Z.of_nat 8 + Z.of_nat (8 * length argv) + Z.of_nat 8 + Z.of_nat (8 * length envp) + Z.of_nat 8 + Z.of_nat (8 * 20)
+ Z.of_nat (length (flatten_strings argv)) + Z.of_nat (length (flatten_strings envp)) + Z.of_nat (Z.to_nat (pad_len argv envp)))%Z
by (unfold rnd_addr, raw_len, struct_size, argc, envc; lia). exact B.
Qed.

#[using="IMG"] Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
exists p slack, nth_error (argv_ptrs sp argv envp) i = Some (Z_to_bv 64 p) /\ str_base sp argv envp <= p /\
p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd)) /\
bytes_at rsegs m p (s ++ Z_to_bv 8 0 :: slack) /\
(- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
Proof.
intros i s Hn AL. first [ pose proof (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as sfP_; sf_destruct 5%nat sfP_ as off Hp Ho Ht Hf | sf_fb; destruct (str_ptrs_nth argv (str_base sp argv envp) i s Hn) as (off & Hp & Ho & Ht & Hf) ].
pose proof (raw_len_nonneg argv envp) as RN. pose proof (build_stack_bytes_length rph sp argv envp uid hw rnd) as BL.
pose proof (flatten_strings_length argv) as L1. pose proof (flatten_strings_length envp) as L2.
set (p := str_base sp argv envp + off).
set (e := p + Z.of_nat (length s) + 1).
set (k := (- e) mod 8).
assert (HK : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
assert (OFF : usp <= p /\ e + k <= usp + Z.of_nat (length (build_stack_bytes rph sp argv envp uid hw rnd))).
{ subst p e k. unfold str_base, struct_size, raw_len in *. split; [lia|].
rewrite BL. apply ceil8_le.
- unfold pad_len, raw_len, struct_size. Z.div_mod_to_equations. lia.
- unfold raw_len, struct_size. lia. }
exists p, (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes rph sp argv envp uid hw rnd))).
split; [unfold argv_ptrs; rewrite nth_error_map, Hp; reflexivity|]. split; [subst p; lia|].
assert (LS : length (firstn (Z.to_nat k) (skipn (Z.to_nat (e - usp)) (build_stack_bytes rph sp argv envp uid hw rnd))) = Z.to_nat k).
{ rewrite length_firstn, length_skipn. lia. }
rewrite LS. split; [lia|]. split; [| lia].
first [ sf_destruct 6%nat stack_pieces as _ _ _ _ B6 _ | sf_fb; destruct stack_pieces as (_ & _ & _ & _ & B6 & _) ].
pose proof (bytes_at_slice rsegs m (str_base sp argv envp) (flatten_strings argv) (Z.to_nat off) (length s + 1) B6 ltac:(lia)) as BS.
rewrite Hf in BS. replace (str_base sp argv envp + Z.of_nat (Z.to_nat off)) with p in BS by (subst p; lia).
pose proof (bytes_at_slice rsegs m usp (build_stack_bytes rph sp argv envp uid hw rnd) (Z.to_nat (e - usp)) (Z.to_nat k) IMG ltac:(lia)) as BK.
replace (usp + Z.of_nat (Z.to_nat (e - usp))) with (p + Z.of_nat (length (s ++ [Z_to_bv 8 0]))) in BK by (rewrite length_app; cbn [length]; subst e; lia).
pose proof (proj2 (bytes_at_app rsegs m p _ _) (conj BS BK)) as BB. rewrite <- app_assoc in BB. cbn [app] in BB. exact BB.
Qed.
End Pieces.

Ltac rimg_chunk0 NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (X0pw.rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (X0pw.rw_cells_image0 rsegs m A bs);
[ intros a Ha; cbn [length] in Ha; apply NONE; [lia| cbn [outside rcrt_written]; lia] | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].

Definition rheap_init_stmt {RCEIL : RunCeiling} : Prop := forall (m : mem) (auxv : word),
(forall a : word, 0x6d748 <= bv_unsigned a < 0x6daf4 -> m a = None) ->
rw_cells rsegs m 0x6d6d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m 0x6d6e0 [C8 auxv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
rw_cells rsegs m 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)] ->
rw_cells rsegs m 0x6d6b8 [C8 run_canary] ->
mem_inv rsegs m ->
RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] m
/\ rw_cells rsegs m RAUXV_CELL [C8 auxv].

Definition rheap_frame_stmt {RCEIL : RunCeiling} : Prop := forall s LB m m' W,
RHEAP s LB m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.

Definition rheap_blocks_nodup_stmt {RCEIL : RunCeiling} : Prop := forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Definition rheap_block_range_stmt {RCEIL : RunCeiling} : Prop := forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Definition rheap_blocks_disjoint_stmt {RCEIL : RunCeiling} : Prop := forall s LB m b1 b2,
RHEAP s LB m -> In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.

Definition rheap_facts {RCEIL : RunCeiling} : Prop :=
rheap_init_stmt /\ rheap_frame_stmt /\ rheap_blocks_nodup_stmt /\ rheap_block_range_stmt /\ rheap_blocks_disjoint_stmt.

Definition RINITIALIZED : Z := 0x4d350.
Definition RGOT_FUZZINIT : Z := 0x3c028.

Definition RSTG : Z := 0x3d349.
Lemma RSTG_eq : RSTAGE_ubsan = RSTG. Proof. reflexivity. Qed.

Lemma stage_image0 : X0pw.rw_bytes_b rsegs RSTG (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
Proof. vm_compute. reflexivity. Qed.

Section InitFacts.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (m : mem).
Notation usp0 := (bv_unsigned sp0).
Hypothesis NONE : forall a : word, (0x3b000 <= bv_unsigned a < 0x6e000)%Z -> outside (rcrt_written) (bv_unsigned a) -> m a = None.
Hypothesis LIBC1 : rw_cells rsegs m 0x6d6d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
Hypothesis LIBC2 : rw_cells rsegs m 0x6d6e0 [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
Hypothesis GOTG : rw_cells rsegs m 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)].
Hypothesis GUARD : rw_cells rsegs m 0x6d6b8 [C8 (canary_of (rnd_w0 rnd))].
Hypothesis MI : mem_inv rsegs m.
Hypothesis IMG : bytes_at rsegs m usp0 (build_stack_bytes rph sp0 argv envp uid hw rnd).
Hypothesis SPLO : sp_window_lo <= usp0.

Hypothesis HCEIL : alloc_ceiling = usp0 - 8388608.
Hypothesis HSEC : run_secret = rnd_w1 rnd.
Hypothesis HCAN : run_canary = canary_of (rnd_w0 rnd).

Hypothesis RHI : rheap_init_stmt.

#[using="rnd NONE LIBC1 LIBC2 GOTG GUARD MI HCAN RHI"] Lemma heap_init : RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] m /\ rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 argv envp))].
Proof.
apply RHI; [| exact LIBC1| exact LIBC2| exact GOTG| rewrite HCAN; exact GUARD| exact MI].
intros a Ha. apply NONE; [lia|]. unfold rcrt_written. cbn. lia.
Qed.

#[using="argv envp uid hw rnd NONE LIBC1 LIBC2 GOTG GUARD MI IMG HCEIL HSEC HCAN RHI"] Lemma rauxv_ok_init : rauxv_ok m usp0.
Proof.
first [ pose proof (stack_pieces sp0 argv envp uid hw rnd m IMG) as sfP_; sf_destruct 7%nat sfP_ as _ _ _ AUXW _ _ RND | sf_fb; destruct (stack_pieces sp0 argv envp uid hw rnd m IMG) as (_ & _ & _ & AUXW & _ & _ & RND) ].
pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd) as BL. pose proof (raw_len_nonneg argv envp) as RLN.
pose proof (bytes_at_bound _ _ _ _ IMG) as IB. unfold sp_window_lo in SPLO.
pose proof (bv_unsigned_in_range 64 uid) as RU. unfold bv_modulus in RU.
pose proof (bv_unsigned_in_range 64 hw) as RH. unfold bv_modulus in RH.
first [ unshelve sf_eexists 10%nat; [ exact ((auxv_addr sp0 argv envp)) | exact ((Z.of_N (ph_addr rph))) | exact ((Z.of_N (ph_ent rph))) | exact ((Z.of_N (ph_num rph))) | exact ((bv_unsigned hw)) | exact (4096) | exact ((bv_unsigned uid)) | exact ((bv_unsigned uid)) | exact (0) | exact ((rnd_addr sp0 argv envp)) | ] | sf_fb; exists (auxv_addr sp0 argv envp), (Z.of_N (ph_addr rph)), (Z.of_N (ph_ent rph)), (Z.of_N (ph_num rph)), (bv_unsigned hw), 4096, (bv_unsigned uid), (bv_unsigned uid), 0, (rnd_addr sp0 argv envp) ].
split; [apply (proj2 heap_init)|].
split. { unfold auxv_addr. replace (rauxv_list _ _ _ _ _ _ _ _ _) with (auxv_words rph sp0 argv envp uid hw); [exact AUXW|].
unfold rauxv_list, auxv_words, wz. cbn [map]. rewrite !(Z_to_bv_bv_unsigned uid), !(Z_to_bv_bv_unsigned hw). reflexivity. }
split. { rewrite rnd_bytes_eq in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R. rewrite HSEC.
replace (rnd_addr sp0 argv envp + 8) with (rnd_addr sp0 argv envp + Z.of_nat 8) by lia. exact R. }
unfold auxv_addr, rnd_addr, raw_len, struct_size, argc, envc, sp_window_lo, stack_max_size in *.
pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
repeat split; lia.
Qed.

#[using="RCEIL NONE"] Lemma initialized_init : rw_cells rsegs m RINITIALIZED [C1 (Z_to_bv 8 0)].
Proof. unfold RINITIALIZED. rimg_chunk0 NONE m 0x4d350 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

#[using="RCEIL NONE"] Lemma got_fuzzinit_init : rw_cells rsegs m RGOT_FUZZINIT [C8 (Z_to_bv 64 0)].
Proof. unfold RGOT_FUZZINIT. rimg_chunk0 NONE m 0x3c028 [C8 (Z_to_bv 64 0)] H. exact H. Qed.

#[using="RCEIL NONE"] Lemma tables_pristine_init : rtables_pristine m.
Proof. intros a Ha. unfold RTABLES_LO, RTABLES_HI in Ha. apply NONE; [lia|]. unfold rcrt_written. cbn. lia. Qed.

#[using="RCEIL NONE"] Lemma stage_init : exists stg, rw_cells rsegs m RSTG [CB (Z.to_nat 65536) stg].
Proof.
exists (repeat (Z_to_bv 8 0) (Z.to_nat 65536)).
pose proof (X0pw.rw_cells_image0 rsegs m RSTG (repeat (Z_to_bv 8 0) (Z.to_nat 65536))) as H. rewrite repeat_length in H.
apply H; [| apply stage_image0| unfold RSTG; lia| unfold RSTG; lia].
intros a Ha. unfold RSTG in Ha. apply NONE; [lia|]. unfold rcrt_written. cbn. lia.
Qed.
End InitFacts.

Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
intros b0 b1 b2 b3.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 2^8 * bv_unsigned b1 + 2^16 * bv_unsigned b2 + 2^24 * bv_unsigned b3).
exists (Z_to_bv 64 v). unfold le4. rewrite Z_to_bv_unsigned.
assert (HV : 0 <= v < 2^32) by (subst v; lia).
replace (bv_wrap 64 v) with v by (unfold bv_wrap, bv_modulus; rewrite Z.mod_small; [reflexivity|]; cbn; lia).
cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add].
rewrite !Z.shiftr_div_pow2 by lia.
assert (E0 : Z_to_bv 8 v = b0).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
assert (E1 : Z_to_bv 8 (v / 2^8) = b1).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
assert (E2 : Z_to_bv 8 (v / 2^16) = b2).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
assert (E3 : Z_to_bv 8 (v / 2^24) = b3).
{ apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.pow_pos Pos.mul Z.of_N]. subst v. Z.div_mod_to_equations. nia. }
rewrite E0, E1, E2, E3. reflexivity.
Qed.

Lemma libc_head_byte : forall (m : mem) (a : Z), 0x6d6d8 <= a < 0x6d6e0 ->
exists b : byte, mrd rsegs m (wa a) = Some b /\ wview rsegs m (wa a) <> None.
Proof.
intros m a Ha.
assert (IMG : exists b0, seg_rom rsegs (wa a) = Some b0 /\ wview rsegs (fun _ => None) (wa a) <> None).
{ assert (E : a = 0x6d6d8 \/ a = 0x6d6d9 \/ a = 0x6d6da \/ a = 0x6d6db \/ a = 0x6d6dc \/ a = 0x6d6dd \/ a = 0x6d6de \/ a = 0x6d6df) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
destruct IMG as (b0 & SR & WV).
destruct (m (wa a)) as [b|] eqn:E.
- exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
- exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma RHEAP_libc_head {RCEIL : RunCeiling} : forall s LB m, RHEAP s LB m ->
exists (cdt thr sec : byte) (tm1 : word),
rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
intros s LB m sfH_; first [ sf_destruct 6%nat sfH_ as st LB0 _ _ MREP _ | sf_fb; destruct sfH_ as (st & LB0 & _ & _ & MREP & _) ].
first [ sf_destruct 4%nat MREP as _ _ (_ & NL & _) _ | sf_fb; destruct MREP as (_ & _ & (_ & NL & _) & _) ].
destruct (libc_head_byte m 0x6d6d8 ltac:(lia)) as (b0 & R0 & W0).
destruct (libc_head_byte m 0x6d6d9 ltac:(lia)) as (b1 & R1 & W1).
destruct (libc_head_byte m 0x6d6da ltac:(lia)) as (b2 & R2 & W2).
destruct (libc_head_byte m 0x6d6dc ltac:(lia)) as (b4 & R4 & W4).
destruct (libc_head_byte m 0x6d6dd ltac:(lia)) as (b5 & R5 & W5).
destruct (libc_head_byte m 0x6d6de ltac:(lia)) as (b6 & R6 & W6).
destruct (libc_head_byte m 0x6d6df ltac:(lia)) as (b7 & R7 & W7).
destruct (le4_of_bytes b4 b5 b6 b7) as [tm1 Htm].
destruct NL as [[_ NLB] NLW]. unfold RNEED_LOCKS in NLB, NLW.
pose proof (proj2 (proj2 NLB) 0%nat ltac:(cbn; lia)) as R3. cbn [cells_bytes cbytes app nth_error b8 X0qm.b8] in R3.
pose proof (proj2 (proj2 NLW) 0 ltac:(cbn; lia)) as W3.
first [ unshelve sf_eexists 4%nat; [ exact (b0) | exact (b1) | exact (b2) | exact (tm1) | ] | sf_fb; exists b0, b1, b2, tm1 ]. split; [split|].
- cbn. repeat split; exact I.
- cbn [cells_bytes cbytes app]. rewrite Htm. cbn [app]. split; [lia|]. split; [cbn; lia|].
intros i Hi. cbn [length] in Hi.
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
+ exact R0. + exact R1. + exact R2.
+ replace (0x6d6d8 + 3) with (0x6d6db + Z.of_nat 0) by lia. exact R3.
+ exact R4. + exact R5. + exact R6. + exact R7.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
+ exact W0. + exact W1. + exact W2.
+ replace (0x6d6d8 + 3) with (0x6d6db + 0) by lia. exact W3.
+ exact W4. + exact W5. + exact W6. + exact W7.
Qed.

Lemma bptr_eqb_refl : forall p, bptr_eqb p p = true.
Proof. intros [[r o] z]. unfold bptr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, !Z.eqb_refl. reflexivity. Qed.

Lemma bptr_eqb_eq : forall p q, bptr_eqb p q = true -> p = q.
Proof.
intros [[r o] z] [[r' o'] z'] H. unfold bptr_eqb, aptr_eqb in H. cbn in H.
apply andb_true_iff in H. destruct H as [H1 H2]. apply andb_true_iff in H1. destruct H1 as [H0 H1].
apply N.eqb_eq in H0. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Lemma lb_remove_notin : forall p LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros H; [reflexivity|].
rewrite filter_cons. cbn [map In] in H. destruct (decide _) as [Y|N].
- rewrite IH; [reflexivity|]. intros H'. apply H. right. exact H'.
- exfalso. destruct (bptr_eqb (blk_id b) p) eqn:E.
+ apply H. left. apply bptr_eqb_eq in E. exact E.
+ apply N. cbn [negb]. exact I.
Qed.

Lemma lb_remove_head : forall b LB, List.NoDup (map blk_id (b :: LB)) -> lb_remove (blk_id b) (b :: LB) = LB.
Proof.
intros b LB ND. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
unfold lb_remove. rewrite filter_cons, bptr_eqb_refl. destruct (decide _) as [Y|N]; [exfalso; exact Y|].
apply (lb_remove_notin (blk_id b) LB). exact NI.
Qed.

Lemma lb_remove_hd : forall p b LB, blk_id b = p -> List.NoDup (map blk_id (b :: LB)) -> lb_remove p (b :: LB) = LB.
Proof. intros p b LB <- ND. apply lb_remove_head. exact ND. Qed.

Lemma lb_remove_second : forall p b0 b LB,
blk_id b = p -> List.NoDup (map blk_id (b0 :: b :: LB)) -> lb_remove p (b0 :: b :: LB) = b0 :: LB.
Proof.
intros p b0 b LB <- ND. unfold lb_remove. rewrite filter_cons.
cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI ND].
destruct (decide _) as [Y|N].
- f_equal. apply (lb_remove_head b LB). exact ND.
- exfalso. apply N. destruct (bptr_eqb (blk_id b0) (blk_id b)) eqn:E; [| exact I].
apply bptr_eqb_eq in E. apply NI. left. symmetry. exact E.
Qed.

Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m (A + Z.of_nat n1) [CB n2 b2] ->
rw_cells rsegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
intros m A n1 n2 b1 b2 H1 H2.
assert (H : rw_cells rsegs m A ([CB n1 b1] ++ [CB n2 b2])).
{ apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
split; [split|].
- cbn. rewrite length_app. split; [lia| exact I].
- cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
- replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed.

Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma rw_cells_CB_split : forall m A n k (bs : list byte),
rw_cells rsegs m A [CB n bs] -> (k <= n)%nat ->
rw_cells rsegs m A [CB k (firstn k bs); CB (n - k)%nat (skipn k bs)].
Proof.
intros m A n k bs H Hk. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L _].
apply (X0pw.rw_cells_recast rsegs m A [CB n bs]); [exact H| | |].
- cbn. rewrite length_firstn, length_skipn. repeat split; lia.
- cbn [cells_bytes cbytes app]. rewrite !app_nil_r. apply firstn_skipn.
- cbn. lia.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D S N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat N) src]
/\ bytes_at rsegs m' S src.

Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D S N : Z) (src junk : list byte),
bytes_at rsegs m S src ->
length src = Z.to_nat N -> 0 <= N -> D + N < 2^64 -> S + N < 2^64 ->
rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
(S + N <= D \/ D + N <= S)%Z ->
mem_inv rsegs m ->
evt rsegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x39c5c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN HN HD HS DST SEP MI.
pose proof (bytes_at_bound _ _ _ _ SRC) as B1. pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (U.X1fd.memcpy_spec) with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
intros ms' P. unfold U.X1fd.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.
