(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the stack block is the launch's [entry_stack_image] over the process input and the mmap base; the auxv facts are [auxv_keys] at both values of the CONFIG_RSEQ flag). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw X0pt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1m2 X1m3 X1m5 X1nl X1h7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require X1ff X1fd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1o8 X1r3 X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.

Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change Ref.X1fd.rsegs with X1gj.rsegs in *.

Notation rph := Plain.M.phdrs.

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

(* the words of a [u64s] list, one at a time *)
Lemma u64s_nth_bytes : forall m A ws i w, bytes_at rsegs m A (u64s ws) -> nth_error ws i = Some w ->
bytes_at rsegs m (A + 8 * Z.of_nat i) (le8 w).
Proof.
intros m A ws i w B Hn. destruct (u64s_split _ _ _ Hn) as (pre & post & _ & _ & Eu & Hlu).
rewrite Eu in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite Hlu in B.
apply bytes_at_app in B. destruct B as [B _].
replace (A + 8 * Z.of_nat i) with (A + Z.of_nat (8 * i)) by lia. exact B.
Qed.

Section Pieces.
Context {RCEIL : RunCeiling}.
(* LPS 727298f3: the stack block is the launch's own ([entry_stack_image]); its pieces are
   [X0pw.image_pieces] and [X0pw.image_argv_string] under the launch's head-size bound [HSP]. *)
Variables (sp mbase : word) (rnd : EntryDraw) (inp : ProcInput).
Notation usp := (bv_unsigned sp).
Notation argv := (in_argv inp).
Notation ent := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)).
Notation img := (entry_stack_image inp mbase rph (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) sp rnd).
Hypothesis HSP : (usp + head_size inp <= bv_unsigned (ed_top rnd) - 8 - str_len inp)%Z.
Variable (m : mem).
Hypothesis IMG : bytes_at rsegs m usp img.

#[using="HSP IMG"] Lemma stack_pieces :
bytes_at rsegs m usp (le8 (Z_to_bv 64 (argc inp))) /\
bytes_at rsegs m (usp + 8) (u64s (argv_ptrs inp rnd ++ [Z_to_bv 64 0])) /\
bytes_at rsegs m (usp + 8 * (argc inp + 2)) (u64s (envp_ptrs inp rnd ++ [Z_to_bv 64 0])) /\
bytes_at rsegs m (usp + 8 * (argc inp + envc inp + 3)) (u64s (auxv_words inp mbase rph ent sp rnd)) /\
bytes_at rsegs m (str_base inp rnd) (flatten_strings argv) /\
bytes_at rsegs m (env_base inp rnd) (flatten_strings (in_envp inp)) /\
bytes_at rsegs m (rnd_addr inp sp) (rnd_bytes rnd).
Proof. exact (image_pieces rsegs inp mbase rph ent sp rnd HSP m IMG). Qed.

#[using="HSP IMG"] Lemma argv_cstring : forall i s, nth_error argv i = Some s -> usp mod 8 = 0 ->
exists p slack, nth_error (argv_ptrs inp rnd) i = Some (Z_to_bv 64 p) /\ usp + 8 * (argc inp + envc inp + 3) + 16 <= p /\
p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= usp + Z.of_nat (length img) /\
bytes_at rsegs m p (s ++ Z_to_bv 8 0 :: slack) /\
(- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack).
Proof.
intros i s Hn _.
destruct (image_argv_string rsegs inp mbase rph ent sp rnd HSP m IMG i s Hn) as (p & slack & A1 & A2 & A3 & A4 & A5).
exists p, slack. pose proof (str_base_eq inp mbase rph ent sp rnd HSP) as SB. pose proof (head_size_ge inp) as HG.
split; [exact A1|]. split; [lia|]. split; [exact A3|]. split; [exact A4| exact A5].
Qed.

#[using="HSP"] Lemma IMG_len : usp + Z.of_nat (length img) <= 2^64.
Proof. exact (image_hi inp mbase rph ent sp rnd HSP). Qed.
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
(forall a : word, 0x66238 <= bv_unsigned a < 0x665e4 -> m a = None) ->
rw_cells rsegs m 0x661c8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m 0x661d0 [C8 auxv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
rw_cells rsegs m 0x34bc0 [C8 (Z_to_bv 64 0x661a8)] ->
rw_cells rsegs m 0x661a8 [C8 run_canary] ->
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

Definition RINITIALIZED : Z := 0x45e40.
Definition RGOT_FUZZINIT : Z := 0x34b18.

Definition RSTG : Z := 0x35e39.
Lemma RSTG_eq : RSTAGE_plain = RSTG. Proof. reflexivity. Qed.

Lemma stage_image0 : X0pw.rw_bytes_b rsegs RSTG (repeat (Z_to_bv 8 0) (Z.to_nat 65536)) = true.
Proof. vm_compute. reflexivity. Qed.

Section InitFacts.
Context {RCEIL : RunCeiling}.
Variables (sp0 mbase : word) (rnd : EntryDraw) (inp : ProcInput) (m : mem).
Notation usp0 := (bv_unsigned sp0).
Notation ent := (Z_to_bv 64 (Z.of_N Plain.M.init_pc)).
Hypothesis NONE : forall a : word, (0x34000 <= bv_unsigned a < 0x67000)%Z -> outside (rcrt_written) (bv_unsigned a) -> m a = None.
Hypothesis LIBC1 : rw_cells rsegs m 0x661c8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)].
Hypothesis LIBC2 : rw_cells rsegs m 0x661d0 [C8 (Z_to_bv 64 (auxv_addr sp0 inp)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)].
Hypothesis GOTG : rw_cells rsegs m 0x34bc0 [C8 (Z_to_bv 64 0x661a8)].
Hypothesis GUARD : rw_cells rsegs m 0x661a8 [C8 (canary_of (rnd_w0 rnd))].
Hypothesis MI : mem_inv rsegs m.
Hypothesis IMG : bytes_at rsegs m usp0 (entry_stack_image inp mbase rph ent sp0 rnd).
Hypothesis HSP : (usp0 + head_size inp <= bv_unsigned (ed_top rnd) - 8 - str_len inp)%Z.
Hypothesis HTOP : (bv_unsigned (ed_top rnd) <= 0x800000000000)%Z.

Hypothesis HCEIL : alloc_ceiling = usp0 - 8388608.
Hypothesis HSEC : run_secret = rnd_w1 rnd.
Hypothesis HCAN : run_canary = canary_of (rnd_w0 rnd).

Hypothesis RHI : rheap_init_stmt.

#[using="rnd NONE LIBC1 LIBC2 GOTG GUARD MI HCAN RHI"] Lemma heap_init : RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] m /\ rw_cells rsegs m RAUXV_CELL [C8 (Z_to_bv 64 (auxv_addr sp0 inp))].
Proof.
apply RHI; [| exact LIBC1| exact LIBC2| exact GOTG| rewrite HCAN; exact GUARD| exact MI].
intros a Ha. apply NONE; [lia|]. unfold rcrt_written. cbn. lia.
Qed.

(* LPS 727298f3: the auxv is the launch's ([X1nl.rauxv_eq]); its keys are read off it one word at a time *)
#[using="NONE LIBC1 LIBC2 GOTG GUARD MI IMG HSP HTOP HCEIL HSEC HCAN RHI"] Lemma rauxv_ok_init : rauxv_ok m usp0.
Proof.
destruct (stack_pieces sp0 mbase rnd inp HSP m IMG) as (_ & _ & _ & AUXW & _ & _ & RND).
rewrite (rauxv_eq sp0 mbase rnd inp) in AUXW.
pose proof (head_size_ge inp) as HG. pose proof (bv_unsigned_in_range 64 (ed_top rnd)) as RT. unfold bv_modulus in RT.
pose proof (bv_unsigned_in_range 64 sp0) as RS. unfold bv_modulus in RS.
set (av := auxv_addr sp0 inp). set (ra := rnd_addr inp sp0).
assert (AV : av = usp0 + 8 * (argc inp + envc inp + 3)) by reflexivity.
assert (RA : ra = usp0 + head_size inp - 16) by reflexivity.
rewrite <- AV in AUXW.
exists av, 0, 0, 0, 0, 0, 0, 0, 0, ra.
split; [apply (proj2 heap_init)|].
split.
{ unfold auxv_keys.
revert AUXW. generalize (kb_rseq (in_kernel inp)) as r. intros r AUXW.
lazymatch type of AUXW with bytes_at _ _ _ (u64s ?ws) =>
assert (KEY : forall i w, nth_error ws i = Some w -> bytes_at rsegs m (av + 8 * Z.of_nat i) (le8 w))
by (intros i w Hn; exact (u64s_nth_bytes m av ws i w AUXW Hn)) end.
clear AUXW.
rewrite <- (Z.add_0_r av) at 1.
Ltac key_at KEY :=
lazymatch goal with |- bytes_at _ _ (?A + ?c) _ =>
let n := eval compute in (Z.to_nat (c / 8)) in
replace (A + c) with (A + 8 * Z.of_nat n) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
apply KEY; reflexivity end.
(* split only the conjunctions of [auxv_keys]: a bare [split] would also open each [bytes_at] *)
destruct r.
- repeat match goal with |- _ /\ _ => split end; try key_at KEY.
  left. repeat match goal with |- _ /\ _ => split end; key_at KEY.
- repeat match goal with |- _ /\ _ => split end; try key_at KEY.
  right. key_at KEY. }
split.
{ rewrite rnd_bytes_eq in RND. apply bytes_at_app in RND. destruct RND as [_ R]. rewrite length_le8 in R. rewrite HSEC.
replace (ra + 8) with (ra + Z.of_nat 8) by lia. exact R. }
rewrite AV, RA in *. unfold argc, envc, head_size, str_len in *.
repeat split; lia.
Qed.

#[using="RCEIL NONE"] Lemma initialized_init : rw_cells rsegs m RINITIALIZED [C1 (Z_to_bv 8 0)].
Proof. unfold RINITIALIZED. rimg_chunk0 NONE m 0x45e40 [C1 (Z_to_bv 8 0)] H. exact H. Qed.

#[using="RCEIL NONE"] Lemma got_fuzzinit_init : rw_cells rsegs m RGOT_FUZZINIT [C8 (Z_to_bv 64 0)].
Proof. unfold RGOT_FUZZINIT. rimg_chunk0 NONE m 0x34b18 [C8 (Z_to_bv 64 0)] H. exact H. Qed.

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

Lemma libc_head_byte : forall (m : mem) (a : Z), 0x661c8 <= a < 0x661d0 ->
exists b : byte, mrd rsegs m (wa a) = Some b /\ wview rsegs m (wa a) <> None.
Proof.
intros m a Ha.
assert (IMG : exists b0, seg_rom rsegs (wa a) = Some b0 /\ wview rsegs (fun _ => None) (wa a) <> None).
{ assert (E : a = 0x661c8 \/ a = 0x661c9 \/ a = 0x661ca \/ a = 0x661cb \/ a = 0x661cc \/ a = 0x661cd \/ a = 0x661ce \/ a = 0x661cf) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; (eexists; split; [vm_compute; reflexivity| vm_compute; discriminate]). }
destruct IMG as (b0 & SR & WV).
destruct (m (wa a)) as [b|] eqn:E.
- exists b. split; [unfold mrd; rewrite E; reflexivity|]. unfold wview. rewrite E. discriminate.
- exists b0. split; [unfold mrd; rewrite E; exact SR|]. unfold wview in *. rewrite E. exact WV.
Qed.

Lemma RHEAP_libc_head {RCEIL : RunCeiling} : forall s LB m, RHEAP s LB m ->
exists (cdt thr sec : byte) (tm1 : word),
rw_cells rsegs m 0x661c8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1].
Proof.
intros s LB m sfH_; first [ sf_destruct 6%nat sfH_ as st LB0 _ _ MREP _ | sf_fb; destruct sfH_ as (st & LB0 & _ & _ & MREP & _) ].
first [ sf_destruct 4%nat MREP as _ _ (_ & NL & _) _ | sf_fb; destruct MREP as (_ & _ & (_ & NL & _) & _) ].
destruct (libc_head_byte m 0x661c8 ltac:(lia)) as (b0 & R0 & W0).
destruct (libc_head_byte m 0x661c9 ltac:(lia)) as (b1 & R1 & W1).
destruct (libc_head_byte m 0x661ca ltac:(lia)) as (b2 & R2 & W2).
destruct (libc_head_byte m 0x661cc ltac:(lia)) as (b4 & R4 & W4).
destruct (libc_head_byte m 0x661cd ltac:(lia)) as (b5 & R5 & W5).
destruct (libc_head_byte m 0x661ce ltac:(lia)) as (b6 & R6 & W6).
destruct (libc_head_byte m 0x661cf ltac:(lia)) as (b7 & R7 & W7).
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
+ replace (0x661c8 + 3) with (0x661cb + Z.of_nat 0) by lia. exact R3.
+ exact R4. + exact R5. + exact R6. + exact R7.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|].
intros i Hi.
assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; cbn [Z.add].
+ exact W0. + exact W1. + exact W2.
+ replace (0x661c8 + 3) with (0x661cb + 0) by lia. exact W3.
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
F (Z_to_bv 64 0x3274c) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros SRC LEN HN HD HS DST SEP MI.
pose proof (bytes_at_bound _ _ _ _ SRC) as B1. pose proof (rw_cells_bound _ _ _ _ DST) as B2. cbn [cells_size csize Nat.add] in B2.
assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (Ref.X1fd.memcpy_spec) with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
intros ms' P. unfold Ref.X1fd.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.
