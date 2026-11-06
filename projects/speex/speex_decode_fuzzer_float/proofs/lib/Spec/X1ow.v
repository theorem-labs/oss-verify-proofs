(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1qu X1r3 X1r4 X1r0 X1nv
X1od X1pb X1rm X1o8 X1r6 X1pe X1ph X1p1 X1oq X1p0 X1os X1oz X1oy X1p5 X1ok X1ov.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Definition P0 (c : Z) : Z := if c =? 63 then 2 else 256.

Lemma P0_nonneg : forall c, 0 <= P0 c.
Proof. intros c. unfold P0. destruct (c =? 63); lia. Qed.
Lemma P0_small : forall c, 0 <= c < 48 -> P0 c = 256.
Proof. intros c Hc. unfold P0. destruct (Z.eqb_spec c 63); lia. Qed.
Lemma P0_63 : P0 63 = 2.
Proof. reflexivity. Qed.

Lemma PHI_P0_eq : PHI P0 = 430307328.
Proof. vm_compute. reflexivity. Qed.
Lemma PHI_P0 : PHI P0 + 2 ^ 28 <= LBUDGET.
Proof. rewrite PHI_P0_eq. unfold LBUDGET. cbn. lia. Qed.

Lemma NCAP_P0 : NCAP P0 <= 3309467.
Proof. vm_compute. discriminate. Qed.

Lemma ROOMX_intro X n :
(n < MMAP_THRESHOLD -> LRX X (size_to_class n) + 1 <= P0 (size_to_class n)) ->
(MMAP_THRESHOLD <= n -> n63X X + 1 <= P0 63) -> n <= 2 ^ 26 -> ROOMX X P0 n.
Proof. intros H1 H2 H3. split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact NCAP_P0]. Qed.

Definition KROOM : nat := 250.

Definition small (xb : bptr * Z) : Prop := 0 <= snd xb < MMAP_THRESHOLD.

Definition AMB (X0 : list (bptr * Z)) : Prop :=
(length X0 <= 2)%nat /\ Forall (fun xb => 0 <= snd xb <= MAX_INPUT + 1) X0.

Lemma AMB_nil : AMB [].
Proof. split; [cbn; lia| constructor]. Qed.
Lemma AMB_one b cap : 0 <= cap <= MAX_INPUT + 1 -> AMB [(b, cap)].
Proof. intros H. split; [cbn; lia|]. repeat constructor; cbn; lia. Qed.
Lemma AMB_two t m b cap : 0 <= m <= MAX_INPUT + 1 -> 0 <= cap <= MAX_INPUT + 1 -> AMB [(t, m); (b, cap)].
Proof. intros Hm Hc. split; [cbn; lia|]. repeat constructor; cbn; lia. Qed.

Lemma zlen_length {A} (l : list A) : zlen l = Z.of_nat (length l).
Proof. reflexivity. Qed.

Lemma LRX_le_length X c : LRX X c <= Z.of_nat (length X).
Proof. unfold LRX. pose proof (zcount_le_len (fun xb : bptr * Z => negb (MMAP_THRESHOLD <=? snd xb) && (size_to_class (snd xb) =? c)) X). rewrite zlen_length in H. exact H. Qed.

Lemma n63X_le_length X : n63X X <= Z.of_nat (length X).
Proof. unfold n63X. pose proof (zcount_le_len (fun xb : bptr * Z => MMAP_THRESHOLD <=? snd xb) X). rewrite zlen_length in H. exact H. Qed.

Lemma R63X_app X Y : R63X (X ++ Y) = R63X X + R63X Y.
Proof. unfold R63X. rewrite map_app, zsum_app. reflexivity. Qed.

Lemma R63X_small X : Forall small X -> R63X X = 0.
Proof.
induction 1 as [|[p n] X Hs _ IH]; [reflexivity|]. rewrite R63X_cons, IH. unfold small in Hs. cbn in Hs.
rewrite bigb_small by lia. reflexivity.
Qed.

Lemma round_up_pg_le x : 0 <= x -> round_up_pg x <= x + 4095.
Proof. intros Hx. pose proof (round_up_pg_spec x) as [[_ H] _]. lia. Qed.

Lemma bigb_le n : 0 <= n -> bigb n <= n + 4095 + IB + UNIT.
Proof.
intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [| unfold IB, UNIT; lia].
pose proof (round_up_pg_le (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)). lia.
Qed.

Lemma R63X_nil : R63X [] = 0.
Proof. reflexivity. Qed.

Lemma R63X_AMB X0 : AMB X0 -> R63X X0 <= 2 * (MAX_INPUT + 1 + 4095 + IB + UNIT).
Proof.
intros [HL HF]. destruct X0 as [|[p1 n1] [|[p2 n2] [|x l]]]; cbn in HL; [| | | lia].
- rewrite R63X_nil. unfold MAX_INPUT, IB, UNIT; lia.
- rewrite R63X_cons, R63X_nil. apply Forall_cons_iff in HF as [H1 _]. cbn in H1. pose proof (bigb_le n1 ltac:(lia)).
unfold MAX_INPUT, IB, UNIT in *; lia.
- rewrite !R63X_cons, R63X_nil. apply Forall_cons_iff in HF as [H1 HF]. apply Forall_cons_iff in HF as [H2 _]. cbn in H1, H2.
pose proof (bigb_le n1 ltac:(lia)). pose proof (bigb_le n2 ltac:(lia)).
unfold MAX_INPUT, IB, UNIT in *; lia.
Qed.

Lemma room_small X0 Xh n : AMB X0 -> (length Xh < KROOM)%nat -> 0 <= n < MMAP_THRESHOLD ->
PHI P0 + R63X (Xh ++ X0) <= LBUDGET ->
ROOMX (Xh ++ X0) P0 n /\ PHI P0 + R63X (Xh ++ X0) + bigb n <= LBUDGET.
Proof.
intros HA HL Hn HB. split.
- apply ROOMX_intro; [| intros H; lia| unfold MMAP_THRESHOLD in Hn; lia]. intros _.
pose proof (size_to_class_ok n Hn) as [SC _]. rewrite (P0_small _ SC).
pose proof (LRX_le_length (Xh ++ X0) (size_to_class n)) as LE. rewrite length_app in LE.
destruct HA as [HL0 _]. unfold KROOM in HL. lia.
- rewrite bigb_small by lia. lia.
Qed.

Definition ownA (X0 : list (bptr * Z)) (X : list bptr) : assn PState := fun s mo =>
exists Xh, map fst Xh = X /\ Forall small Xh /\ QI (Xh ++ X0) P0 s mo.

Lemma ownA_QI X0 X s mo : ownA X0 X s mo -> exists Xh, QI (Xh ++ X0) P0 s mo.
Proof. intros (Xh & _ & _ & HQ). exists Xh. exact HQ. Qed.

Lemma ownA_step_live X0 X s mo : ownA X0 X s mo -> step_live LBUDGET mo.
Proof. intros (Xh & _ & _ & HQ). exact (QI_step_live _ _ _ _ HQ). Qed.

Lemma ownA_set_so X0 X v s mo : ownA X0 X s mo -> ownA X0 X (set_so_ps v s) mo.
Proof. intros (Xh & HX & HS & HQ). exists Xh. split; [exact HX|]. split; [exact HS|]. apply QI_set_so. exact HQ. Qed.

Lemma ownA_minv X0 X s mo : ownA X0 X s mo -> minv mo /\ m_halted mo = None.
Proof. intros (Xh & _ & _ & HQ). exact (QI_minv _ _ _ _ HQ). Qed.

Lemma ownA_vm X0 X s mo mo' : ownA X0 X s mo -> m_vm mo' = m_vm mo -> minv mo' -> m_halted mo' = None -> ownA X0 X s mo'.
Proof. intros (Xh & HX & HS & HQ) H1 H2 H3. exists Xh. split; [exact HX|]. split; [exact HS|]. eapply QI_fds; eauto. Qed.

Lemma ownA_perm X0 : forall X Y s mo, Permutation X Y -> ownA X0 X s mo -> ownA X0 Y s mo.
Proof.
intros X Y s mo HP (Xh & HX & HS & HQ). subst X.
destruct (Permutation_map_inv fst _ (Permutation_sym HP)) as (Xh' & -> & HP').
exists Xh'. split; [reflexivity|]. split.
- eapply Permutation_Forall; [exact HP'| exact HS].
- eapply QI_perm; [| exact HQ]. apply Permutation_app_tail. exact HP'.
Qed.

Lemma ownA_nil X0 s mo : QI X0 P0 s mo -> ownA X0 [] s mo.
Proof. intros HQ. exists []. split; [reflexivity|]. split; [constructor| exact HQ]. Qed.

Lemma ownA_nil_inv X0 s mo : ownA X0 [] s mo -> QI X0 P0 s mo.
Proof. intros (Xh & HX & _ & HQ). destruct Xh; [exact HQ| discriminate]. Qed.

Definition rtrueA (p : bptr) : Prop := True.

Section HarnessHyps.
Variable X0 : list (bptr * Z).
Hypothesis HA : AMB X0.

Local Notation PMT := X1r2.MMAP_THRESHOLD.
#[using="Type"] Lemma PMT_eq : PMT = MMAP_THRESHOLD.
Proof. reflexivity. Qed.

#[using="HA"] Lemma malloc_A : forall X n, 0 <= n -> n < PMT -> (length X < KROOM)%nat ->
mspecL LBUDGET (ownA X0 X) (raw_malloc n)
(fun r s mo => match r with Some p => ownA X0 (p :: X) s mo | None => ownA X0 X s mo end).
Proof.
intros X n Hn Hs HL. rewrite PMT_eq in Hs. apply mspecL_exI. intros Xh. apply mspecL_pure_l. intros HX. apply mspecL_pure_l. intros HS.
subst X. rewrite length_map in HL.
eapply mspecL_conseq; [apply (raw_malloc_LQ (Xh ++ X0) P0 n Hn)| |].
- intros s mo HQ. split; [exact HQ|]. exact (room_small X0 Xh n HA HL ltac:(lia) (proj2 HQ)).
- intros [p|] s mo H.
+ destruct H as [HQ _]. exists ((p, n) :: Xh). split; [reflexivity|]. split; [constructor; [unfold small; cbn; lia| exact HS]| exact HQ].
+ exists Xh. split; [reflexivity|]. split; [exact HS| exact H].
Qed.

#[using="HA"] Lemma malloc_big_A : forall X n, REALL_MIN <= n -> n < PMT -> (length X < KROOM)%nat ->
mspecL LBUDGET (ownA X0 X) (raw_malloc n)
(fun r s mo => match r with Some p => ownA X0 (p :: X) s mo /\ rtrueA p | None => ownA X0 X s mo end).
Proof.
intros X n Hn Hs HL. eapply mspecL_post; [apply malloc_A; [unfold REALL_MIN in Hn; lia| exact Hs| exact HL]|].
intros [p|] s mo H; [split; [exact H| exact I]| exact H].
Qed.

#[using="HA"] Lemma calloc_A : forall X n m, 0 <= n -> 0 <= m -> n * m < PMT -> (length X < KROOM)%nat ->
mspecL LBUDGET (ownA X0 X) (raw_calloc n m)
(fun r s mo => match r with Some p => ownA X0 (p :: X) s mo | None => ownA X0 X s mo end).
Proof.
intros X n m Hn Hm Hs HL. rewrite PMT_eq in Hs. apply mspecL_exI. intros Xh. apply mspecL_pure_l. intros HX. apply mspecL_pure_l. intros HS.
subst X. rewrite length_map in HL.
eapply mspecL_conseq; [apply (raw_calloc_LQ (Xh ++ X0) P0 n m Hn Hm)| |].
- intros s mo HQ. split; [exact HQ|]. exact (room_small X0 Xh (m * n) HA HL ltac:(nia) (proj2 HQ)).
- intros [p|] s mo H.
+ destruct H as [HQ _]. exists ((p, m * n) :: Xh). split; [reflexivity|]. split; [constructor; [unfold small; cbn; nia| exact HS]| exact HQ].
+ exists Xh. split; [reflexivity|]. split; [exact HS| exact H].
Qed.

#[using="HA"] Lemma calloc_big_A : forall X n m, 0 <= n -> 0 <= m -> REALL_MIN <= n * m -> n * m < PMT -> (length X < KROOM)%nat ->
mspecL LBUDGET (ownA X0 X) (raw_calloc n m)
(fun r s mo => match r with Some p => ownA X0 (p :: X) s mo /\ rtrueA p | None => ownA X0 X s mo end).
Proof.
intros X n m Hn Hm _ Hs HL. eapply mspecL_post; [apply calloc_A; assumption|].
intros [p|] s mo H; [split; [exact H| exact I]| exact H].
Qed.

#[using="HA"] Lemma realloc_A : forall X p n, rtrueA p -> REALL_MIN <= n < PMT -> (length X + 1 < KROOM)%nat ->
mspecL LBUDGET (ownA X0 (p :: X)) (raw_realloc p n)
(fun r s mo => match r with Some q => ownA X0 (q :: X) s mo /\ rtrueA q | None => ownA X0 (p :: X) s mo end).
Proof.
intros X p n _ Hn HL. rewrite PMT_eq in Hn. apply mspecL_exI. intros Xh. apply mspecL_pure_l. intros HX. apply mspecL_pure_l. intros HS.
destruct Xh as [|[p' k] Xh]; [discriminate|]. cbn in HX. injection HX as Ep EX. subst p' X. rewrite length_map in HL.
apply Forall_cons_iff in HS as [Hk HS].
eapply mspecL_conseq; [apply (raw_realloc_LQ (Xh ++ X0) P0 p k n); unfold REALL_MIN in Hn; lia| |].
- intros s mo HQ. split; [exact HQ|].
change ((p, k) :: Xh ++ X0) with (((p, k) :: Xh) ++ X0).
apply (room_small X0 ((p, k) :: Xh) n HA ltac:(cbn [length]; lia) ltac:(unfold REALL_MIN in Hn; lia)). exact (proj2 HQ).
- intros [q|] s mo H.
+ destruct H as (k' & Hk' & HQ). split; [| exact I]. exists ((q, k') :: Xh). split; [reflexivity|]. split; [| exact HQ].
constructor; [| exact HS]. unfold small in *; cbn in *. unfold REALL_MIN in Hn. destruct Hk' as [-> | ->]; lia.
+ exists ((p, k) :: Xh). split; [reflexivity|]. split; [constructor; assumption| exact H].
Qed.

#[using="Type"] Lemma free_A : forall X p, mspecL LBUDGET (ownA X0 (p :: X)) (raw_free p) (fun _ => ownA X0 X).
Proof.
intros X p. apply mspecL_exI. intros Xh. apply mspecL_pure_l. intros HX. apply mspecL_pure_l. intros HS.
destruct Xh as [|[p' k] Xh]; [discriminate|]. cbn in HX. injection HX as Ep EX. subst p' X.
apply Forall_cons_iff in HS as [_ HS].
eapply mspecL_post; [apply (raw_free_LQ (Xh ++ X0) P0 p k)|]. intros [] s mo HQ. exists Xh. split; [reflexivity|]. split; [exact HS| exact HQ].
Qed.

#[using="Type"] Lemma notify_A : forall X msg, msg_ok msg -> mspecL LBUDGET (ownA X0 X) (io_notify msg) (fun _ => ownA X0 X).
Proof. intros X msg _. apply (io_notify_L LBUDGET (ownA X0 X) (ownA_step_live X0 X)). Qed.

#[using="Type"] Lemma warning_A : forall X msg, msg_ok msg -> mspecL LBUDGET (ownA X0 X) (io_warning msg) (fun _ => ownA X0 X).
Proof. intros X msg _. apply (io_warning_L LBUDGET (ownA X0 X) (ownA_step_live X0 X)). Qed.

#[using="HA"] Theorem fuzz_one_L : forall X payload, bytes_ok payload -> (length X + HROOM <= KROOM)%nat ->
mspecL LBUDGET (ownA X0 X) (fuzz_one payload) (fun _ => ownA X0 X).
Proof.
intros X payload Hb HL. unfold fuzz_one.
exact (X1pb.LLVMFuzzerTestOneInput_spec (ownA X0) raw_malloc raw_calloc raw_realloc raw_free io_notify io_warning KROOM
calloc_A rtrueA malloc_big_A calloc_big_A realloc_A free_A (ownA_perm X0) notify_A warning_A X payload Hb HL).
Qed.

#[using="HA"] Lemma fuzz_one_L0 : forall payload, bytes_ok payload ->
mspecL LBUDGET (QI X0 P0) (fuzz_one payload) (fun _ => QI X0 P0).
Proof.
intros payload Hb. eapply mspecL_conseq; [apply (fuzz_one_L [] payload Hb); unfold HROOM, KROOM; cbn; lia| |].
- intros s mo Ho. apply ownA_nil. exact Ho.
- intros r s mo Ho. apply ownA_nil_inv. exact Ho.
Qed.
End HarnessHyps.

Lemma io_emit_QI : forall X rc, mspecL LBUDGET (QI X P0) (io_emit rc) (fun _ => QI X P0).
Proof. intros X rc. apply (io_emit_L LBUDGET (QI X P0) (QI_step_live X P0) (fun v s mo H => QI_set_so X P0 s mo v H)). Qed.

Lemma run_calls_L X0 n payload rc : AMB X0 -> bytes_ok payload ->
mspecL LBUDGET (QI X0 P0) (run_calls io_emit fuzz_one n payload rc) (fun _ => QI X0 P0).
Proof.
intros HA Hb. revert rc. induction n as [|n IH]; intros rc; cbn [run_calls].
- apply mspecL_ret. intros s mo H. exact H.
- eapply mspecL_seq; [apply fuzz_one_L0; assumption|]. intros rc'. eapply mspecL_seq; [apply io_emit_QI|]. intros _. apply IH.
Qed.

Lemma text_ok b cap m : 0 <= cap <= MAX_INPUT -> 0 <= m <= MAX_INPUT ->
ROOMX [(b, cap)] P0 m /\ PHI P0 + R63X [(b, cap)] + bigb m <= LBUDGET.
Proof.
intros Hcap Hm. split.
- apply ROOMX_intro; [| | unfold MAX_INPUT in Hm; lia].
+ intros LT. pose proof (size_to_class_ok m ltac:(lia)) as [SC _]. rewrite (P0_small _ SC).
pose proof (LRX_le_length [(b, cap)] (size_to_class m)). cbn [length] in H. lia.
+ intros GE. rewrite P0_63. pose proof (n63X_le_length [(b, cap)]). cbn [length] in H. lia.
- pose proof (R63X_AMB [(b, cap)] (AMB_one b cap ltac:(lia))). pose proof (bigb_le m ltac:(lia)). pose proof PHI_P0.
unfold MAX_INPUT, IB, UNIT in *. lia.
Qed.

Theorem target_run_L b cap cfg payload : 0 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT -> bytes_ok payload ->
mspecL LBUDGET (QI [(b, cap)] P0) (target_run raw_malloc raw_free io_emit fuzz_one cfg payload) (fun _ => QI [(b, cap)] P0).
Proof.
intros Hcap Hpl Hb. unfold target_run. pose proof (zlength_nonneg payload) as PL0.
eapply mspecL_bind with (Q1 := fun t s mo => match t with
| Some (Some tp) => QI [(tp, zlength payload); (b, cap)] P0 s mo
| Some None => QI [(b, cap)] P0 s mo
| None => QI [(b, cap)] P0 s mo end).
{ destruct (zlength payload =? 0); [apply mspecL_ret; intros s mo H; exact H|].
eapply mspecL_bind.
- eapply mspecL_pre; [apply (raw_malloc_LQ [(b, cap)] P0 (zlength payload)); lia|].
intros s mo HQ. split; [exact HQ|]. exact (text_ok b cap (zlength payload) Hcap ltac:(lia)).
- intros [tp|]; apply mspecL_ret; cbn; [intros s mo [H _]; exact H| intros s mo H; exact H]. }
intros [[tp|]|]; cbn beta iota.
- eapply mspecL_seq; [apply (run_calls_L [(tp, zlength payload); (b, cap)]); [apply AMB_two; lia| exact Hb]|].
intros status. eapply mspecL_seq; [apply raw_free_LQ|]. intros _. apply mspecL_ret. intros s mo H; exact H.
- eapply mspecL_seq; [apply (run_calls_L [(b, cap)]); [apply AMB_one; lia| exact Hb]|].
intros status. eapply mspecL_seq; [apply mspecL_ret; intros s mo H; exact H|]. intros _. apply mspecL_ret. intros s mo H; exact H.
- apply mspecL_ret. intros s mo H; exact H.
Qed.

Theorem run_L b cap cfg payload : 0 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT -> bytes_ok payload ->
mspecL LBUDGET (QI [(b, cap)] P0) (run cfg payload) (fun _ => QI [(b, cap)] P0).
Proof. intros. unfold run. apply target_run_L; assumption. Qed.
