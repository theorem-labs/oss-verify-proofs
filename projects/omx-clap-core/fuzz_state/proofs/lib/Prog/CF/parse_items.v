From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import ReaderKB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memset_c parse_items_prefix.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger parse_items_model parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import grow_c parse_string_c fuzz_free_c parse_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import parse_items_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require PvGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Local Open Scope Z_scope.
Local Notation calls := PjGrammar.calls (only parsing).

Lemma pi_mkR_of : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 R,
  xregs_eqv (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31) R ->
  mkR_of R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 R H.
  unfold mkR_of. repeat (rewrite <- H by reflexivity). reflexivity.
Qed.

Lemma pi_frame_mv : forall m m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8,
  pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  (forall x, f <= x < f + 80 -> mbyte rsegs m' x = mbyte rsegs m x) -> 0 <= f -> f + 80 <= 2 ^ 64 ->
  pi_frame m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8.
Proof.
  intros m m' f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9) HM H0 H1.
  assert (K : forall a w, bytes_at rsegs m a (le8 w) -> f <= a -> a + 8 <= f + 80 -> bytes_at rsegs m' a (le8 w)).
  { intros a w Hb Ha1 Ha2. apply (pis_bytes_mv rsegs m m' a a _ Hb); [lia | rewrite length_le8; cbn; lia |].
    intros i Hi. rewrite length_le8 in Hi. cbn in Hi. apply HM. lia. }
  unfold pi_frame.
  split; [apply (K _ _ F0); lia|]. split; [apply (K _ _ F1); lia|]. split; [apply (K _ _ F2); lia|].
  split; [apply (K _ _ F3); lia|]. split; [apply (K _ _ F4); lia|]. split; [apply (K _ _ F5); lia|].
  split; [apply (K _ _ F6); lia|]. split; [apply (K _ _ F7); lia|]. split; [apply (K _ _ F8); lia|].
  apply (K _ _ F9); lia.
Qed.

Lemma pi_in_mv : forall segs m m' q text len p dd tb,
  pj_in_ok segs m q text len p dd tb ->
  (forall x, q <= x < q + 24 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  bytes_at segs m' text tb -> pj_in_ok segs m' q text len p dd tb.
Proof.
  intros segs m m' q text len p dd tb H HQ HT.
  pose proof (pj_in_ok_bounds segs m q text len p dd tb H) as (Q0 & Q1 & _).
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
  refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj HT (conj H11 H12))))))))))).
  - apply (pis_bytes_mv segs m m' q q _ H1); [lia | rewrite length_le8; cbn; lia |].
    intros i Hi. rewrite length_le8 in Hi. cbn in Hi. exact (proj1 (HQ (q + i) ltac:(lia))).
  - apply (pis_bytes_mv segs m m' (q + 8) (q + 8) _ H2); [lia | rewrite length_le8; cbn; lia |].
    intros i Hi. rewrite length_le8 in Hi. cbn in Hi. exact (proj1 (HQ (q + 8 + i) ltac:(lia))).
  - apply (pis_bytes_mv segs m m' (q + 16) (q + 16) _ H3); [lia | rewrite length_le4; cbn; lia |].
    intros i Hi. rewrite length_le4 in Hi. cbn in Hi. exact (proj1 (HQ (q + 16 + i) ltac:(lia))).
  - destruct H4 as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|].
    intros i Hi. apply (proj2 (HQ (q + i) ltac:(lia))). exact (W3 i Hi).
Qed.

Definition pi_c2 (cap : nat) : nat := if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.

Lemma pi_cap2 : forall cap, Z.of_nat (pi_c2 cap) = cap2 (Z.of_nat cap).
Proof.
  intros [|c]; unfold pi_c2, cap2; cbn [Nat.eqb]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) by lia. lia.
Qed.

Lemma pi_take : forall (l : list bool) k, take (skipn k l) = (nth k l true, skipn (S k) l).
Proof. induction l as [|b l IH]; intros [|k]; cbn [skipn take nth]; try reflexivity. apply IH. Qed.

Lemma pi_rm1_perm : forall k s, In k s -> Permutation s (k :: rm1n k s).
Proof.
  intros k s. induction s as [|x s IH]; intros H; [destruct H|].
  cbn [rm1n]. destruct (Nat.eqb_spec x k) as [->|Hne]; [apply Permutation_refl|].
  destruct H as [H|H]; [contradiction|].
  eapply Permutation_trans; [apply perm_skip; exact (IH H)|]. apply perm_swap.
Qed.

Lemma pi_lsz_grow : forall s l m n, Permutation (Z.of_nat m :: l) (map Z.of_nat s) -> (0 < m)%nat ->
  Permutation (Z.of_nat n :: l) (map Z.of_nat (lsz_ev s (EGrow m n))).
Proof.
  intros s l [|m] n HP Hm; [lia|]. cbn [lsz_ev map].
  assert (Hin : In (S m) s).
  { assert (H : In (Z.of_nat (S m)) (map Z.of_nat s)) by (apply (Permutation_in _ HP); left; reflexivity).
    apply in_map_iff in H as (x & Ex & Hx). apply Nat2Z.inj in Ex. subst x. exact Hx. }
  pose proof (Permutation_map Z.of_nat (pi_rm1_perm (S m) s Hin)) as P2. cbn [map] in P2.
  apply perm_skip. eapply Permutation_cons_inv. exact (Permutation_trans HP P2).
Qed.

Lemma pi_lsz_new : forall s l n, Permutation l (map Z.of_nat s) ->
  Permutation (Z.of_nat n :: l) (map Z.of_nat (lsz_ev s (EGrow 0 n))).
Proof. intros s l n HP. cbn [lsz_ev map]. apply perm_skip. exact HP. Qed.

Lemma pi_nlive_app : forall t1 t2, nlive (t1 ++ t2) = nlive t1 + nlive t2.
Proof. induction t1 as [|e t1 IH]; intros t2; cbn [app nlive]; [lia | rewrite IH; lia]. Qed.

Lemma pi_lsz_app : forall t1 t2, lsz (t1 ++ t2) = fold_left lsz_ev t2 (lsz t1).
Proof. intros t1 t2. unfold lsz. apply fold_left_app. Qed.

Lemma pi_lsum_perm : forall l l', Permutation l l' -> lsum l = lsum l'.
Proof. intros l l' H. rewrite !lsum_zl. apply zl_perm. apply Permutation_map. exact H. Qed.

Lemma pi_lsum_app : forall l l', lsum (l ++ l') = lsum l + lsum l'.
Proof. intros l l'. rewrite !lsum_zl, map_app. apply zl_app. Qed.

Lemma pi_hpeak_held : forall t, held t <= hpeak t.
Proof. induction t as [|e t IH]; cbn [held hpeak]; lia. Qed.

Lemma pi_cap2_gt : forall c, 0 <= c -> c < cap2 c.
Proof. intros c Hc. unfold cap2. destruct (Z.eqb_spec c 0); lia. Qed.

Lemma pi_lsum_kids : forall a c, 0 <= c -> lsum (kids_blk a c) = 56 * c.
Proof. intros a c Hc. unfold kids_blk. destruct (Z.eqb_spec c 0) as [->|E]; cbn [lsum]; lia. Qed.

Lemma pi_lsum_keys : forall a c, 0 <= c -> lsum (keys_blk 6 a c) = 8 * c.
Proof. intros a c Hc. unfold keys_blk. destruct (Z.eqb_spec c 0) as [->|E]; cbn; lia. Qed.

Lemma pi_lsz_blk : forall s l a c n, Permutation (map snd (kids_blk a (Z.of_nat c)) ++ l) (map Z.of_nat s) ->
  Permutation (Z.of_nat n :: l) (map Z.of_nat (lsz_ev s (EGrow (56 * c) n))).
Proof.
  intros s l a [|c] n H; unfold kids_blk in H.
  - cbn in H. cbn [Nat.mul]. apply pi_lsz_new. exact H.
  - rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) in H by lia. cbn [map snd app] in H.
    apply pi_lsz_grow; [|lia]. rewrite Nat2Z.inj_mul. exact H.
Qed.

Lemma pi_lsz_kblk : forall s l a c n, Permutation (map snd (keys_blk 6 a (Z.of_nat c)) ++ l) (map Z.of_nat s) ->
  Permutation (Z.of_nat n :: l) (map Z.of_nat (lsz_ev s (EGrow (8 * c) n))).
Proof.
  intros s l a [|c] n H; unfold keys_blk in H.
  - cbn in H. cbn [Nat.mul]. apply pi_lsz_new. exact H.
  - rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) in H by lia. change (6 =? 6) with true in H.
    cbn [orb negb map snd app] in H.
    apply pi_lsz_grow; [|lia]. rewrite Nat2Z.inj_mul. exact H.
Qed.

Lemma pi_nl_kids : forall a c n, Z.of_nat (length (kids_blk a (Z.of_nat c))) + nlive_ev (EGrow (56 * c) n) = 1.
Proof.
  intros a [|c] n; unfold kids_blk; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) by lia. cbn [length].
  replace (56 * S c)%nat with (S (55 + 56 * c))%nat by lia. cbn [nlive_ev]. lia.
Qed.

Lemma pi_nl_keys : forall a c n, Z.of_nat (length (keys_blk 6 a (Z.of_nat c))) + nlive_ev (EGrow (8 * c) n) = 1.
Proof.
  intros a [|c] n; unfold keys_blk; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) by lia. change (6 =? 6) with true. cbn [orb negb length].
  replace (8 * S c)%nat with (S (7 + 8 * c))%nat by lia. cbn [nlive_ev]. lia.
Qed.

Lemma pip_pv_fail : forall (ra gp tp t0 t1 t2 s0 w a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f q v n : Z) (o : bool)
    (r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 : word),
  bv_unsigned w <> 0 -> pi_frame m f r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 ->
  bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) -> wr_at rsegs m (v + 40) 8 -> 0 <= n -> n + 1 < 2 ^ 64 ->
  disjoint_from [(f, f + 80)] (v + 40) 8 ->
  evt rsegs
    (fun ms' => exists m' : word -> option byte,
       ms' = MS (mkR r0 (Z_to_bv 64 (f + 80)) gp tp t0 t1 t2 c0 c1 s0 (Z_to_bv 64 (n + 1)) a2 a3 a4 a5 a6 a7
                  c2 c3 c4 c5 c6 c7 c8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc r0) fc None m' (seg_rom rsegs) /\
       chg [(v + 40, v + 48)] m m' /\ bytes_at rsegs m' (v + 40) (le8 (Z_to_bv 64 (n + 1))))
    (MS (mkR ra (Z_to_bv 64 f) gp tp t0 t1 t2 s0 (Z_to_bv 64 q) w a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (if o then 1 else 0))
           (Z_to_bv 64 v) (Z_to_bv 64 32) (Z_to_bv 64 44) s6 (Z_to_bv 64 WSM) s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 0x151bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 w a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f q v n o
    r0 c0 c1 c2 c3 c4 c5 c6 c7 c8 Hw FR HN WN Hn Hn1 DN.
  cbn [disjoint_from] in DN.
  pose proof FR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
  pose proof (bytes_at_bound rsegs m _ _ F0) as FB0. pose proof (bytes_at_bound rsegs m _ _ F9) as FB9.
  pose proof (bytes_at_bound rsegs m _ _ HN) as BN.
  rewrite length_le8 in FB0, FB9, BN. cbn in FB0, FB9, BN.
  pose proof WN as (WN0 & WN1 & _).
  pose proof (pip_rd8 _ _ _ HN) as RN.
  pose proof (chg_refl [(v + 40, v + 48)] m) as CH1.
  step. step. sok (v + 40) 8%nat. step. mst.
  step. if_cases H1; zify_cond H1.
  - eapply evt_cut; [eapply pip_epi; frame_pack | intros ms' ->].
    apply evt_done. eexists. split; [reflexivity|]. split; [exact CH1 | eassumption].
  - exfalso. lia.
Qed.

Lemma pi_room_bind : forall (F : ResForm) (A C : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M C) b,
  room_run F b (snd (fst (jbind m k []))) -> room_run F b (snd (fst (m []))).
Proof.
  intros F A C m k b. unfold jbind. destruct (m []) as [[[a|] t] o']; cbn [fst snd]; [|tauto].
  destruct (k a o') as [[r t'] o'']; cbn [fst snd]. intros H. exact (proj1 (room_run_app F t b t' H)).
Qed.

Lemma pi_rest_len : forall tb text len p, Z.of_nat (length tb) = len -> text <= p <= text + len ->
  Z.of_nat (length (rest_at tb text p)) = text + len - p.
Proof. intros tb text len p H Hp. unfold rest_at, zb. rewrite length_map, length_skipn. lia. Qed.

Lemma pi_mrd_eq : forall segs (m m' : word -> option byte) x, m' x = m x -> lib.Lib.Mem.mrd segs m' x = lib.Lib.Mem.mrd segs m x.
Proof. intros segs m m' x E. unfold lib.Lib.Mem.mrd. rewrite E. reflexivity. Qed.

Lemma pi_wr_stk : forall segs m lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at segs m a n.
Proof. intros segs m lo hi a n (H0 & H1 & H) Ha Hn Hn0. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))). Qed.

Lemma pi_fd_store : forall segs m m' lblk v o num kids keys cap ts ns Di dd Dn Dt q0,
  pis_open segs m lblk v o num kids keys cap (Z.of_nat (length ts)) ts ns Di ->
  Z.of_nat (length ts) < cap ->
  Forall (fun t => (depth t <= dd)%nat) ts ->
  pj_fd segs m lblk dd (kids + 56 * Z.of_nat (length ts)) Dt ->
  (if o then pj_key segs m lblk true (keys + 8 * Z.of_nat (length ts)) Dn else Dn = []) ->
  NoDup (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_apart (Dn ++ Dt) v ->
  pj_hdr segs m' v (5 + pis_oz o) num 0 kids keys (Z.of_nat (length ts) + 1) cap ->
  (forall b x, In b (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_holds b x ->
     0 <= x < 2 ^ 64 /\ ~ (q0 <= x < q0 + 24)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (v <= x < v + 56) -> ~ (q0 <= x < q0 + 24) -> pis_same segs m m' x) ->
  pj_fd segs m' lblk (S dd) v (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt).
Proof.
  intros segs m m' lblk v o num kids keys cap ts ns Di dd Dn Dt q0 H Hlc HF Ht Hn HN HA Hh' HQ HM.
  pose proof H as (HN0 & HA0 & Hh & Hs & Hk & Hi).
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (Hks : In (kids, 56 * cap) (pis_slots o kids keys cap))
    by (unfold pis_slots, kids_blk; rewrite Ec; apply in_or_app; left; left; reflexivity).
  assert (Hys : o = true -> In (keys, 8 * cap) (pis_slots o kids keys cap))
    by (intros Eo; unfold pis_slots, kids_blk, keys_blk; rewrite Eo, Ec; cbn; right; left; reflexivity).
  assert (IN1 : forall b, In b (pis_slots o kids keys cap) -> In b (pis_slots o kids keys cap ++ Di))
    by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (IN2 : forall b, In b (pis_slots o kids keys cap) -> In b (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt))
    by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (IN3 : forall b, In b Di -> In b (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt))
    by (intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (IN4 : forall b, In b Dt -> In b (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt))
    by (intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb).
  assert (HMb : forall b x, In b (pis_slots o kids keys cap ++ Di ++ Dn ++ Dt) -> pj_holds b x -> ~ (v <= x < v + 56) ->
             pis_same segs m m' x).
  { intros b x Hb Hx Hv. destruct (HQ b x Hb Hx) as [Hr Hq]. exact (HM x Hr Hv Hq). }
  assert (H' : pis_open segs m' lblk v o num kids keys cap (Z.of_nat (length ts) + 1) ts ns Di).
  { apply (pis_frame segs m lblk m' lblk v o num kids keys cap _ ts ns Di num _ H Hh' ltac:(lia)
      (pis_open_lblk segs m lblk v o num kids keys cap _ ts ns Di H)).
    intros x [Hx|[(Eo & Hx)|(b & Hb & Hx)]].
    - apply (HMb (kids, 56 * cap) x (IN2 _ Hks)); [unfold pj_holds; cbn [fst snd]; lia|].
      apply (HA0 (kids, 56 * cap) x (IN1 _ Hks)). unfold pj_holds; cbn [fst snd]. lia.
    - apply (HMb (keys, 8 * cap) x (IN2 _ (Hys Eo))); [unfold pj_holds; cbn [fst snd]; lia|].
      apply (HA0 (keys, 8 * cap) x (IN1 _ (Hys Eo))). unfold pj_holds; cbn [fst snd]. lia.
    - apply (HMb b x (IN3 _ Hb) Hx). apply (HA0 b x); [apply in_or_app; right; exact Hb | exact Hx]. }
  apply (pis_fd_next segs m' lblk v o num kids keys cap _ ts ns Di dd Dn Dt H' eq_refl HF).
  - apply (pis_fd_frame segs dd m lblk m' lblk _ Dt Ht); [intros a k _ Hl; exact Hl|].
    intros x [Hx|(b & Hb & Hx)].
    + apply (HMb (kids, 56 * cap) x (IN2 _ Hks)); [unfold pj_holds; cbn [fst snd]; lia|].
      apply (HA0 (kids, 56 * cap) x (IN1 _ Hks)). unfold pj_holds; cbn [fst snd]. lia.
    + apply (HMb b x (IN4 _ Hb) Hx). apply (HA b x); [apply in_or_app; right; exact Hb | exact Hx].
  - destruct o; [|exact Hn].
    cbn [pj_key] in Hn |- *. destruct Hn as (x & Hx & Hz). exists x. split; [|exact Hz].
    apply (pis_u64_frame segs m m'); [exact Hx|]. intros y Hy.
    refine (proj1 (HMb (keys, 8 * cap) y (IN2 _ (Hys eq_refl)) ltac:(unfold pj_holds; cbn [fst snd]; lia) _)).
    apply (HA0 (keys, 8 * cap) y (IN1 _ (Hys eq_refl))). unfold pj_holds; cbn [fst snd]. lia.
  - exact HN.
  - exact HA.
Qed.

Lemma pi_rest_suf : forall tb text len P r, Z.of_nat (length tb) = len -> text <= P <= text + len ->
  rk_suf r (rest_at tb text P) -> rest_at tb text (text + len - Z.of_nat (length r)) = r.
Proof.
  intros tb text len P r HL HP (u & Hu). unfold rest_at, zb in *.
  assert (E : Z.to_nat (text + len - Z.of_nat (length r) - text) = (length u + Z.to_nat (P - text))%nat).
  { apply (f_equal (@length Z)) in Hu. rewrite length_map, length_skipn, length_app in Hu. lia. }
  rewrite E, <- skipn_skipn, <- skipn_map, Hu, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma pi_jafter_f : forall d n cap acc y ok, jafter d false n cap acc y ok = jval d false n cap acc [] y ok.
Proof.
  intros d n cap acc y ok. unfold jafter, jbind, jr_name, jret. cbv beta iota. cbn [fst snd app].
  destruct (jval d false n cap acc [] y ok) as [[r t] o']. reflexivity.
Qed.

Lemma pi_nm_val : forall y z ok, skip y = 34 :: z ->
  jr_name true y ok =
  match scan z with
  | None => (None, [], ok)
  | Some Q =>
      if fst (take ok) then
        match decode z with
        | None => (None, [EAlloc (S Q); EFree (S Q)], snd (take ok))
        | Some (s, r) =>
            match skip r with
            | c :: r1 => if c =? 58 then (Some (s, r1), [EAlloc (S Q)], snd (take ok))
                         else (None, [EAlloc (S Q); EFree (S Q)], snd (take ok))
            | [] => (None, [EAlloc (S Q); EFree (S Q)], snd (take ok))
            end
        end
      else (None, [EFail (S Q)], snd (take ok))
  end.
Proof.
  intros y z ok H. unfold jr_name. rewrite H. cbv beta iota.
  replace (34 =? 34) with true by reflexivity. cbv beta iota.
  unfold jr_string, jalloc, jfree, jret, jrefuse, sblock, jbind. cbv beta iota.
  destruct (scan z) as [Q|]; cbv beta iota; [|reflexivity].
  destruct (take ok) as [[|] ok1]; cbv beta iota; cbn [fst snd]; [|reflexivity].
  destruct (decode z) as [[s r]|]; cbv beta iota; [|reflexivity].
  destruct (skip r) as [|c r1]; cbv beta iota; [reflexivity|]. destruct (c =? 58); reflexivity.
Qed.

Lemma pi_rest_app : forall tb text P l r, text <= P -> rest_at tb text P = l ++ r ->
  rest_at tb text (P + Z.of_nat (length l)) = r.
Proof.
  intros tb text P l r HP H. unfold rest_at, zb in *.
  replace (Z.to_nat (P + Z.of_nat (length l) - text)) with (length l + Z.to_nat (P - text))%nat by lia.
  rewrite <- skipn_skipn, <- skipn_map, H. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma pi_rest_sk : forall tb text len P x b, Z.of_nat (length tb) = len -> text <= P <= x -> x < text + len ->
  skip (rest_at tb text P) = b :: rest_at tb text (x + 1) -> rest_at tb text x = b :: rest_at tb text (x + 1).
Proof.
  intros tb text len P x b HL HP Hx H.
  destruct (rk_suf_skip (rest_at tb text P)) as (u & Hu). rewrite H in Hu.
  pose proof (pi_rest_app tb text P u _ ltac:(lia) Hu) as E.
  pose proof (pi_rest_len tb text len P HL ltac:(lia)) as L1.
  pose proof (pi_rest_len tb text len (x + 1) HL ltac:(lia)) as L2.
  rewrite Hu, length_app in L1. cbn [length] in L1.
  replace (P + Z.of_nat (length u)) with x in E by lia. exact E.
Qed.

Lemma pi_skipn_nth : forall (T : Type) n (l : list T) c r, skipn n l = c :: r -> nth_error l n = Some c.
Proof.
  intros T n. induction n as [|n IH]; intros [|x l] c r H; cbn in *; try discriminate.
  - injection H as -> _. reflexivity.
  - exact (IH l c r H).
Qed.

Lemma pi_ra_nth : forall (tb : list byte) text P b y, rest_at tb text P = b :: y ->
  nth_error tb (Z.to_nat (P - text)) = Some (Z_to_bv 8 b).
Proof.
  intros tb text P b y H. unfold rest_at, zb in H.
  destruct (skipn (Z.to_nat (P - text)) tb) as [|c r] eqn:E; [discriminate|].
  cbn [map] in H. injection H as Hb _. rewrite (pi_skipn_nth _ _ _ c r E). rewrite <- Hb. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma pi_nm_nq : forall y ok, (forall c r, skip y = c :: r -> c <> 34) -> jr_name true y ok = (None, [], ok).
Proof.
  intros y ok H. unfold jr_name. destruct (skip y) as [|b z] eqn:E; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq b 34) (H b z eq_refl)). reflexivity.
Qed.

Lemma pi_ext_refl : forall (A : Type) (full : option A * list ev * list bool), ext full [] full.
Proof. intros A [[r t] o']. reflexivity. Qed.

Section PI.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Notation segs := (ms_segs B).

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (Lam0 : list (Z * Z)) (peak0 cnt0 fail0 : Z) (b0 : rf_R RF) (q text len p0 : Z) (tb : list byte) (v : Z)
  (o : bool) (d : nat).

Hypothesis ENV : reader_env B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0.
Hypothesis LG0 : ledger B L0 A0 mem0 Lam0 peak0 cnt0 fail0.
Hypothesis RES0 : rf_ok RF A0 b0.
Hypothesis R10 : getr regs0 10 = Z_to_bv 64 q.
Hypothesis R11 : getr regs0 11 = Z_to_bv 64 v.
Hypothesis R12 : getr regs0 12 = Z_to_bv 64 (if o then 1 else 0).
Hypothesis PIN0 : pj_in_ok segs mem0 q text len p0 (Z.of_nat d) tb.
Hypothesis PLT : p0 < text + len.
Hypothesis PNTH : nth_error tb (Z.to_nat (p0 - text)) = Some (Z_to_bv 8 (opener o)).
Hypothesis QSP : spZ regs0 <= q.
Hypothesis QAUX : st_init_done A0 = false -> auxv_pre B (ly_sec L0) (q + 24) mem0.
Hypothesis MXR : Z.of_nat (PjRoundTrip.maxrun (zb tb)) < 2 ^ 30.
Hypothesis TOK : text_ok B L0 A0 Lam0 regs0 text len.
Hypothesis VNZ : v <> 0.
Hypothesis VZ : pj_zero segs mem0 v.
Hypothesis RPL : rplace B L0 A0 Lam0 regs0 mem0 v.
Hypothesis DJV : Frame.disjoint_from [(text, text + len); (q, q + 24)] v 56.
Hypothesis DJS : Frame.disjoint_from [(q, q + 24); (text, text + len); (v, v + 56)]
  (spZ regs0 - PARSE_ITEMS_K d) (PARSE_ITEMS_K d).
Hypothesis CNT : cnt0 + 2 * Z.of_nat (length (rest_at tb text p0)) + 2 < 2 ^ 64 - 1.
Hypothesis ROOM : room_run RF b0 (snd (fst (jr_items jr_strtod d o (rest_at tb text p0) []))).

Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis CO : ctx_owned B API.
Hypothesis PVC : (d < MAXD)%nat -> forall fx', @parse_value_contract fx' rc B API RF (S d).
Hypothesis GRC : forall fx', @grow_contract fx' rc B API RF.
Hypothesis PSC : forall fx', @parse_string_contract fx' rc B API RF.
Hypothesis MSC : memset_contract.
Hypothesis FFC : forall fx', @fuzz_free_contract fx' rc B API RF.

Definition pi_post : config -> Prop :=
  fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' Lam' peak' cnt' fail' ok res tr okr D,
    c' = mkCfg (@mkst fx' regs' (getr regs0 1) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\ fregs_kept fx fx' /\
    rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 (rd_writes q v D) (fun _ _ => False) L' A' regs' mem' md' /\
    rd_cells B mem' /\
    ledger B L' A' mem' Lam' peak' cnt' fail' /\
    jr_items jr_strtod d o (rest_at tb text p0) ok = (res, tr, okr) /\
    oks ok cnt0 fail0 (calls tr) /\
    cnt' = cnt0 + Z.of_nat (calls tr) /\
    fail_after cnt0 fail0 (calls tr) fail' /\
    Permutation Lam' (D ++ Lam0) /\ Permutation (map snd D) (map Z.of_nat (lsz tr)) /\
    Z.of_nat (length D) = nlive tr /\ new_blks L0 A0 D /\
    peak' = Z.max peak0 (lsum Lam0 + hpeak tr) /\
    hpeak tr <= 224 * Z.of_nat (length (rest_at tb text p0)) + 512 * Z.of_nat (MAXD - d) /\
    rf_ok RF A' (rf_run RF b0 tr) /\
    match res with
    | Some (t, r) =>
        getr regs' 10 = Z_to_bv 64 0 /\
        pj_in_ok segs mem' q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
        pj_node segs mem' (lin Lam') v t D /\
        lsum D <= 224 * (Z.of_nat (length (rest_at tb text p0)) - Z.of_nat (length r))
    | None =>
        getr regs' 10 = Z_to_bv 64 (-1) /\
        pj_in_after B mem' q text len (Z.of_nat d + 1) 33 /\
        pj_fd segs mem' (lin Lam') (MAXD - d) v D
    end.

Definition pi_f : Z := spZ regs0 - 80.

Definition pi_x : list Z := rest_at tb text p0.

Definition pi_ok : list bool := okf cnt0 fail0 (S (Z.to_nat (fail0 - cnt0))).

Definition pi_E0 (a : Z) : Prop := v <= a < v + 56 \/ pj_in_set q a \/ alloc_statics a.

Definition pi_lo : Z := Z.max (q + 24) (if spZ regs0 <=? v then v + 56 else spZ regs0).

Definition pi_cs (R : bvmap 5 word) : Prop :=
  getr R 2 = Z_to_bv 64 pi_f /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  getr R 8 = Z_to_bv 64 (-1) /\ getr R 9 = Z_to_bv 64 q /\ getr R 18 = Z_to_bv 64 (pis_oz o) /\
  getr R 19 = Z_to_bv 64 v /\ getr R 20 = Z_to_bv 64 32 /\ getr R 21 = Z_to_bv 64 44 /\
  getr R 22 = Z_to_bv 64 34 /\ getr R 23 = Z_to_bv 64 WSM /\ getr R 24 = Z_to_bv 64 58 /\
  getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27.

Definition pi_frm (m : word -> option byte) : Prop :=
  pi_frame m pi_f (getr regs0 1) (getr regs0 8) (getr regs0 9) (getr regs0 18) (getr regs0 19) (getr regs0 20)
    (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24).

Definition pi_glob (fxc : YK11.FPState) (Lc : layout) (Ac : astate) (m : word -> option byte) (mdc : Model)
    (Lamc : list (Z * Z)) (tr : list ev) (D : list (Z * Z)) : Prop :=
  frm_zero (@fp_csr fxc) /\ fregs_kept fx fxc /\
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 m mdc /\
  rd_cells B m /\ pi_frm m /\
  Permutation Lamc (D ++ Lam0) /\ Permutation (map snd D) (map Z.of_nat (lsz tr)) /\
  Z.of_nat (length D) = nlive tr /\ new_blks L0 A0 D /\
  rf_ok RF Ac (rf_run RF b0 tr) /\
  (st_init_done Ac = false -> auxv_pre B (ly_sec L0) pi_lo m).

Definition pi_inv (w : nat) (c : config) : Prop :=
  exists (fxc : YK11.FPState) (R : bvmap 5 word) (m : word -> option byte) (mdc : Model) (Lc : layout) (Ac : astate)
    (Lamc : list (Z * Z)) (tr : list ev) (D : list (Z * Z)) (n cap : nat) (acc : list (list Z * jv))
    (P num kids keys : Z) (Di : list (Z * Z)),
    c = mkCfg (@mkst fxc R (Z_to_bv 64 0x150d8) m (seg_rom segs)) mdc /\
    (d < MAXD)%nat /\ pi_cs R /\
    pi_glob fxc Lc Ac m mdc Lamc tr D /\
    ledger B Lc Ac m Lamc (Z.max peak0 (lsum Lam0 + hpeak tr)) (cnt0 + Z.of_nat (calls tr)) fail0 /\
    ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls tr)) /\
    pj_in_ok segs m q text len P (Z.of_nat d + 1) tb /\
    length (rest_at tb text P) = w /\
    Z.of_nat (calls tr) + 2 * Z.of_nat w <= 2 * Z.of_nat (length pi_x) /\
    ext (jr_items jr_strtod d o pi_x pi_ok) tr
      (jafter d o n cap acc (rest_at tb text P) (skipn (calls tr) pi_ok)) /\
    room_run RF (rf_run RF b0 tr) (snd (fst (jafter d o n cap acc (rest_at tb text P) []))) /\
    length acc = n /\ inv (S n) cap /\
    D = pis_slots o kids keys (Z.of_nat cap) ++ Di /\
    pis_open segs m (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) (map snd (rev acc)) (map fst (rev acc)) Di /\
    Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev acc)).

Lemma pi_seg : ms_segs B = rsegs.
Proof. exact (proj1 ENV). Qed.

Lemma pi_kv_pos : forall k, 64 + 8928 <= kv_up k.
Proof.
  assert (PVL : PV_LEAF = 8928) by reflexivity.
  intros [|k]; cbn [kv_up]; rewrite PVL; unfold PARSE_VALUE_F; lia.
Qed.

Lemma pi_K_bounds : (d < MAXD)%nat ->
  GROW_K + 80 <= PARSE_ITEMS_K d /\ PARSE_STRING_K + 80 <= PARSE_ITEMS_K d /\ ALLOC_STACK + 80 <= PARSE_ITEMS_K d /\
  PARSE_VALUE_K (S d) + 80 <= PARSE_ITEMS_K d /\ 0 <= GROW_K /\ 0 <= PARSE_STRING_K /\ 0 <= ALLOC_STACK /\
  0 <= PARSE_VALUE_K (S d).
Proof.
  intros H. unfold PARSE_ITEMS_K. replace (d <? MAXD)%nat with true by (symmetry; apply Nat.ltb_lt; exact H).
  pose proof (pi_kv_pos (MAXD - S d)) as KV. unfold PARSE_VALUE_K.
  assert (E1 : GROW_K = 8352) by reflexivity. assert (E2 : PARSE_STRING_K = 8368) by reflexivity.
  assert (E3 : PI_LEAF = 8368) by reflexivity. assert (E4 : ALLOC_STACK = 8192) by reflexivity.
  rewrite E1, E2, E3, E4. unfold PARSE_ITEMS_F. lia.
Qed.

Lemma pi_canon : forall R, pi_cs R ->
  mkR_of R = mkR (reg_get R 1) (Z_to_bv 64 pi_f) (reg_get regs0 3) (reg_get regs0 4) (reg_get R 5) (reg_get R 6)
    (reg_get R 7) (Z_to_bv 64 (-1)) (Z_to_bv 64 q) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13)
    (reg_get R 14) (reg_get R 15) (reg_get R 16) (reg_get R 17) (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v)
    (Z_to_bv 64 32) (Z_to_bv 64 44) (Z_to_bv 64 34) (Z_to_bv 64 WSM) (Z_to_bv 64 58) (reg_get regs0 25)
    (reg_get regs0 26) (reg_get regs0 27) (reg_get R 28) (reg_get R 29) (reg_get R 30) (reg_get R 31).
Proof.
  intros R (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  assert (E2 : reg_get R 2 = Z_to_bv 64 pi_f) by exact H2.
  assert (E3 : reg_get R 3 = reg_get regs0 3) by exact H3.
  assert (E4 : reg_get R 4 = reg_get regs0 4) by exact H4.
  assert (E8 : reg_get R 8 = Z_to_bv 64 (-1)) by exact H8.
  assert (E9 : reg_get R 9 = Z_to_bv 64 q) by exact H9.
  assert (E18 : reg_get R 18 = Z_to_bv 64 (if o then 1 else 0)) by exact H18.
  assert (E19 : reg_get R 19 = Z_to_bv 64 v) by exact H19.
  assert (E20 : reg_get R 20 = Z_to_bv 64 32) by exact H20.
  assert (E21 : reg_get R 21 = Z_to_bv 64 44) by exact H21.
  assert (E22 : reg_get R 22 = Z_to_bv 64 34) by exact H22.
  assert (E23 : reg_get R 23 = Z_to_bv 64 WSM) by exact H23.
  assert (E24 : reg_get R 24 = Z_to_bv 64 58) by exact H24.
  assert (E25 : reg_get R 25 = reg_get regs0 25) by exact H25.
  assert (E26 : reg_get R 26 = reg_get regs0 26) by exact H26.
  assert (E27 : reg_get R 27 = reg_get regs0 27) by exact H27.
  unfold mkR_of. rewrite E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27. reflexivity.
Qed.

Lemma pi_cs_rp : forall R R', pi_cs R -> regs_preserved R R' -> pi_cs R'.
Proof.
  intros R R' (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27) RP.
  assert (K : forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) by exact RP.
  unfold pi_cs.
  split; [transitivity (getr R' (Z_to_bv 5 2)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H2|].
  split; [transitivity (getr R' (Z_to_bv 5 3)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H3|].
  split; [transitivity (getr R' (Z_to_bv 5 4)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H4|].
  split; [transitivity (getr R' (Z_to_bv 5 8)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H8|].
  split; [transitivity (getr R' (Z_to_bv 5 9)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H9|].
  split; [transitivity (getr R' (Z_to_bv 5 18)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H18|].
  split; [transitivity (getr R' (Z_to_bv 5 19)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H19|].
  split; [transitivity (getr R' (Z_to_bv 5 20)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H20|].
  split; [transitivity (getr R' (Z_to_bv 5 21)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H21|].
  split; [transitivity (getr R' (Z_to_bv 5 22)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H22|].
  split; [transitivity (getr R' (Z_to_bv 5 23)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H23|].
  split; [transitivity (getr R' (Z_to_bv 5 24)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H24|].
  split; [transitivity (getr R' (Z_to_bv 5 25)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H25|].
  split; [transitivity (getr R' (Z_to_bv 5 26)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H26|].
  transitivity (getr R' (Z_to_bv 5 27)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H27.
Qed.

Lemma pi_final : forall x5 x6 x7 a0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 R',
  xregs_eqv (mkR (getr regs0 1) (Z_to_bv 64 (pi_f + 80)) (reg_get regs0 3) (reg_get regs0 4) x5 x6 x7
    (getr regs0 8) (getr regs0 9) a0 x11 x12 x13 x14 x15 x16 x17 (getr regs0 18) (getr regs0 19) (getr regs0 20)
    (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24) (reg_get regs0 25) (reg_get regs0 26)
    (reg_get regs0 27) x28 x29 x30 x31) R' ->
  regs_preserved regs0 R' /\ getr R' 10 = a0.
Proof.
  intros x5 x6 x7 a0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 R' XR.
  split; [|rewrite (rk_getr_eqv _ _ XR); reflexivity].
  intros r Hr. rewrite (rk_getr_eqv _ _ XR). unfold callee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    try reflexivity.
  change (Z_to_bv 64 (pi_f + 80) = getr regs0 2). unfold pi_f, spZ. rewrite Z.sub_add. apply Z_to_bv_lit_self.
Qed.

Lemma pi_okf_len : forall n c f, length (okf c f n) = n.
Proof. induction n as [|n IH]; intros c f; cbn [okf length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pi_ok_nth : forall i, nth i pi_ok true = negb (cnt0 + Z.of_nat i =? fail0).
Proof.
  intros i. unfold pi_ok.
  destruct (Nat.lt_ge_cases i (S (Z.to_nat (fail0 - cnt0)))) as [H|H].
  - apply okf_nth. exact H.
  - rewrite nth_overflow by (rewrite pi_okf_len; exact H). symmetry. apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma pi_ok_skip : forall k i, nth i (skipn k pi_ok) true = negb (cnt0 + Z.of_nat k + Z.of_nat i =? fail0).
Proof.
  intros k i. rewrite nth_skipn_b, pi_ok_nth. f_equal. f_equal. lia.
Qed.

Lemma pi_oks : forall k, oks pi_ok cnt0 fail0 k.
Proof. intros k i _. apply pi_ok_nth. Qed.

Lemma pi_x_cons : pi_x = opener o :: rest_at tb text (p0 + 1).
Proof.
  unfold pi_x. pose proof (pj_in_ok_bounds segs mem0 q text len p0 (Z.of_nat d) tb PIN0) as (_ & _ & _ & Hp & _).
  rewrite (pip_rest_cons tb text p0 _ ltac:(lia) PNTH).
  f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. destruct o; reflexivity.
Qed.

Definition pi_fresh (x : Z) : Prop :=
  0 <= x < alloc_ceiling /\ ~ in_img B x /\
  (forall p n, In (p, n) (user_blocks A0) -> ~ (ptr_addr L0 p <= x < ptr_addr L0 p + n)).

Lemma pi_pre0 : call_pre_k B (aa_MR API) (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ENV)))))). Qed.

Lemma pi_HM0 : aa_MR API L0 A0 mem0 md0.
Proof. exact (proj1 pi_pre0). Qed.

Lemma pi_rp_E : forall K L A regs mem md (E E' : Z -> Prop) gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' -> (forall x, E x -> E' x) ->
  rpost B API K L A regs mem md E' gone L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E E' gone L' A' regs' mem' md' (M & W & Bd & Y & HI & X & G & UB & PA & RP & Dv & H & IM & Kb & C) HE.
  refine (conj M (conj W (conj Bd (conj Y (conj HI (conj X (conj G (conj UB (conj PA (conj RP (conj Dv
    (conj _ (conj _ (conj _ C)))))))))))))).
  - intros a Ha Hs He. apply H; [exact Ha | exact Hs | intros E1; apply He, HE, E1].
  - intros a Ha Hn Hs He. apply IM; [exact Ha | exact Hn | exact Hs | intros E1; apply He, HE, E1].
  - intros p n i Hp Hp' Hi He. apply (Kb p n i); [exact Hp | exact Hp' | exact Hi | intros E1; apply He, HE, E1].
Qed.

Lemma pi_rp_exit : forall Lc Ac mc mdc D R',
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  regs_preserved regs0 R' ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 (rd_writes q v D) (fun _ _ => False) Lc Ac R' mc mdc.
Proof.
  intros Lc Ac mc mdc D R' RP HR. apply (pi_rp_E _ _ _ _ _ _ pi_E0); [exact (rk_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP HR)|].
  intros x [H|[H|H]]; unfold rd_writes; tauto.
Qed.

Lemma pi_rp_A : forall Lc Ac mc mdc m1 W,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  munch W mc m1 -> wmono segs mc m1 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> ~ in_img B x /\ ~ owned B Lc Ac x /\ (pi_E0 x \/ pi_fresh x)) ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 m1 mdc.
Proof.
  intros Lc Ac mc mdc m1 W (M & WF1 & Bd & Y & I & X & G & S & P & RP & Dv & H & IM & Kb & C) MU WM HW.
  pose proof rk_ceil as HC. pose proof pi_HM0 as HM0.
  assert (OUT : forall x, 0 <= x < 2 ^ 64 -> (in_img B x \/ owned B Lc Ac x \/ (~ pi_E0 x /\ ~ pi_fresh x)) ->
                  outside W x).
  { intros x Hx Hc. destruct (rk_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
    destruct (HW x Hx Ho) as (N1 & N2 & N3). destruct Hc as [Hc|[Hc|[Hc1 Hc2]]]; tauto. }
  assert (MB : forall x, 0 <= x < 2 ^ 64 -> outside W x ->
                 mbyte segs m1 x = mbyte segs mc x /\ (writable_at segs mc x <-> writable_at segs m1 x)).
  { intros x Hx Ho. split; [exact (MemNorm.mbyte_munch _ W mc m1 x MU Hx Ho) | exact (rk_writable_munch _ W mc m1 x MU Hx Ho)]. }
  split.
  { apply (rk_MR_A pi_seg Lc Ac mc m1 mdc W M MU WM).
    - intros x Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ x M Ho). apply OUT; [lia | right; left; exact Ho].
    - intros x Hx Ho. exact (proj1 (HW x Hx Ho)). }
  split; [exact WF1|]. split; [exact Bd|]. split; [exact Y|]. split; [exact I|].
  split.
  { intros HI i Hi. rewrite <- (X HI i Hi).
    assert (Ho : owned B Lc Ac (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M Ho).
    apply MB; [lia|]. apply OUT; [lia | right; left; exact Ho]. }
  split; [exact G|]. split; [exact S|]. split; [exact P|]. split; [exact RP|]. split; [exact Dv|].
  split.
  { intros a Ha Hs He. assert (Ho : outside W a).
    { apply OUT; [lia|]. right; right. split; [exact He | intros (F1 & _); lia]. }
    destruct (MB a ltac:(lia) Ho) as [E1 E2]. destruct (H a Ha Hs He) as [E3 E4]. split; [congruence | tauto]. }
  split.
  { intros a Ha Hn Hs He. pose proof (rk_img_bound pi_seg a Ha) as Hr.
    assert (Ho : outside W a) by (apply OUT; [lia | left; exact Ha]).
    destruct (MB a ltac:(lia) Ho) as [E1 E2]. destruct (IM a Ha Hn Hs He) as [E3 E4]. split; [congruence | tauto]. }
  split.
  { intros p n i Hp Hp' Hi He.
    destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 p n i HM0 Hp Hi) as (_ & B1 & B2 & _).
    assert (Ho : outside W (ptr_addr L0 p + i)).
    { apply OUT; [lia|]. right; right. split; [exact He|]. intros (_ & _ & F3). exact (F3 p n Hp ltac:(lia)). }
    rewrite (proj1 (MB (ptr_addr L0 p + i) ltac:(lia) Ho)). exact (Kb p n i Hp Hp' Hi He). }
  intros a Ha. unfold writable_at. apply WM. exact (C a Ha).
Qed.

Lemma pi_rp_call : forall Lc Ac mc mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  rpost B API K2 Lc Ac regs2 mc mdc E2 gone2 L2 A2 regs3 m2 md2 ->
  spZ regs2 = pi_f -> K2 + 80 <= PARSE_ITEMS_K d -> 0 <= K2 ->
  (forall a, E2 a -> pi_E0 a \/ pi_fresh a) ->
  (forall p n, In (p, n) (user_blocks A0) -> ~ gone2 (ptr_addr L0 p) n) ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2.
Proof.
  intros Lc Ac mc mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 R1 R2 SP KK K0 HE HG.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  pose proof rk_ceil as HC. pose proof DJS as DJ. cbn [disjoint_from] in DJ.
  apply (rk_seq (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 Lc Ac regs0 mc mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2
    regs0 R1 R2).
  - intros r _. reflexivity.
  - rewrite SP. unfold pi_f. lia.
  - rewrite SP. unfold pi_f. lia.
  - exact HAC.
  - exact K0.
  - intros a Ha Hs He H2. destruct (HE a H2) as [H|(F1 & _)]; [exact (He H) | lia].
  - intros a Ha Hs He H2. destruct (HE a H2) as [H|(_ & F2 & _)]; [exact (He H) | exact (F2 Ha)].
  - intros p n i Hp Hp1 Hi He H2. destruct (HE _ H2) as [H|(_ & _ & F3)]; [exact (He H) | exact (F3 p n Hp ltac:(lia))].
  - intros p n Hp _. exact (HG p n Hp).
  - intros a Ha Hd. left. intros H2. unfold scratch_k in Ha, Hd. rewrite SP in Hd. unfold pi_f in Hd.
    destruct (HE a H2) as [[Hv|[Hq|Hs]]|(F1 & _)].
    + lia.
    + unfold pj_in_set in Hq. lia.
    + unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia.
    + lia.
Qed.

Lemma pi_fresh_blk : forall Lc Ac mc mdc a k x,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  In (a, k) (blocks Lc Ac) -> ~ In (a, k) (blocks L0 A0) -> a <= x < a + k -> pi_fresh x.
Proof.
  intros Lc Ac mc mdc a k x R Hin Hn Hx.
  pose proof R as (M & _ & _ & _ & _ & _ & _ & S & P & _).
  destruct (rk_blk_facts Lc Ac mc mdc a k M Hin) as (B1 & B2 & _).
  pose proof rk_ceil.
  split; [lia|]. split.
  - destruct (rk_blk_user Lc Ac a k Hin) as (pp & Hp & Ep). intros Hi.
    apply (YL01.ax_blocks_img AX Lc Ac mc mdc pp k (x - a) M Hp ltac:(lia)). rewrite Ep.
    replace (a + (x - a)) with x by lia. exact Hi.
  - intros p n Hp Hpx. assert (Hp1 : In (p, n) (user_blocks Ac)) by (apply S; [exact Hp | tauto]).
    pose proof (rk_blk_of_user Lc Ac p n Hp1) as Hq. rewrite (P p n Hp Hp1) in Hq.
    pose proof (mr_blocks_disjoint B _ (aa_laws API) Lc Ac mc mdc M) as PW.
    assert (Hne : (ptr_addr L0 p, n) <> (a, k)) by (intros E; apply Hn; rewrite <- E; exact (rk_blk_of_user L0 A0 p n Hp)).
    destruct (rk_pairwise_in _ _ _ _ PW Hq Hin Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia.
Qed.

Lemma pi_fresh_D : forall Lc Ac mc mdc Lamc peakc cntc failc D x,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  ledger B Lc Ac mc Lamc peakc cntc failc -> Permutation Lamc (D ++ Lam0) -> new_blks L0 A0 D ->
  blk_set D x -> pi_fresh x.
Proof.
  intros Lc Ac mc mdc Lamc peakc cntc failc D x R LG PERM NB (a & k & HD & Hx).
  pose proof R as (M & _).
  destruct (rk_D_facts Lc Ac mc mdc Lamc peakc cntc failc D Lam0 a k M LG PERM HD) as (HB & _).
  apply (pi_fresh_blk Lc Ac mc mdc (a - 16) (k + 16) x R HB (NB a k HD)). lia.
Qed.

Lemma pi_exit : forall fxc Lc Ac m mdc Lamc peakc cntc failc tr D R' res okr,
  frm_zero (@fp_csr fxc) -> fregs_kept fx fxc ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 m mdc ->
  rd_cells B m -> ledger B Lc Ac m Lamc peakc cntc failc ->
  Permutation Lamc (D ++ Lam0) -> Permutation (map snd D) (map Z.of_nat (lsz tr)) -> Z.of_nat (length D) = nlive tr ->
  new_blks L0 A0 D ->
  peakc = Z.max peak0 (lsum Lam0 + hpeak tr) -> rf_ok RF Ac (rf_run RF b0 tr) ->
  cntc = cnt0 + Z.of_nat (calls tr) -> fail_after cnt0 fail0 (calls tr) failc ->
  regs_preserved regs0 R' ->
  jr_items jr_strtod d o pi_x pi_ok = (res, tr, okr) ->
  match res with
  | Some (t, r) =>
      getr R' 10 = Z_to_bv 64 0 /\
      pj_in_ok segs m q text len (text + len - Z.of_nat (length r)) (Z.of_nat d) tb /\
      pj_node segs m (lin Lamc) v t D
  | None =>
      getr R' 10 = Z_to_bv 64 (-1) /\
      pj_in_after B m q text len (Z.of_nat d + 1) 33 /\
      pj_fd segs m (lin Lamc) (MAXD - d) v D
  end ->
  pi_post (mkCfg (@mkst fxc R' (getr regs0 1) m (seg_rom segs)) mdc).
Proof.
  intros fxc Lc Ac m mdc Lamc peakc cntc failc tr D R' res okr FZ FK RP RD LG PERM HELD NL NB PK RS CN FA RPF JI ARM.
  exists fxc, Lc, Ac, R', m, mdc, Lamc, peakc, cntc, failc, pi_ok, res, tr, okr, D.
  split; [reflexivity|]. split; [exact FZ|]. split; [exact FK|].
  split; [exact (pi_rp_exit Lc Ac m mdc D R' RP RPF)|].
  split; [exact RD|]. split; [exact LG|]. split; [exact JI|].
  split; [exact (pi_oks _)|]. split; [exact CN|]. split; [exact FA|].
  split; [exact PERM|]. split; [exact HELD|]. split; [exact NL|]. split; [exact NB|]. split; [exact PK|].
  split.
  { fold pi_x. apply hpeak_le; [lia|]. intros pp rr Ht. rewrite pi_x_cons in JI |- *.
    apply (G10_2_items jr_strtod d o (opener o) (rest_at tb text (p0 + 1)) pi_ok pp rr). rewrite JI. exact Ht. }
  split; [exact RS|].
  destruct res as [[t r]|].
  - destruct ARM as (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    rewrite (lsz_counts D tr HELD NL). fold pi_x. rewrite pi_x_cons in JI |- *.
    exact (G10_1_items jr_strtod d o (opener o) (rest_at tb text (p0 + 1)) pi_ok t r tr okr JI).
  - exact ARM.
Qed.

Lemma pi_ret : forall fxc m mdc (ms' : machine_state) (P : config -> Prop)
    (a0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ms_eqv (MS (mkR (getr regs0 1) (Z_to_bv 64 (pi_f + 80)) (reg_get regs0 3) (reg_get regs0 4) x5 x6 x7
    (getr regs0 8) (getr regs0 9) a0 x11 x12 x13 x14 x15 x16 x17 (getr regs0 18) (getr regs0 19) (getr regs0 20)
    (getr regs0 21) (getr regs0 22) (getr regs0 23) (getr regs0 24) (reg_get regs0 25) (reg_get regs0 26)
    (reg_get regs0 27) x28 x29 x30 x31) (@fp_regs fxc) (ret_pc (getr regs0 1)) (@fp_csr fxc) None m (seg_rom rsegs)) ms' ->
  (forall R', regs_preserved regs0 R' -> getr R' 10 = a0 ->
     P (mkCfg (@mkst fxc R' (getr regs0 1) m (seg_rom segs)) mdc)) ->
  SR segs (mkCfg ms' mdc) P.
Proof.
  intros fxc m mdc ms' P a0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 EQV K.
  destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
  destruct (pi_final _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (RPF & R10F).
  pose proof pi_pre0 as (_ & _ & _ & HRA & _).
  rewrite Ems, (rk_ret_pc _ HRA).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite pi_seg; reflexivity).
  apply SR_ret. apply K; assumption.
Qed.

Lemma pi_K80 : 80 <= PARSE_ITEMS_K d.
Proof.
  assert (E3 : PI_LEAF = 8368) by reflexivity.
  unfold PARSE_ITEMS_K, PARSE_ITEMS_F. destruct (d <? MAXD)%nat; [rewrite E3; lia | lia].
Qed.

Lemma pi_sp : forall R, pi_cs R -> spZ R = pi_f.
Proof.
  intros R CS. pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _).
  pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 pi_f)); [f_equal; exact (proj1 CS)|].
  apply MState.unsigned_lit. unfold pi_f. lia.
Qed.

Lemma pi_env : forall fxc Lc Ac m mdc Lamc tr D R K1,
  pi_glob fxc Lc Ac m mdc Lamc tr D -> pi_cs R -> YK0s.ret_ok (getr R 1) ->
  K1 + 80 <= PARSE_ITEMS_K d -> 0 <= K1 ->
  reader_env (fx := fxc) B API K1 Lc Ac R m mdc.
Proof.
  intros fxc Lc Ac m mdc Lamc tr D R K1 (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX) CS RA KK K0.
  pose proof ENV as (SEG & TP & ERR & GG & GD & PRE & SP47 & GTOP & FRM & RDC).
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  pose proof RP as (M & WF1 & Bd & Y & I & X & G & UB & PA & RPr & Dv & H & IM & Kb & C).
  pose proof (pi_sp R CS) as SPR. pose proof rk_ceil as HC.
  assert (LO : pi_f <= pi_lo) by (unfold pi_lo, pi_f; lia).
  split; [exact SEG|]. split; [exact TP|]. split; [exact ERR|]. split; [exact GG|]. split; [exact GD|].
  split.
  { split; [exact M|]. split; [exact WF1|]. split; [exact Bd|]. split; [exact RA|].
    split; [rewrite SPR; unfold pi_f; replace (spZ regs0 - 80) with (spZ regs0 + (-5) * 16) by lia;
      rewrite Z_mod_plus_full; exact H16|].
    split; [rewrite SPR; unfold pi_f; lia|]. split; [rewrite SPR; unfold pi_f; lia|].
    split; [intros a Ha; apply C; left; rewrite SPR in Ha; unfold pi_f in Ha; lia|].
    split; [transitivity (getr regs0 4); [exact (proj1 (proj2 (proj2 CS))) | exact HTP]|].
    split; [intros a Ha; apply C; right; exact Ha|].
    intros HDn. destruct Y as (_ & Hsec & _). rewrite Hsec, SPR. exact (auxv_pre_mono B _ _ _ m LO (AUX HDn)). }
  split; [rewrite SPR; unfold pi_f; lia|]. split; [rewrite SPR; unfold pi_f; lia|].
  split; [exact FZ | exact RD].
Qed.

Lemma pi_vlo : spZ regs0 <= v \/ v + 56 <= alloc_ceiling.
Proof.
  pose proof RPL as (PL & _). pose proof pi_HM0 as HM0.
  destruct PL as [(P1 & _) | [(a & k & Hb & _ & Ha & Hk) | (a & k & Hl & Ha & Hk)]]; [left; exact P1| |].
  - right. destruct (rk_blk_facts L0 A0 mem0 md0 a k HM0 Hb) as (_ & B2 & _). lia.
  - right. destruct (ledger_block_range B API L0 A0 mem0 md0 Lam0 peak0 cnt0 fail0 a k HM0 LG0 Hl) as (_ & B2 & _). lia.
Qed.

Lemma pi_rplace : forall fxc Lc Ac m mdc Lamc tr D R peakc cntc failc,
  pi_glob fxc Lc Ac m mdc Lamc tr D -> ledger B Lc Ac m Lamc peakc cntc failc -> spZ R = pi_f ->
  rplace B Lc Ac Lamc R m v.
Proof.
  intros fxc Lc Ac m mdc Lamc tr D R peakc cntc failc (_ & _ & RP & _ & _ & PERM & _ & _ & NB & _ & AUX) LG SPR.
  pose proof RP as (M & _ & _ & Y & _ & _ & _ & UB & PA & _).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _).
  pose proof RPL as (PL & _ & PNO).
  pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  destruct PL as [(P1 & P2) | [(a & k & Hb & Hnl & Ha & Hk) | (a & k & Hl & Ha & Hk)]].
  - split; [left; rewrite SPR; unfold pi_f; lia|].
    split.
    + intros _ HDn. destruct Y as (_ & Hsec & _). rewrite Hsec.
      apply (auxv_pre_mono B _ pi_lo); [|exact (AUX HDn)].
      unfold pi_lo. destruct (Z.leb_spec (spZ regs0) v); lia.
    + intros i Hi. destruct (PNO i Hi) as (N1 & N2 & N3 & N4). split; [|tauto].
      intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M Ho). lia.
  - destruct (rk_blk_user L0 A0 a k Hb) as (p & Hp & Ep).
    assert (Hp' : In (p, k) (user_blocks Ac)) by (apply UB; [exact Hp | intros Hf; exact Hf]).
    assert (Hb' : In (a, k) (blocks Lc Ac)).
    { rewrite <- Ep, <- (PA p k Hp Hp'). exact (rk_blk_of_user Lc Ac p k Hp'). }
    destruct (rk_blk_facts Lc Ac m mdc a k M Hb') as (B1 & B2 & B3).
    split.
    + right; left. exists a, k. split; [exact Hb'|]. split; [|lia].
      intros Hl. unfold lin in Hl. apply (Permutation_in _ PERM) in Hl. apply in_app_or in Hl.
      destruct Hl as [Hl|Hl]; [|exact (Hnl Hl)].
      apply (NB _ _ Hl). replace (a + 16 - 16) with a by lia. replace (k - 16 + 16) with k by lia. exact Hb.
    + split; [intros Hs; exfalso; rewrite SPR in Hs; unfold pi_f in Hs; lia|].
      intros i Hi. destruct (PNO i Hi) as (N1 & N2 & N3 & N4). split; [|tauto].
      replace (v + i) with (a + (v + i - a)) by lia. exact (proj2 (B3 (v + i - a) ltac:(lia))).
  - pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
    assert (Hl' : In (a, k) Lamc) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact Hl).
    destruct (LF _ Hl') as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
    destruct (rk_blk_facts Lc Ac m mdc _ _ M Lin) as (B1 & B2 & B3).
    split; [right; right; exists a, k; split; [exact Hl' | lia]|].
    split; [intros Hs; exfalso; rewrite SPR in Hs; unfold pi_f in Hs; lia|].
    intros i Hi. destruct (PNO i Hi) as (N1 & N2 & N3 & N4). split; [|tauto].
    replace (v + i) with (a - 16 + (v + i - (a - 16))) by lia. exact (proj2 (B3 (v + i - (a - 16)) ltac:(lia))).
Qed.

Lemma pi_lo_E : forall a, pi_E0 a \/ pi_fresh a -> a < pi_lo.
Proof.
  intros a H. pose proof pi_vlo as HV. pose proof rk_ceil as HC.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof pi_K80 as KP.
  unfold pi_lo. destruct H as [[Hv|[Hq|Hs]]|(Hf & _)].
  - destruct (Z.leb_spec (spZ regs0) v); lia.
  - unfold pj_in_set in Hq. lia.
  - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia.
  - lia.
Qed.

Lemma pi_frm_call : forall Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2,
  rpost B API K2 Lc Ac regs2 m mdc E2 gone2 L2 A2 regs3 m2 md2 -> spZ regs2 <= pi_f ->
  (forall a, E2 a -> pi_E0 a \/ pi_fresh a) -> pi_frm m -> pi_frm m2.
Proof.
  intros Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 RP2 SP2 HE2 FR.
  pose proof RP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H2 & _).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC.
  pose proof ENV as (_ & _ & ERR & _). pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof pi_K80 as KP.
  unfold pi_frm in FR |- *.
  apply (pi_frame_mv m m2 pi_f _ _ _ _ _ _ _ _ _ _ FR); [|unfold pi_f; lia | unfold pi_f; lia].
  intros x Hx. rewrite <- pi_seg. unfold pi_f in Hx.
  assert (NE : ~ E2 x).
  { intros He. destruct (HE2 x He) as [[Hv|[Hq|Hs]]|(Hf & _)].
    - lia.
    - unfold pj_in_set in Hq. lia.
    - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia.
    - lia. }
  assert (NS : ~ scratch_k B K2 regs2 x)
    by (unfold scratch_k; rewrite ERR; unfold strtod_c.STRTOD_ERRNO; unfold pi_f in SP2; lia).
  exact (proj1 (H2 x ltac:(lia) NS NE)).
Qed.

Lemma pi_aux_call : forall Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2,
  rpost B API K2 Lc Ac regs2 m mdc E2 gone2 L2 A2 regs3 m2 md2 -> spZ regs2 <= pi_f ->
  (forall a, E2 a -> pi_E0 a \/ pi_fresh a) ->
  (st_init_done Ac = false -> auxv_pre B (ly_sec L0) pi_lo m) ->
  st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo m2.
Proof.
  intros Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 RP2 SP2 HE2 AUX HD2.
  pose proof RP2 as (_ & _ & _ & _ & I2 & X2 & _ & _ & _ & _ & _ & H2 & _).
  assert (HDc : st_init_done Ac = false).
  { destruct (st_init_done Ac) eqn:E; [rewrite (I2 eq_refl) in HD2; discriminate | reflexivity]. }
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC.
  pose proof ENV as (_ & _ & ERR & _). pose proof pi_K80 as KP.
  assert (LQ : q + 24 <= pi_lo) by (unfold pi_lo; lia).
  apply (rk_auxv_keep (ly_sec L0) pi_lo m m2 (AUX HDc)).
  - intros i Hi. exact (X2 HD2 i Hi).
  - intros a Ha. assert (NE : ~ E2 a) by (intros He; pose proof (pi_lo_E a (HE2 a He)); lia).
    assert (NS : ~ scratch_k B K2 regs2 a)
      by (unfold scratch_k; rewrite ERR; unfold strtod_c.STRTOD_ERRNO; unfold pi_f in SP2; lia).
    exact (proj1 (H2 a ltac:(lia) NS NE)).
Qed.

Lemma pi_text : forall Lc Ac mc mdc,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  bytes_at segs mc text tb.
Proof.
  intros Lc Ac mc mdc (M & W & Bd & Y & HI & X & G & UB & PA & RP & Dv & H & IM & Kb & C).
  pose proof TOK as (TXL & TXN). pose proof pi_HM0 as HM0. pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof PIN0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _).
  apply (pis_bytes_mv segs mem0 mc text text tb HT); [lia | lia |].
  intros i Hi. rewrite TL in Hi.
  destruct (TXN i Hi) as (N1 & N2 & N3).
  assert (NE : ~ pi_E0 (text + i)) by (intros [Hv|[Hq|Hs]]; [lia | unfold pj_in_set in Hq; lia | exact (N2 Hs)]).
  assert (NS : ~ scratch_k B (PARSE_ITEMS_K d) regs0 (text + i))
    by (unfold scratch_k; intros [Hs|Hs]; [lia | exact (N3 Hs)]).
  destruct TXL as [Hs | [Him | [(a0 & k0 & Hb & _ & Ha & Hk) | (a0 & k0 & Hl0 & Ha & Hk)]]].
  - exact (proj1 (H (text + i) ltac:(lia) NS NE)).
  - refine (proj1 (IM (text + i) (Him i Hi) _ NS NE)).
    intros L1 A1 mem1 md1 HM1 [Ho|Ho].
    + pose proof (YL01.ax_img AX L1 A1 mem1 md1 (text + i) HM1 (Him i Hi) Ho) as HCx.
      apply N1. exact (CO L0 A0 mem0 md0 (text + i) HM0 HCx).
    + apply N1. right. exact Ho.
  - destruct (rk_blk_user L0 A0 a0 k0 Hb) as (p & Hp & Ep).
    assert (Hp' : In (p, k0) (user_blocks Ac)) by (apply UB; [exact Hp | intros Hf; exact Hf]).
    replace (text + i) with (ptr_addr L0 p + (text + i - ptr_addr L0 p)) by lia.
    apply (Kb p k0 (text + i - ptr_addr L0 p) Hp Hp'); [lia|].
    replace (ptr_addr L0 p + (text + i - ptr_addr L0 p)) with (text + i) by lia. exact NE.
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl0.
    destruct (LF _ Hl0) as (LK & LIn & _). cbn [fst snd] in LK, LIn.
    destruct (rk_blk_user L0 A0 _ _ LIn) as (p & Hp & Ep).
    assert (Hp' : In (p, k0 + 16) (user_blocks Ac)) by (apply UB; [exact Hp | intros Hf; exact Hf]).
    replace (text + i) with (ptr_addr L0 p + (text + i - ptr_addr L0 p)) by lia.
    apply (Kb p (k0 + 16) (text + i - ptr_addr L0 p) Hp Hp'); [lia|].
    replace (ptr_addr L0 p + (text + i - ptr_addr L0 p)) with (text + i) by lia. exact NE.
Qed.

Lemma pi_in_call : forall Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 P dd,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  rpost B API K2 Lc Ac regs2 m mdc E2 gone2 L2 A2 regs3 m2 md2 ->
  spZ regs2 <= spZ regs0 -> (forall a, E2 a -> ~ (q <= a < q + 24)) ->
  pj_in_ok segs m q text len P dd tb -> pj_in_ok segs m2 q text len P dd tb.
Proof.
  intros Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 P dd RPc RP2 SP2 HE2 PIN.
  pose proof RP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H2 & _).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC.
  pose proof ENV as (_ & _ & ERR & _). pose proof pi_K80 as KP.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN) as (Q0 & Q1 & _).
  apply (pi_in_mv segs m m2 q text len P dd tb PIN); [|exact (pi_text L2 A2 m2 md2 RPc)].
  intros x Hx.
  assert (NS : ~ scratch_k B K2 regs2 x) by (unfold scratch_k; rewrite ERR; unfold strtod_c.STRTOD_ERRNO; lia).
  destruct (H2 x ltac:(lia) NS (fun He => HE2 x He Hx)) as [E1 E3]. split; [exact E1 | intros Hw; apply E3; exact Hw].
Qed.

Lemma pi_cs_eqv : forall R R', pi_cs R -> xregs_eqv (mkR_of R) R' -> pi_cs R'.
Proof.
  intros R R' CS XR. rewrite (pi_canon R CS) in XR.
  unfold pi_cs. repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]).
  rewrite (rk_getr_eqv _ _ XR). reflexivity.
Qed.

Lemma pi_g2_tail : forall fxc R m mdc (P : config -> Prop),
  pi_cs R -> pi_frm m -> m_halted mdc = None -> m_vm_lazy mdc = [] ->
  (bv_unsigned (getr R 10) = 0 -> forall R', pi_cs R' ->
     P (mkCfg (@mkst fxc R' (Z_to_bv 64 0x150d8) m (seg_rom segs)) mdc)) ->
  (bv_unsigned (getr R 10) <> 0 -> forall R', regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
     P (mkCfg (@mkst fxc R' (getr regs0 1) m (seg_rom segs)) mdc)) ->
  SR segs (mkCfg (@mkst fxc R (Z_to_bv 64 0x15214) m (seg_rom segs)) mdc) P.
Proof.
  intros fxc R m mdc P CS FR Hh Hl K0 K1. unfold pi_frm in FR.
  rewrite pi_seg.
  eapply rk_kA; [exact Hh | exact Hl | |].
  { rewrite (pi_canon R CS). eapply pip_g2. exact FR. }
  intros ms' (can & HQ & EQV).
  destruct HQ as [(H0 & ->) | (H0 & ->)].
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
    rewrite Ems. apply SR_ret. rewrite <- pi_seg.
    apply K0; [exact H0|].
    apply (pi_cs_eqv R); [exact CS|]. rewrite (pi_canon R CS). exact XR.
  - rewrite <- pi_seg. eapply pi_ret; [exact EQV|].
    intros R' RPF R10F. apply K1; [exact H0 | exact RPF | exact R10F].
Qed.

Definition pi_cs0 (R : bvmap 5 word) : Prop :=
  getr R 2 = Z_to_bv 64 pi_f /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  getr R 8 = Z_to_bv 64 (-1) /\ getr R 9 = Z_to_bv 64 q /\ getr R 18 = Z_to_bv 64 (pis_oz o) /\
  getr R 19 = Z_to_bv 64 v /\ getr R 25 = getr regs0 25 /\ getr R 26 = getr regs0 26 /\ getr R 27 = getr regs0 27.

Lemma pi_cs_cs0 : forall R, pi_cs R -> pi_cs0 R.
Proof.
  intros R (H2 & H3 & H4 & H8 & H9 & H18 & H19 & _ & _ & _ & _ & _ & H25 & H26 & H27).
  unfold pi_cs0. repeat (split; [assumption|]). assumption.
Qed.

Lemma pi_sp0 : forall R, pi_cs0 R -> spZ R = pi_f.
Proof.
  intros R CS. pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _).
  pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 pi_f)); [f_equal; exact (proj1 CS)|].
  apply MState.unsigned_lit. unfold pi_f. lia.
Qed.

Lemma pi_cs0_rp : forall R R', pi_cs0 R -> regs_preserved R R' -> pi_cs0 R'.
Proof.
  intros R R' (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H25 & H26 & H27) RP.
  assert (K : forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) by exact RP.
  unfold pi_cs0.
  split; [transitivity (getr R' (Z_to_bv 5 2)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H2|].
  split; [transitivity (getr R' (Z_to_bv 5 3)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H3|].
  split; [transitivity (getr R' (Z_to_bv 5 4)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H4|].
  split; [transitivity (getr R' (Z_to_bv 5 8)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H8|].
  split; [transitivity (getr R' (Z_to_bv 5 9)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H9|].
  split; [transitivity (getr R' (Z_to_bv 5 18)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H18|].
  split; [transitivity (getr R' (Z_to_bv 5 19)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H19|].
  split; [transitivity (getr R' (Z_to_bv 5 25)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H25|].
  split; [transitivity (getr R' (Z_to_bv 5 26)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H26|].
  transitivity (getr R' (Z_to_bv 5 27)); [reflexivity|]; rewrite K by (unfold callee_saved; lia); exact H27.
Qed.

Lemma pi_env0 : forall fxc Lc Ac m mdc Lamc tr D R K1,
  pi_glob fxc Lc Ac m mdc Lamc tr D -> pi_cs0 R -> YK0s.ret_ok (getr R 1) ->
  K1 + 80 <= PARSE_ITEMS_K d -> 0 <= K1 ->
  reader_env (fx := fxc) B API K1 Lc Ac R m mdc.
Proof.
  intros fxc Lc Ac m mdc Lamc tr D R K1 (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX) CS RA KK K0.
  pose proof ENV as (SEG & TP & ERR & GG & GD & PRE & SP47 & GTOP & FRM & RDC).
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  pose proof RP as (M & WF1 & Bd & Y & I & X & G & UB & PA & RPr & Dv & H & IM & Kb & C).
  pose proof (pi_sp0 R CS) as SPR. pose proof rk_ceil as HC.
  assert (LO : pi_f <= pi_lo) by (unfold pi_lo, pi_f; lia).
  split; [exact SEG|]. split; [exact TP|]. split; [exact ERR|]. split; [exact GG|]. split; [exact GD|].
  split.
  { split; [exact M|]. split; [exact WF1|]. split; [exact Bd|]. split; [exact RA|].
    split; [rewrite SPR; unfold pi_f; replace (spZ regs0 - 80) with (spZ regs0 + (-5) * 16) by lia;
      rewrite Z_mod_plus_full; exact H16|].
    split; [rewrite SPR; unfold pi_f; lia|]. split; [rewrite SPR; unfold pi_f; lia|].
    split; [intros a Ha; apply C; left; rewrite SPR in Ha; unfold pi_f in Ha; lia|].
    split; [transitivity (getr regs0 4); [exact (proj1 (proj2 (proj2 CS))) | exact HTP]|].
    split; [intros a Ha; apply C; right; exact Ha|].
    intros HDn. destruct Y as (_ & Hsec & _). rewrite Hsec, SPR. exact (auxv_pre_mono B _ _ _ m LO (AUX HDn)). }
  split; [rewrite SPR; unfold pi_f; lia|]. split; [rewrite SPR; unfold pi_f; lia|].
  split; [exact FZ | exact RD].
Qed.

Lemma pi_canon1 : forall R, pi_cs0 R ->
  mkR_of R = mkR (reg_get R 1) (Z_to_bv 64 pi_f) (reg_get regs0 3) (reg_get regs0 4) (reg_get R 5) (reg_get R 6)
    (reg_get R 7) (Z_to_bv 64 (-1)) (Z_to_bv 64 q) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13)
    (reg_get R 14) (reg_get R 15) (reg_get R 16) (reg_get R 17) (Z_to_bv 64 (if o then 1 else 0)) (Z_to_bv 64 v)
    (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23) (reg_get R 24) (reg_get regs0 25)
    (reg_get regs0 26) (reg_get regs0 27) (reg_get R 28) (reg_get R 29) (reg_get R 30) (reg_get R 31).
Proof.
  intros R (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H25 & H26 & H27).
  assert (E2 : reg_get R 2 = Z_to_bv 64 pi_f) by exact H2.
  assert (E3 : reg_get R 3 = reg_get regs0 3) by exact H3.
  assert (E4 : reg_get R 4 = reg_get regs0 4) by exact H4.
  assert (E8 : reg_get R 8 = Z_to_bv 64 (-1)) by exact H8.
  assert (E9 : reg_get R 9 = Z_to_bv 64 q) by exact H9.
  assert (E18 : reg_get R 18 = Z_to_bv 64 (if o then 1 else 0)) by exact H18.
  assert (E19 : reg_get R 19 = Z_to_bv 64 v) by exact H19.
  assert (E25 : reg_get R 25 = reg_get regs0 25) by exact H25.
  assert (E26 : reg_get R 26 = reg_get regs0 26) by exact H26.
  assert (E27 : reg_get R 27 = reg_get regs0 27) by exact H27.
  unfold mkR_of. rewrite E2, E3, E4, E8, E9, E18, E19, E25, E26, E27. reflexivity.
Qed.

Lemma pi_g1_tail : forall fxc R m mdc (P : config -> Prop),
  pi_cs0 R -> pi_frm m -> m_halted mdc = None -> m_vm_lazy mdc = [] ->
  (bv_unsigned (getr R 10) = 0 -> forall R', pi_cs R' ->
     P (mkCfg (@mkst fxc R' (Z_to_bv 64 0x150d8) m (seg_rom segs)) mdc)) ->
  (bv_unsigned (getr R 10) <> 0 -> forall R', regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
     P (mkCfg (@mkst fxc R' (getr regs0 1) m (seg_rom segs)) mdc)) ->
  SR segs (mkCfg (@mkst fxc R (Z_to_bv 64 0x150b8) m (seg_rom segs)) mdc) P.
Proof.
  intros fxc R m mdc P CS FR Hh Hl K0 K1. unfold pi_frm in FR.
  rewrite pi_seg.
  eapply rk_kA; [exact Hh | exact Hl | |].
  { rewrite (pi_canon1 R CS). eapply pip_g1. exact FR. }
  intros ms' (can & HQ & EQV).
  destruct HQ as [(H0 & ->) | (H0 & ->)].
  - rewrite <- pi_seg. eapply pi_ret; [exact EQV|].
    intros R' RPF R10F. apply K1; [exact H0 | exact RPF | exact R10F].
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
    rewrite Ems. apply SR_ret. rewrite <- pi_seg.
    apply K0; [exact H0|].
    unfold pi_cs. repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]). rewrite (rk_getr_eqv _ _ XR). reflexivity.
Qed.

Lemma pi_grow_val : forall k n cap,
  grow o n cap (skipn k pi_ok) =
  if Nat.ltb n cap then (Some cap, [], skipn k pi_ok)
  else if cnt0 + Z.of_nat k =? fail0 then (None, [EFail (56 * pi_c2 cap)%nat], skipn (S k) pi_ok)
  else if o then
    (if cnt0 + Z.of_nat k + 1 =? fail0
     then (None, [EGrow (56 * cap)%nat (56 * pi_c2 cap)%nat; EFail (8 * pi_c2 cap)%nat], skipn (S (S k)) pi_ok)
     else (Some (pi_c2 cap), [EGrow (56 * cap)%nat (56 * pi_c2 cap)%nat; EGrow (8 * cap)%nat (8 * pi_c2 cap)%nat],
           skipn (S (S k)) pi_ok))
  else (Some (pi_c2 cap), [EGrow (56 * cap)%nat (56 * pi_c2 cap)%nat], skipn (S k) pi_ok).
Proof.
  intros k n cap. unfold grow. destruct (Nat.ltb n cap); [reflexivity|].
  unfold jbind, jrealloc. cbv beta zeta. rewrite pi_take. cbv beta iota. rewrite pi_ok_nth.
  destruct (cnt0 + Z.of_nat k =? fail0); cbv beta iota delta [negb]; [reflexivity|].
  destruct o; cbv beta iota.
  - rewrite pi_take. cbv beta iota. rewrite pi_ok_nth.
    replace (cnt0 + Z.of_nat (S k)) with (cnt0 + Z.of_nat k + 1) by lia.
    destruct (cnt0 + Z.of_nat k + 1 =? fail0); reflexivity.
  - reflexivity.
Qed.

Lemma pi_grow_nil : forall n cap, grow o n cap [] =
  if Nat.ltb n cap then (Some cap, [], [])
  else (Some (pi_c2 cap),
        (EGrow (56 * cap)%nat (56 * pi_c2 cap)%nat :: if o then [EGrow (8 * cap)%nat (8 * pi_c2 cap)%nat] else []), []).
Proof. intros n cap. unfold grow. destruct (Nat.ltb n cap); [reflexivity|]. destruct o; reflexivity. Qed.

Lemma pi_grow_room : forall b cap,
  room_run RF b (EGrow (56 * cap)%nat (56 * pi_c2 cap)%nat :: if o then [EGrow (8 * cap)%nat (8 * pi_c2 cap)%nat] else []) ->
  rf_room RF b (56 * cap2 (Z.of_nat cap) + 16) /\ 56 * cap2 (Z.of_nat cap) + 16 <= 2 ^ 28 /\
  (5 + pis_oz o = 6 ->
   rf_room RF (rf_grow RF b (56 * Z.of_nat cap) (56 * cap2 (Z.of_nat cap))) (8 * cap2 (Z.of_nat cap) + 16)).
Proof.
  intros b cap H. cbn [room_run is_call esize] in H. destruct H as [H1 H2].
  destruct (H1 eq_refl) as [R1 R2]. rewrite Nat2Z.inj_mul, pi_cap2 in R1, R2.
  split; [exact R1|]. split; [exact R2|].
  intros Ho. destruct o; [|cbn in Ho; lia].
  cbn [room_run is_call esize rf_ev] in H2. destruct H2 as [H3 _]. destruct (H3 eq_refl) as [R3 _].
  rewrite !Nat2Z.inj_mul, pi_cap2 in R3. exact R3.
Qed.

Lemma pi_room_call : forall b n cap acc y, n = cap ->
  room_run RF b (snd (fst (jturn d o n cap acc y []))) ->
  rf_room RF b (56 * cap2 (Z.of_nat cap) + 16) /\ 56 * cap2 (Z.of_nat cap) + 16 <= 2 ^ 28 /\
  (5 + pis_oz o = 6 ->
   rf_room RF (rf_grow RF b (56 * Z.of_nat cap) (56 * cap2 (Z.of_nat cap))) (8 * cap2 (Z.of_nat cap) + 16)).
Proof.
  intros b n cap acc y -> RM. rewrite jturn_eq in RM. unfold jbind in RM. rewrite pi_grow_nil, Nat.ltb_irrefl in RM.
  cbv beta iota in RM.
  destruct (jafter d o cap (pi_c2 cap) acc y []) as [[r t'] o'] eqn:EJ. cbn [fst snd] in RM.
  apply pi_grow_room. exact (proj1 (room_run_app RF _ b t' RM)).
Qed.

Lemma pi_turn_some : forall tr n cap acc y cap1 tg,
  grow o n cap (skipn (calls tr) pi_ok) = (Some cap1, tg, skipn (calls tr + calls tg) pi_ok) ->
  grow o n cap [] = (Some cap1, tg, []) ->
  ext (jr_items jr_strtod d o pi_x pi_ok) tr (jturn d o n cap acc y (skipn (calls tr) pi_ok)) ->
  room_run RF (rf_run RF b0 tr) (snd (fst (jturn d o n cap acc y []))) ->
  ext (jr_items jr_strtod d o pi_x pi_ok) (tr ++ tg) (jafter d o n cap1 acc y (skipn (calls (tr ++ tg)) pi_ok)) /\
  room_run RF (rf_run RF b0 (tr ++ tg)) (snd (fst (jafter d o n cap1 acc y []))).
Proof.
  intros tr n cap acc y cap1 tg G1 G0 EXT RM. rewrite jturn_eq in EXT, RM. split.
  - rewrite calls_app. exact (ext_bind_some _ _ _ _ _ _ _ _ _ _ G1 EXT).
  - unfold jbind in RM. rewrite G0 in RM. cbv beta iota in RM.
    destruct (jafter d o n cap1 acc y []) as [[r t'] o'] eqn:EJ. cbn [fst snd] in RM |- *.
    destruct (room_run_app RF tg (rf_run RF b0 tr) t' RM) as [_ R2]. rewrite rf_run_app. exact R2.
Qed.

Lemma pi_turn_none : forall tr n cap acc y tg okr,
  grow o n cap (skipn (calls tr) pi_ok) = (None, tg, okr) ->
  ext (jr_items jr_strtod d o pi_x pi_ok) tr (jturn d o n cap acc y (skipn (calls tr) pi_ok)) ->
  jr_items jr_strtod d o pi_x pi_ok = (None, tr ++ tg, okr).
Proof.
  intros tr n cap acc y tg okr G1 EXT. rewrite jturn_eq in EXT. exact (ext_bind_none _ _ _ _ _ _ _ _ _ G1 EXT).
Qed.

Lemma pi_blk_keep : forall Lc Ac mc mdc a k,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  In (a, k) (blocks L0 A0) -> In (a, k) (blocks Lc Ac).
Proof.
  intros Lc Ac mc mdc a k RP Hb. pose proof RP as (_ & _ & _ & _ & _ & _ & _ & UB & PA & _).
  destruct (rk_blk_user L0 A0 a k Hb) as (p & Hp & Ep).
  assert (Hp' : In (p, k) (user_blocks Ac)) by (apply UB; [exact Hp | intros Hf; exact Hf]).
  rewrite <- Ep, <- (PA p k Hp Hp'). exact (rk_blk_of_user Lc Ac p k Hp').
Qed.

Lemma pi_new_keep : forall Lc Ac mc mdc X,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  new_blks Lc Ac X -> new_blks L0 A0 X.
Proof. intros Lc Ac mc mdc X RP NB a k Hin Hb. exact (NB a k Hin (pi_blk_keep Lc Ac mc mdc _ _ RP Hb)). Qed.

Lemma pi_lam_disj : forall L A mem md Lam peak cnt fail a k a' k',
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (a, k) Lam -> In (a', k') Lam ->
  (a, k) <> (a', k') -> a + k <= a' - 16 \/ a' + k' <= a - 16.
Proof.
  intros L A mem md Lam peak cnt fail a k a' k' HM LG H1 H2 Hne.
  pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ H1) as (K1 & B1 & _). destruct (LF _ H2) as (K2 & B2 & _). cbn [fst snd] in K1, B1, K2, B2.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L A mem md HM) as PW.
  assert (Hne' : (a - 16, k + 16) <> (a' - 16, k' + 16)) by (intros E; injection E as E1 E2; apply Hne; f_equal; lia).
  destruct (rk_pairwise_in _ _ _ _ PW B1 B2 Hne') as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia.
Qed.

Lemma pi_statics_img : forall x, alloc_statics x -> in_img B x.
Proof.
  assert (K : forall g, find_segment rsegs g 8 <> None -> forall x, g <= x < g + 8 -> in_img B x).
  { intros g Hg x Hx. destruct (find_segment rsegs g 8) as [s|] eqn:F; [|contradiction].
    destruct (rk_fs_some _ _ _ _ F) as (Hin & H1 & H2). apply (rk_seg_img pi_seg s x Hin). lia. }
  intros x [H|[H|[H|H]]]; [apply (K G_LIVE) | apply (K G_PEAK) | apply (K G_COUNT) | apply (K G_FAIL)];
    first [exact H | vm_compute; discriminate].
Qed.

Lemma pi_new_apart : forall Lc Ac mc mdc L2 A2 m2 md2 a k,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  In (a - 16, k + 16) (blocks L2 A2) -> ~ In (a - 16, k + 16) (blocks Lc Ac) -> pj_apart [(a, k)] v.
Proof.
  intros Lc Ac mc mdc L2 A2 m2 md2 a k RPc RP2 Hb Hn. pose proof RP2 as (M2 & _).
  pose proof RPL as (PL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  destruct (rk_blk_facts L2 A2 m2 md2 _ _ M2 Hb) as (B1 & B2 & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L2 A2 m2 md2 M2) as PW.
  assert (OLD : forall a0 k0, In (a0, k0) (blocks L0 A0) -> a0 <= v -> v + 56 <= a0 + k0 ->
             forall x, a <= x < a + k -> ~ (v <= x < v + 56)).
  { intros a0 k0 Hb0 Ha Hk x Hx Hv.
    pose proof (pi_blk_keep _ _ _ _ _ _ RPc Hb0) as Hc. pose proof (pi_blk_keep _ _ _ _ _ _ RP2 Hb0) as H2.
    assert (Hne : (a0, k0) <> (a - 16, k + 16)) by (intros E; rewrite E in Hc; exact (Hn Hc)).
    destruct (rk_pairwise_in _ _ _ _ PW H2 Hb Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia. }
  intros bb x Hbb Hx. destruct Hbb as [<-|[]]. unfold pj_holds in Hx; cbn [fst snd] in Hx.
  destruct PL as [(P1 & _) | [(a0 & k0 & Hb0 & _ & Ha & Hk) | (a0 & k0 & Hl & Ha & Hk)]].
  - lia.
  - exact (OLD a0 k0 Hb0 Ha Hk x Hx).
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl.
    destruct (LF _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0.
    exact (OLD _ _ Hb0 ltac:(lia) ltac:(lia) x Hx).
Qed.

Lemma pi_new_apart0 : forall L2 A2 m2 md2 a k,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  In (a - 16, k + 16) (blocks L2 A2) -> ~ In (a - 16, k + 16) (blocks L0 A0) -> pj_apart [(a, k)] v.
Proof.
  intros L2 A2 m2 md2 a k RP2 Hb Hn. pose proof RP2 as (M2 & _).
  pose proof RPL as (PL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  destruct (rk_blk_facts L2 A2 m2 md2 _ _ M2 Hb) as (B1 & B2 & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L2 A2 m2 md2 M2) as PW.
  assert (OLD : forall a0 k0, In (a0, k0) (blocks L0 A0) -> a0 <= v -> v + 56 <= a0 + k0 ->
             forall x, a <= x < a + k -> ~ (v <= x < v + 56)).
  { intros a0 k0 Hb0 Ha Hk x Hx Hv.
    pose proof (pi_blk_keep _ _ _ _ _ _ RP2 Hb0) as H2.
    assert (Hne : (a0, k0) <> (a - 16, k + 16)) by (intros E; rewrite E in Hb0; exact (Hn Hb0)).
    destruct (rk_pairwise_in _ _ _ _ PW H2 Hb Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia. }
  intros bb x Hbb Hx. destruct Hbb as [<-|[]]. unfold pj_holds in Hx; cbn [fst snd] in Hx.
  destruct PL as [(P1 & _) | [(a0 & k0 & Hb0 & _ & Ha & Hk) | (a0 & k0 & Hl & Ha & Hk)]].
  - lia.
  - exact (OLD a0 k0 Hb0 Ha Hk x Hx).
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl.
    destruct (LF _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0.
    exact (OLD _ _ Hb0 ltac:(lia) ltac:(lia) x Hx).
Qed.

Lemma pi_fresh_call : forall Lc Ac mc mdc K2 regs2 E2 L2 A2 regs3 m2 md2 Lam2 peak2 cnt2 fail2 Dv x,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  rpost B API K2 Lc Ac regs2 mc mdc E2 (fun _ _ => False) L2 A2 regs3 m2 md2 ->
  ledger B L2 A2 m2 Lam2 peak2 cnt2 fail2 -> incl Dv Lam2 -> new_blks Lc Ac Dv -> blk_set Dv x -> pi_fresh x.
Proof.
  intros Lc Ac mc mdc K2 regs2 E2 L2 A2 regs3 m2 md2 Lam2 peak2 cnt2 fail2 Dv x RPc RP2 LG2 INC NB (a & k & Hin & Hx).
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & UB2 & PA2 & _).
  pose proof RPc as (_ & _ & _ & _ & _ & _ & _ & UBc & PAc & _).
  assert (PR : Permutation Lam2 (Lam2 ++ [])) by (rewrite app_nil_r; apply Permutation_refl).
  destruct (rk_D_facts L2 A2 m2 md2 Lam2 peak2 cnt2 fail2 Lam2 [] a k M2 LG2 PR (INC _ Hin)) as (HB & H1 & H2 & H3 & H4).
  split; [lia|]. split.
  - intros Hi. apply (H4 (x - a) ltac:(lia)). replace (a + (x - a)) with x by lia. exact Hi.
  - intros p n Hp Hpx.
    assert (Hpc : In (p, n) (user_blocks Ac)) by (apply UBc; [exact Hp | intros Hf; exact Hf]).
    assert (Hp2 : In (p, n) (user_blocks A2)) by (apply UB2; [exact Hpc | intros Hf; exact Hf]).
    pose proof (rk_blk_of_user L2 A2 p n Hp2) as Hq. rewrite (PA2 p n Hpc Hp2), (PAc p n Hp Hpc) in Hq.
    pose proof (mr_blocks_disjoint B _ (aa_laws API) L2 A2 m2 md2 M2) as PW.
    assert (Hne : (ptr_addr L0 p, n) <> (a - 16, k + 16)).
    { intros E. apply (NB a k Hin). rewrite <- E, <- (PAc p n Hp Hpc). exact (rk_blk_of_user Lc Ac p n Hpc). }
    destruct (rk_pairwise_in _ _ _ _ PW Hq HB Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia.
Qed.

Lemma pi_errno_img : forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Proof.
  pose proof ENV as (_ & _ & ERR & _). rewrite ERR. intros x Hx.
  destruct (find_segment rsegs strtod_c.STRTOD_ERRNO 4) as [s|] eqn:F; [|vm_compute in F; discriminate].
  destruct (rk_fs_some _ _ _ _ F) as (Hin & H1 & H2). apply (rk_seg_img pi_seg s x Hin). lia.
Qed.

Lemma pi_blk_rplace : forall Lc Ac m mdc Lamc peakc cntc failc R a k s,
  aa_MR API Lc Ac m mdc -> ledger B Lc Ac m Lamc peakc cntc failc -> spZ R = pi_f ->
  In (a, k) Lamc -> a <= s -> s + 56 <= a + k -> rplace B Lc Ac Lamc R m s.
Proof.
  intros Lc Ac m mdc Lamc peakc cntc failc R a k s HM LG SPR Hin Ha Hk.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ a k HM LG Hin) as (R1 & R2 & _).
  pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ Hin) as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
  destruct (rk_blk_facts Lc Ac m mdc _ _ HM Lin) as (_ & _ & B3).
  split; [right; right; exists a, k; split; [exact Hin | lia]|].
  split; [intros Hs; exfalso; rewrite SPR in Hs; unfold pi_f in Hs; lia|].
  intros i Hi.
  assert (NI : ~ in_img B (s + i)).
  { replace (s + i) with (a + (s + i - a)) by lia.
    exact (ledger_block_not_img B Lc Ac m Lamc _ _ _ a k (s + i - a) LG Hin ltac:(lia)). }
  split; [replace (s + i) with (a - 16 + (s + i - (a - 16))) by lia; exact (proj2 (B3 (s + i - (a - 16)) ltac:(lia)))|].
  split; [intros Hs; exact (NI (pi_statics_img _ Hs))|].
  split; [intros He; exact (NI (pi_errno_img _ He)) | exact NI].
Qed.

Lemma pi_lam_same : forall Lc Ac m mdc Lamc peakc cntc failc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 Lam2 peak2 cnt2 fail2
    a k x,
  ledger B Lc Ac m Lamc peakc cntc failc ->
  rpost B API K2 Lc Ac regs2 m mdc E2 gone2 L2 A2 regs3 m2 md2 ->
  ledger B L2 A2 m2 Lam2 peak2 cnt2 fail2 ->
  In (a, k) Lamc -> In (a, k) Lam2 -> ~ gone2 (a - 16) (k + 16) -> a <= x < a + k -> ~ E2 x ->
  pis_same segs m m2 x.
Proof.
  intros Lc Ac m mdc Lamc peakc cntc failc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 Lam2 peak2 cnt2 fail2 a k x
    LG RP2 LG2 Hb Hb2 Hng Hx HE.
  pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ Hb) as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
  destruct (rk_blk_user Lc Ac _ _ Lin) as (p & Hp & Ep).
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & UB2 & _ & _ & _ & _ & _ & Kb2 & _).
  assert (Hp2 : In (p, k + 16) (user_blocks A2)) by (apply UB2; [exact Hp | rewrite Ep; exact Hng]).
  split.
  - replace x with (ptr_addr Lc p + (x - ptr_addr Lc p)) by lia.
    apply (Kb2 p (k + 16) (x - ptr_addr Lc p) Hp Hp2); [lia|].
    replace (ptr_addr Lc p + (x - ptr_addr Lc p)) with x by lia. exact HE.
  - intros _. pose proof (ledger_block_present B API L2 A2 m2 md2 Lam2 _ _ _ a k (x - a) M2 LG2 Hb2 ltac:(lia)) as Hpr.
    replace (a + (x - a)) with x in Hpr by lia. exact (present_writable B m2 x Hpr).
Qed.

Lemma pi_v_same : forall Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 m mdc ->
  rpost B API K2 Lc Ac regs2 m mdc E2 gone2 L2 A2 regs3 m2 md2 -> spZ regs2 <= pi_f ->
  (forall x, v <= x < v + 56 -> ~ E2 x) -> (forall a k, In (a, k) (blocks L0 A0) -> ~ gone2 a k) ->
  forall x, v <= x < v + 56 -> pis_same segs m m2 x.
Proof.
  intros Lc Ac m mdc K2 regs2 E2 gone2 L2 A2 regs3 m2 md2 RPc RP2 SP2 HE HG x Hx.
  pose proof RPL as (PL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof ENV as (_ & _ & ERR & _).
  pose proof RPc as (_ & _ & _ & _ & _ & _ & _ & UBc & PAc & _).
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & UB2 & PA2 & _ & _ & H2 & _ & Kb2 & _).
  assert (BLK : forall a0 k0, In (a0, k0) (blocks L0 A0) -> a0 <= x < a0 + k0 -> pis_same segs m m2 x).
  { intros a0 k0 Hb0 Hx0.
    destruct (rk_blk_user L0 A0 a0 k0 Hb0) as (p & Hp & Ep).
    assert (Hpc : In (p, k0) (user_blocks Ac)) by (apply UBc; [exact Hp | intros Hf; exact Hf]).
    assert (Ec : ptr_addr Lc p = a0) by (rewrite (PAc p k0 Hp Hpc); exact Ep).
    assert (Hp2 : In (p, k0) (user_blocks A2)) by (apply UB2; [exact Hpc | rewrite Ec; exact (HG a0 k0 Hb0)]).
    assert (E2' : ptr_addr L2 p = a0) by (rewrite (PA2 p k0 Hpc Hp2); exact Ec).
    split.
    - replace x with (ptr_addr Lc p + (x - ptr_addr Lc p)) by lia.
      apply (Kb2 p k0 (x - ptr_addr Lc p) Hpc Hp2); [lia|].
      replace (ptr_addr Lc p + (x - ptr_addr Lc p)) with x by lia. exact (HE x Hx).
    - intros _. pose proof (rk_blk_of_user L2 A2 p k0 Hp2) as Hq. rewrite E2' in Hq.
      destruct (rk_blk_facts L2 A2 m2 md2 _ _ M2 Hq) as (_ & _ & B3).
      destruct (B3 (x - a0) ltac:(lia)) as (Hpr & _). replace (a0 + (x - a0)) with x in Hpr by lia.
      exact (present_writable B m2 x Hpr). }
  destruct PL as [(P1 & P2) | [(a0 & k0 & Hb0 & _ & Ha & Hk) | (a0 & k0 & Hl & Ha & Hk)]].
  - assert (NS : ~ scratch_k B K2 regs2 x)
      by (unfold scratch_k; rewrite ERR; unfold strtod_c.STRTOD_ERRNO; unfold pi_f in SP2; lia).
    destruct (H2 x ltac:(lia) NS (HE x Hx)) as [E1 E3]. split; [exact E1 | intros Hw; apply E3; exact Hw].
  - exact (BLK a0 k0 Hb0 ltac:(lia)).
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl.
    destruct (LF _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0.
    exact (BLK _ _ Hb0 ltac:(lia)).
Qed.

Lemma pi_text_ok : forall fxc Lc Ac m mdc Lamc tr D R peakc cntc failc,
  pi_glob fxc Lc Ac m mdc Lamc tr D -> ledger B Lc Ac m Lamc peakc cntc failc -> spZ R = pi_f ->
  text_ok B Lc Ac Lamc R text len.
Proof.
  intros fxc Lc Ac m mdc Lamc tr D R peakc cntc failc (_ & _ & RP & _ & _ & PERM & _ & _ & NB & _) LG SPR.
  pose proof RP as (M & _).
  pose proof TOK as (TXL & TXN). pose proof pi_HM0 as HM0.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  assert (NOWN : forall i, 0 <= i < len -> (alloc_ceiling <= text + i \/
                   (exists a k, In (a, k) (blocks Lc Ac) /\ a <= text + i < a + k)) -> ~ owned B Lc Ac (text + i)).
  { intros i Hi [Hs|(a & k & Hb & Hx)] Ho.
    - pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M Ho). lia.
    - destruct (rk_blk_facts Lc Ac m mdc a k M Hb) as (_ & _ & B3).
      apply (proj2 (B3 (text + i - a) ltac:(lia))). replace (a + (text + i - a)) with (text + i) by lia. exact Ho. }
  destruct TXL as [Hs | [Him | [(a & k & Hb & Hnl & Ha & Hk) | (a & k & Hl & Ha & Hk)]]].
  - split; [left; rewrite SPR; unfold pi_f; lia|].
    intros i Hi. destruct (TXN i Hi) as (N1 & N2 & N3). split; [|tauto]. apply NOWN; [exact Hi | left; lia].
  - split; [right; left; exact Him|].
    intros i Hi. destruct (TXN i Hi) as (N1 & N2 & N3). split; [|tauto].
    intros [Ho|Ho].
    + pose proof (YL01.ax_img AX Lc Ac m mdc (text + i) M (Him i Hi) Ho) as HCx.
      apply N1. exact (CO L0 A0 mem0 md0 (text + i) HM0 HCx).
    + apply N1. right. exact Ho.
  - pose proof (pi_blk_keep _ _ _ _ _ _ RP Hb) as Hb'.
    split.
    + right; right; left. exists a, k. split; [exact Hb'|]. split; [|lia].
      intros Hl. unfold lin in Hl. apply (Permutation_in _ PERM) in Hl. apply in_app_or in Hl.
      destruct Hl as [Hl|Hl]; [|exact (Hnl Hl)].
      apply (NB _ _ Hl). replace (a + 16 - 16) with a by lia. replace (k - 16 + 16) with k by lia. exact Hb.
    + intros i Hi. destruct (TXN i Hi) as (N1 & N2 & N3). split; [|tauto].
      apply NOWN; [exact Hi | right; exists a, k; split; [exact Hb' | lia]].
  - assert (Hl' : In (a, k) Lamc) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact Hl).
    pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
    destruct (LF _ Hl') as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
    split; [right; right; right; exists a, k; split; [exact Hl' | lia]|].
    intros i Hi. destruct (TXN i Hi) as (N1 & N2 & N3). split; [|tauto].
    apply NOWN; [exact Hi | right; exists (a - 16), (k + 16); split; [exact Lin | lia]].
Qed.

Lemma pi_jval_some : forall tr n cap acc nm y t r tv ok',
  jr_value jr_strtod (S d) y (skipn (calls tr) pi_ok) = (Some (t, r), tv, ok') ->
  ext (jr_items jr_strtod d o pi_x pi_ok) tr (jval d o n cap acc nm y (skipn (calls tr) pi_ok)) ->
  ext (jr_items jr_strtod d o pi_x pi_ok) (tr ++ tv) (jtail d o n cap acc nm t r ok').
Proof. intros tr n cap acc nm y t r tv ok' G EXT. unfold jval in EXT. exact (ext_bind_some _ _ _ _ _ _ _ _ _ _ G EXT). Qed.

Lemma pi_jval_none : forall tr n cap acc nm y tv ok',
  jr_value jr_strtod (S d) y (skipn (calls tr) pi_ok) = (None, tv, ok') ->
  ext (jr_items jr_strtod d o pi_x pi_ok) tr (jval d o n cap acc nm y (skipn (calls tr) pi_ok)) ->
  jr_items jr_strtod d o pi_x pi_ok = (None, tr ++ tv, ok').
Proof. intros tr n cap acc nm y tv ok' G EXT. unfold jval in EXT. exact (ext_bind_none _ _ _ _ _ _ _ _ _ G EXT). Qed.

Lemma pi_pv_agree : forall tr y okv res tv okr,
  jr_value jr_strtod (S d) y okv = (res, tv, okr) -> oks okv (cnt0 + Z.of_nat (calls tr)) fail0 (calls tv) ->
  jr_value jr_strtod (S d) y (skipn (calls tr) pi_ok) = (res, tv, skipn (calls tv) (skipn (calls tr) pi_ok)).
Proof.
  intros tr y okv res tv okr E OK.
  apply (agrees_det _ _ okv _ res tv okr (agrees_jr_value jr_strtod (S d) y) E).
  intros i Hi. rewrite pi_ok_skip, (OK i Hi). reflexivity.
Qed.

Lemma pi_ro_img : forall x : word, lib.Lib.Mem.ro_addr segs x = true -> in_img B (bv_unsigned x).
Proof.
  intros x H. unfold lib.Lib.Mem.ro_addr in H. rewrite pi_seg in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:F; [|discriminate].
  destruct (rk_fs_some _ _ _ _ F) as (Hin & H1 & H2). apply (rk_seg_img pi_seg s _ Hin). lia.
Qed.

Lemma pi_guard_img : forall k, 0 <= k < 8 -> in_img B (ms_got_guard B + k) /\ in_img B (ms_guard B + k).
Proof.
  pose proof ENV as (_ & _ & _ & GG & GD & _). rewrite GG, GD. intros k Hk.
  assert (K : forall g, find_segment rsegs g 8 <> None -> forall x, g <= x < g + 8 -> in_img B x).
  { intros g Hg x Hx. destruct (find_segment rsegs g 8) as [s|] eqn:F; [|contradiction].
    destruct (rk_fs_some _ _ _ _ F) as (Hin & H1 & H2). apply (rk_seg_img pi_seg s x Hin). lia. }
  split; [apply (K strtod_c.STRTOD_GOT_GUARD) | apply (K strtod_c.STRTOD_GUARD)]; first [lia | vm_compute; discriminate].
Qed.

Lemma pi_rd_munch : forall m m' W, rd_cells B m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> ~ in_img B x) -> rd_cells B m'.
Proof.
  intros m m' W (RO & G1 & g & G2) MU HW.
  pose proof ENV as (_ & _ & _ & GG & GD & _).
  assert (OUT : forall x, 0 <= x < 2 ^ 64 -> in_img B x -> outside W x).
  { intros x Hx Hi. destruct (rk_outside_dec W x) as [Ho|Ho]; [exact Ho | exfalso; exact (HW x Hx Ho Hi)]. }
  split.
  { intros a Ha. rewrite (pi_mrd_eq segs m m' a (MU a (OUT _ (bv_unsigned_in_range 64 a) (pi_ro_img a Ha)))).
    exact (RO a Ha). }
  split.
  { apply (KindBGlue.kb_word_munch segs m m' W); [exact G1 | exact MU |]. intros k Hk.
    assert (R : 0 <= ms_got_guard B + k < 2 ^ 64) by (rewrite GG; unfold strtod_c.STRTOD_GOT_GUARD; lia).
    split; [exact R | exact (OUT _ R (proj1 (pi_guard_img k Hk)))]. }
  exists g. apply (KindBGlue.kb_word_munch segs m m' W); [exact G2 | exact MU |]. intros k Hk.
  assert (R : 0 <= ms_guard B + k < 2 ^ 64) by (rewrite GD; unfold strtod_c.STRTOD_GUARD; lia).
  split; [exact R | exact (OUT _ R (proj2 (pi_guard_img k Hk)))].
Qed.

Lemma pi_v_noown : forall L2 A2 m2 md2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  forall i, 0 <= i < 56 -> ~ owned B L2 A2 (v + i).
Proof.
  intros L2 A2 m2 md2 RP2 i Hi. pose proof RP2 as (M2 & _).
  pose proof RPL as (PL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  assert (BLK : forall a0 k0, In (a0, k0) (blocks L0 A0) -> a0 <= v -> v + 56 <= a0 + k0 -> ~ owned B L2 A2 (v + i)).
  { intros a0 k0 Hb0 Ha Hk. pose proof (pi_blk_keep _ _ _ _ _ _ RP2 Hb0) as H2.
    destruct (rk_blk_facts L2 A2 m2 md2 _ _ M2 H2) as (_ & _ & B3).
    replace (v + i) with (a0 + (v + i - a0)) by lia. exact (proj2 (B3 (v + i - a0) ltac:(lia))). }
  destruct PL as [(P1 & P2) | [(a0 & k0 & Hb0 & _ & Ha & Hk) | (a0 & k0 & Hl & Ha & Hk)]].
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - exact (BLK a0 k0 Hb0 Ha Hk).
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl.
    destruct (LF _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0. exact (BLK _ _ Hb0 ltac:(lia) ltac:(lia)).
Qed.

Lemma pi_v_heads : forall L2 A2 m2 md2 Lam2 D2 peak2 cnt2 fail2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  ledger B L2 A2 m2 Lam2 peak2 cnt2 fail2 -> Permutation Lam2 (D2 ++ Lam0) -> new_blks L0 A0 D2 ->
  forall a k x, In (a, k) Lam2 -> a - 16 <= x < a - 8 -> ~ (v <= x < v + 56).
Proof.
  intros L2 A2 m2 md2 Lam2 D2 peak2 cnt2 fail2 RP2 LG2 PERM NB a k x Hin Hx Hv. pose proof RP2 as (M2 & _).
  pose proof RPL as (PL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  destruct (ledger_block_range B API L2 A2 m2 md2 Lam2 _ _ _ a k M2 LG2 Hin) as (R1 & R2 & _).
  pose proof LG2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ Hin) as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L2 A2 m2 md2 M2) as PW.
  destruct PL as [(P1 & P2) | [(b & kb & Hb & Hnl & Ha & Hk) | (b & kb & Hl & Ha & Hk)]].
  - lia.
  - pose proof (pi_blk_keep _ _ _ _ _ _ RP2 Hb) as H2.
    assert (Hne : (b, kb) <> (a - 16, k + 16)).
    { intros E. injection E as E1 E2. apply (Permutation_in _ PERM) in Hin. apply in_app_or in Hin.
      destruct Hin as [Hin|Hin].
      - apply (NB a k Hin). rewrite <- E1, <- E2. exact Hb.
      - apply Hnl. unfold lin. replace (b + 16) with a by lia. replace (kb - 16) with k by lia. exact Hin. }
    destruct (rk_pairwise_in _ _ _ _ PW H2 Lin Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia.
  - assert (Hl2 : In (b, kb) Lam2) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; exact Hl).
    destruct (Z.eq_dec a b) as [<-|Nab]; [lia|].
    assert (Hne : (a, k) <> (b, kb)) by (intros E; injection E as E1 _; exact (Nab E1)).
    destruct (pi_lam_disj L2 A2 m2 md2 Lam2 _ _ _ a k b kb M2 LG2 Hin Hl2 Hne); lia.
Qed.

Lemma pi_new_raw : forall L2 A2 m2 md2 b kb x,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  In (b, kb) (blocks L2 A2) -> ~ In (b, kb) (blocks L0 A0) -> b <= x < b + kb -> ~ (v <= x < v + 56).
Proof.
  intros L2 A2 m2 md2 b kb x RP2 Hb Hn Hx Hv. pose proof RP2 as (M2 & _).
  pose proof RPL as (PL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  destruct (rk_blk_facts L2 A2 m2 md2 _ _ M2 Hb) as (B1 & B2 & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L2 A2 m2 md2 M2) as PW.
  assert (OLD : forall a0 k0, In (a0, k0) (blocks L0 A0) -> a0 <= v -> v + 56 <= a0 + k0 -> False).
  { intros a0 k0 Hb0 Ha Hk.
    pose proof (pi_blk_keep _ _ _ _ _ _ RP2 Hb0) as H2.
    assert (Hne : (a0, k0) <> (b, kb)) by (intros E; rewrite E in Hb0; exact (Hn Hb0)).
    destruct (rk_pairwise_in _ _ _ _ PW H2 Hb Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia. }
  destruct PL as [(P1 & _) | [(a0 & k0 & Hb0 & _ & Ha & Hk) | (a0 & k0 & Hl & Ha & Hk)]].
  - lia.
  - exact (OLD a0 k0 Hb0 Ha Hk).
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl.
    destruct (LF _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0. exact (OLD _ _ Hb0 ltac:(lia) ltac:(lia)).
Qed.

Lemma pi_D_nodup : forall L A m Lam peak cnt fail D, ledger B L A m Lam peak cnt fail -> Permutation Lam (D ++ Lam0) ->
  NoDup D.
Proof.
  intros L A m Lam peak cnt fail D LG PERM. pose proof LG as (_ & _ & _ & _ & ND & _).
  pose proof (pis_nodup_new D [] Lam Lam0 ND PERM (fun _ H => match H with end) ltac:(constructor)) as H.
  rewrite app_nil_r in H. exact H.
Qed.

Definition pi_next (w : nat) : config -> Prop :=
  fun c' => pi_post c' \/ exists w', (w' < w)%nat /\ pi_inv w' c'.

Definition pi_gc (w : nat) (c : config) : Prop :=
  exists (fxc : YK11.FPState) (R : bvmap 5 word) (m : word -> option byte) (mdc : Model) (Lc : layout) (Ac : astate)
    (Lamc : list (Z * Z)) (tr : list ev) (D : list (Z * Z)) (n cap : nat) (acc : list (list Z * jv))
    (P num kids keys : Z) (Di : list (Z * Z)),
    c = mkCfg (@mkst fxc R (Z_to_bv 64 0x147e8) m (seg_rom segs)) mdc /\
    (d < MAXD)%nat /\ pi_cs R /\ getr R 1 = Z_to_bv 64 0x15214 /\ getr R 10 = Z_to_bv 64 v /\
    pi_glob fxc Lc Ac m mdc Lamc tr D /\
    ledger B Lc Ac m Lamc (Z.max peak0 (lsum Lam0 + hpeak tr)) (cnt0 + Z.of_nat (calls tr)) fail0 /\
    ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls tr)) /\
    pj_in_ok segs m q text len P (Z.of_nat d + 1) tb /\
    (length (rest_at tb text P) < w)%nat /\
    Z.of_nat (calls tr) + 2 * Z.of_nat (length (rest_at tb text P)) + 2 <= 2 * Z.of_nat (length pi_x) /\
    ext (jr_items jr_strtod d o pi_x pi_ok) tr (jturn d o n cap acc (rest_at tb text P) (skipn (calls tr) pi_ok)) /\
    room_run RF (rf_run RF b0 tr) (snd (fst (jturn d o n cap acc (rest_at tb text P) []))) /\
    length acc = n /\ inv n cap /\
    D = pis_slots o kids keys (Z.of_nat cap) ++ Di /\
    pis_open segs m (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) (map snd (rev acc)) (map fst (rev acc)) Di /\
    Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev acc)).

Section Sep.
Variables (gfx : YK11.FPState) (gR : bvmap 5 word) (gm : word -> option byte) (gmd : Model) (gL : layout)
  (gA : astate) (gLam : list (Z * Z)) (gtr : list ev) (gD : list (Z * Z)) (gn gcap : nat)
  (gacc : list (list Z * jv)) (gP gnum gkids gkeys : Z) (gDi : list (Z * Z)).
Hypothesis gHD : (d < MAXD)%nat.
Hypothesis gCS : pi_cs0 gR.
Hypothesis gG1 : (getr gR 1 = Z_to_bv 64 0x15214 /\ pi_cs gR) \/ getr gR 1 = Z_to_bv 64 0x150b8.
Hypothesis gG10 : getr gR 10 = Z_to_bv 64 v.
Hypothesis gGL : pi_glob gfx gL gA gm gmd gLam gtr gD.
Hypothesis gLG : ledger B gL gA gm gLam (Z.max peak0 (lsum Lam0 + hpeak gtr)) (cnt0 + Z.of_nat (calls gtr)) fail0.
Hypothesis gNF : ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls gtr)).
Hypothesis gPIN : pj_in_ok segs gm q text len gP (Z.of_nat d + 1) tb.
Hypothesis gCB : Z.of_nat (calls gtr) + 2 * Z.of_nat (length (rest_at tb text gP)) + 2 <= 2 * Z.of_nat (length pi_x).
Hypothesis gEXT :
  ext (jr_items jr_strtod d o pi_x pi_ok) gtr (jturn d o gn gcap gacc (rest_at tb text gP) (skipn (calls gtr) pi_ok)).
Hypothesis gROOM : room_run RF (rf_run RF b0 gtr) (snd (fst (jturn d o gn gcap gacc (rest_at tb text gP) []))).
Hypothesis gLA : length gacc = gn.
Hypothesis gINV : inv gn gcap.
Hypothesis gED : gD = pis_slots o gkids gkeys (Z.of_nat gcap) ++ gDi.
Hypothesis gPO : pis_open segs gm (lin gLam) v o gnum gkids gkeys (Z.of_nat gcap) (Z.of_nat gn) (map snd (rev gacc))
  (map fst (rev gacc)) gDi.
Hypothesis gDEP : Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev gacc)).

Local Notation gWr := (grow_writes v (5 + pis_oz o) gkids gkeys (Z.of_nat gn) (Z.of_nat gcap)).
Local Notation gGo := (grow_gone (5 + pis_oz o) gkids gkeys (Z.of_nat gn) (Z.of_nat gcap)).

Lemma g_SP : spZ gR = pi_f.
Proof. exact (pi_sp0 gR gCS). Qed.

Lemma g_ts : length (map snd (rev gacc)) = gn.
Proof. rewrite length_map, length_rev. exact gLA. Qed.

Lemma g_slot_incl : incl (pis_slots o gkids gkeys (Z.of_nat gcap)) gLam.
Proof.
  intros b Hb. apply (pis_open_incl segs gm gLam v o gnum gkids gkeys _ _ _ _ gDi gPO). apply in_or_app. left. exact Hb.
Qed.

Lemma g_Di_incl : incl gDi gLam.
Proof.
  intros b Hb. apply (pis_open_incl segs gm gLam v o gnum gkids gkeys _ _ _ _ gDi gPO). apply in_or_app. right. exact Hb.
Qed.

Lemma g_kids_in : Z.of_nat gcap <> 0 -> In (gkids, 56 * Z.of_nat gcap) gLam.
Proof.
  intros E0. apply g_slot_incl. unfold pis_slots, kids_blk. rewrite (proj2 (Z.eqb_neq _ 0) E0). left. reflexivity.
Qed.

Lemma g_keys_in : o = true -> Z.of_nat gcap <> 0 -> In (gkeys, 8 * Z.of_nat gcap) gLam.
Proof.
  intros Eo E0. apply g_slot_incl. unfold pis_slots, kids_blk, keys_blk. rewrite Eo, (proj2 (Z.eqb_neq _ 0) E0).
  cbn. right. left. reflexivity.
Qed.

Lemma g_blk_fresh : forall a, blk_set (kids_blk gkids (Z.of_nat gcap) ++ keys_blk (5 + pis_oz o) gkeys (Z.of_nat gcap)) a ->
  pi_fresh a.
Proof.
  pose proof gGL as (_ & _ & RP & _ & _ & PERM & _ & _ & NB & _).
  intros a (a' & k' & Hin & Hx). apply (pi_fresh_D gL gA gm gmd gLam _ _ _ gD a RP gLG PERM NB).
  exists a', k'. split; [rewrite gED; apply in_or_app; left; exact Hin | exact Hx].
Qed.

Lemma g_HGE : forall a, gWr a -> pi_E0 a \/ pi_fresh a.
Proof.
  intros a (_ & [Hv|[Hv|[Hb|Hs]]]).
  - left; left; lia.
  - left; left; lia.
  - right. exact (g_blk_fresh a Hb).
  - left; right; right; exact Hs.
Qed.

Lemma g_HGG : forall p n, In (p, n) (user_blocks A0) -> ~ gGo (ptr_addr L0 p) n.
Proof.
  pose proof gGL as (_ & _ & _ & _ & _ & _ & _ & _ & NB & _).
  intros p n Hp (_ & Hf). unfold freed in Hf.
  assert (Hin : In (ptr_addr L0 p + 16, n - 16) gD) by (rewrite gED; apply in_or_app; left; exact Hf).
  apply (NB _ _ Hin).
  replace (ptr_addr L0 p + 16 - 16) with (ptr_addr L0 p) by lia. replace (n - 16 + 16) with n by lia.
  exact (rk_blk_of_user L0 A0 p n Hp).
Qed.

Lemma g_WQ : forall a, gWr a -> ~ (q <= a < q + 24).
Proof.
  intros a (_ & [Hv|[Hv|[Hb|Hs]]]) Hq; pose proof DJV as DV; cbn [Frame.disjoint_from] in DV;
    pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _); pose proof rk_ceil as HC; pose proof pi_K80 as KP.
  - lia.
  - lia.
  - destruct (g_blk_fresh a Hb) as (Hf & _). lia.
  - unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia.
Qed.

Lemma g_post_common : forall L2 A2 regs2 mem2 md2,
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 /\
  pi_frm mem2 /\ pj_in_ok segs mem2 q text len gP (Z.of_nat d + 1) tb /\
  (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo mem2) /\ pi_cs0 regs2.
Proof.
  intros L2 A2 regs2 mem2 md2 RP2.
  pose proof gGL as (_ & _ & RP & _ & FR & _ & _ & _ & _ & _ & AUX).
  pose proof (pi_K_bounds gHD) as (KG & _ & _ & _ & KG0 & _).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof pi_K80 as KP.
  assert (SPl : spZ gR <= pi_f) by (rewrite g_SP; lia).
  assert (RPc : rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2)
    by exact (pi_rp_call gL gA gm gmd GROW_K gR _ _ L2 A2 regs2 mem2 md2 RP RP2 g_SP KG KG0 g_HGE g_HGG).
  split; [exact RPc|].
  split; [exact (pi_frm_call gL gA gm gmd GROW_K gR _ _ L2 A2 regs2 mem2 md2 RP2 SPl g_HGE FR)|].
  split.
  { apply (pi_in_call gL gA gm gmd GROW_K gR _ _ L2 A2 regs2 mem2 md2 gP (Z.of_nat d + 1) RPc RP2);
      [rewrite g_SP; unfold pi_f; lia | exact g_WQ | exact gPIN]. }
  split; [exact (pi_aux_call gL gA gm gmd GROW_K gR _ _ L2 A2 regs2 mem2 md2 RP2 SPl g_HGE AUX)|].
  pose proof RP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _). exact (pi_cs0_rp gR regs2 gCS RPr).
Qed.

Lemma g_Di_same : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2,
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> incl gDi Lam2 ->
  forall x, (exists b, In b gDi /\ pj_holds b x) -> pis_same segs gm mem2 x.
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 RP2 LG2 INC x ((a & k) & Hb & Hx).
  unfold pj_holds in Hx; cbn [fst snd] in Hx.
  pose proof gPO as (HN & HA & _).
  pose proof gGL as (_ & _ & RP & _). pose proof RP as (M & _).
  assert (HbL : In (a, k) gLam) by exact (g_Di_incl _ Hb).
  pose proof gLG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ HbL) as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
  destruct (rk_blk_user gL gA _ _ Lin) as (p & Hp & Ep).
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & UB2 & _ & _ & _ & _ & _ & Kb2 & _).
  assert (NS : ~ In (a, k) (pis_slots o gkids gkeys (Z.of_nat gcap)))
    by (intros Hs; exact (pis_nodup_app_disj _ _ _ _ HN Hs Hb)).
  assert (Hp2 : In (p, k + 16) (user_blocks A2)).
  { apply UB2; [exact Hp|]. intros (_ & Hf). unfold freed in Hf. rewrite Ep in Hf.
    replace (a - 16 + 16) with a in Hf by lia. replace (k + 16 - 16) with k in Hf by lia. exact (NS Hf). }
  split.
  - replace x with (ptr_addr gL p + (x - ptr_addr gL p)) by lia.
    apply (Kb2 p (k + 16) (x - ptr_addr gL p) Hp Hp2); [lia|].
    replace (ptr_addr gL p + (x - ptr_addr gL p)) with x by lia.
    intros (_ & [Hv|[Hv|[(a' & k' & Hin & Hx')|Hs]]]).
    + exact (HA (a, k) x ltac:(apply in_or_app; right; exact Hb) ltac:(unfold pj_holds; cbn [fst snd]; lia) ltac:(lia)).
    + exact (HA (a, k) x ltac:(apply in_or_app; right; exact Hb) ltac:(unfold pj_holds; cbn [fst snd]; lia) ltac:(lia)).
    + assert (Hin' : In (a', k') gLam) by exact (g_slot_incl _ Hin).
      assert (Hne : (a, k) <> (a', k')) by (intros E; apply NS; rewrite E; exact Hin).
      destruct (pi_lam_disj gL gA gm gmd gLam _ _ _ a k a' k' M gLG HbL Hin' Hne); lia.
    + apply (ledger_block_not_img B gL gA gm gLam _ _ _ a k (x - a) gLG HbL ltac:(lia)).
      replace (a + (x - a)) with x by lia. exact (pi_statics_img x Hs).
  - intros _.
    pose proof (ledger_block_present B API L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 a k (x - a) M2 LG2 (INC _ Hb) ltac:(lia))
      as Hpr.
    replace (a + (x - a)) with x in Hpr by lia. exact (present_writable B mem2 x Hpr).
Qed.

Lemma g_lam_keep_lt : forall L2 A2 regs2 mem2 md2,
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 -> Z.of_nat gn < Z.of_nat gcap ->
  forall a k i, In (a, k) gLam -> 0 <= i < k -> mbyte segs mem2 (a + i) = mbyte segs gm (a + i).
Proof.
  intros L2 A2 regs2 mem2 md2 RP2 Hlt a k i HbL Hi.
  pose proof gLG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ HbL) as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
  destruct (rk_blk_user gL gA _ _ Lin) as (p & Hp & Ep).
  pose proof RP2 as (_ & _ & _ & _ & _ & _ & _ & UB2 & _ & _ & _ & _ & _ & Kb2 & _).
  assert (Hp2 : In (p, k + 16) (user_blocks A2)) by (apply UB2; [exact Hp | intros (Hc & _); lia]).
  replace (a + i) with (ptr_addr gL p + (i + 16)) by lia.
  apply (Kb2 p (k + 16) (i + 16) Hp Hp2); [lia|]. intros (Hc & _). lia.
Qed.

Lemma g_inv : forall L2 A2 regs2 mem2 md2 Lam2 R' tg cap1 kids' keys',
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 -> rd_cells B mem2 ->
  grow o gn gcap (skipn (calls gtr) pi_ok) = (Some cap1, tg, skipn (calls gtr + calls tg) pi_ok) ->
  grow o gn gcap [] = (Some cap1, tg, []) ->
  ledger B L2 A2 mem2 Lam2 (Z.max peak0 (lsum Lam0 + hpeak (gtr ++ tg))) (cnt0 + Z.of_nat (calls (gtr ++ tg))) fail0 ->
  ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls (gtr ++ tg))) ->
  rf_ok RF A2 (rf_run RF b0 (gtr ++ tg)) ->
  Permutation Lam2 ((pis_slots o kids' keys' (Z.of_nat cap1) ++ gDi) ++ Lam0) ->
  Permutation (map snd (pis_slots o kids' keys' (Z.of_nat cap1) ++ gDi)) (map Z.of_nat (lsz (gtr ++ tg))) ->
  Z.of_nat (length (pis_slots o kids' keys' (Z.of_nat cap1) ++ gDi)) = nlive (gtr ++ tg) ->
  new_blks L0 A0 (pis_slots o kids' keys' (Z.of_nat cap1) ++ gDi) ->
  pis_open segs mem2 (lin Lam2) v o gnum kids' keys' (Z.of_nat cap1) (Z.of_nat gn) (map snd (rev gacc))
    (map fst (rev gacc)) gDi ->
  pi_cs R' ->
  pi_inv (length (rest_at tb text gP)) (mkCfg (@mkst gfx R' (Z_to_bv 64 0x150d8) mem2 (seg_rom segs)) md2).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 R' tg cap1 kids' keys' RP2 RD2 G1 G0 LG2 NF2 RS2 PERM2 HP2 NL2 NB2 PO2 CS'.
  destruct (g_post_common L2 A2 regs2 mem2 md2 RP2) as (RPc & FR2 & PIN2 & AUX2 & _).
  destruct (pi_turn_some gtr gn gcap gacc _ cap1 tg G1 G0 gEXT gROOM) as (EXT2 & ROOM2).
  pose proof (grow_spec o gn gcap (skipn (calls gtr) pi_ok) gINV) as GS. rewrite G1 in GS.
  destruct GS as (INV2 & _ & _ & _ & CT & _).
  assert (HIF : forall b : bool, ((if b then 2 else 1) <= 2)%nat) by (intros []; lia).
  pose proof (HIF o) as HIo.
  pose proof gGL as (FZ & FK & _).
  exists gfx, R', mem2, md2, L2, A2, Lam2, (gtr ++ tg), (pis_slots o kids' keys' (Z.of_nat cap1) ++ gDi), gn, cap1, gacc,
    gP, gnum, kids', keys', gDi.
  split; [reflexivity|]. split; [exact gHD|]. split; [exact CS'|].
  split.
  { split; [exact FZ|]. split; [exact FK|]. split; [exact RPc|]. split; [exact RD2|]. split; [exact FR2|].
    split; [exact PERM2|]. split; [exact HP2|]. split; [exact NL2|]. split; [exact NB2|].
    split; [exact RS2 | exact AUX2]. }
  split; [exact LG2|]. split; [exact NF2|]. split; [exact PIN2|]. split; [reflexivity|].
  split; [rewrite calls_app, Nat2Z.inj_add; lia|].
  split; [exact EXT2|]. split; [exact ROOM2|]. split; [exact gLA|]. split; [exact INV2|].
  split; [reflexivity|]. split; [exact PO2 | exact gDEP].
Qed.

Lemma g_arm_lt : forall regs2 mem2 md2 R',
  rpost B API GROW_K gL gA gR gm gmd gWr gGo gL gA regs2 mem2 md2 -> rd_cells B mem2 ->
  ledger B gL gA mem2 gLam (Z.max peak0 (lsum Lam0 + hpeak gtr)) (cnt0 + Z.of_nat (calls gtr)) fail0 ->
  rf_ok RF gA (rf_run RF b0 gtr) -> Z.of_nat gn < Z.of_nat gcap ->
  pj_hdr segs mem2 v (5 + pis_oz o) gnum 0 gkids gkeys (Z.of_nat gn) (Z.of_nat gcap) -> pi_cs R' ->
  pi_inv (length (rest_at tb text gP)) (mkCfg (@mkst gfx R' (Z_to_bv 64 0x150d8) mem2 (seg_rom segs)) md2).
Proof.
  intros regs2 mem2 md2 R' RP2 RD2 LG2 RS2 Hlt Hh2 CS'.
  assert (Hlt' : (gn < gcap)%nat) by lia.
  pose proof gGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP2 as (M2 & _).
  apply (g_inv gL gA regs2 mem2 md2 gLam R' [] gcap gkids gkeys RP2 RD2); rewrite ?app_nil_r.
  - rewrite pi_grow_val, (proj2 (Nat.ltb_lt _ _) Hlt'). cbn [calls]. rewrite Nat.add_0_r. reflexivity.
  - rewrite pi_grow_nil, (proj2 (Nat.ltb_lt _ _) Hlt'). reflexivity.
  - exact LG2.
  - exact gNF.
  - exact RS2.
  - rewrite <- gED. exact PERM.
  - rewrite <- gED. exact HP.
  - rewrite <- gED. exact NL.
  - rewrite <- gED. exact NB.
  - apply (pis_grow_kept segs gm mem2 (lin gLam) v o gnum gkids gkeys (Z.of_nat gcap) (Z.of_nat gn) _ _ gDi gPO Hh2).
    + intros i Hi. assert (E0 : Z.of_nat gcap <> 0) by lia.
      exact (g_lam_keep_lt gL gA regs2 mem2 md2 RP2 Hlt gkids (56 * Z.of_nat gcap) i (g_kids_in E0) Hi).
    + intros Eo i Hi. assert (E0 : Z.of_nat gcap <> 0) by lia.
      exact (g_lam_keep_lt gL gA regs2 mem2 md2 RP2 Hlt gkeys (8 * Z.of_nat gcap) i (g_keys_in Eo E0) Hi).
    + intros i Hi _. rewrite g_ts in Hi. assert (E0 : Z.of_nat gcap <> 0) by lia.
      pose proof (ledger_block_present B API gL gA mem2 md2 gLam _ _ _ gkids (56 * Z.of_nat gcap) i M2 LG2 (g_kids_in E0)
        ltac:(lia)) as Hpr.
      exact (present_writable B mem2 _ Hpr).
    + exact (g_Di_same gL gA regs2 mem2 md2 gLam _ _ _ RP2 LG2 g_Di_incl).
    + rewrite g_ts. lia.
  - exact CS'.
Qed.

Lemma g_after : forall m P, pj_in_ok segs m q text len P (Z.of_nat d + 1) tb ->
  pj_in_after B m q text len (Z.of_nat d + 1) 33.
Proof.
  intros m P (Q0 & Q8 & Q16 & WQ & _ & _ & _ & Tp & _ & _ & _ & Dd).
  exists P, (Z.of_nat d + 1). split; [lia|]. split; [lia|].
  split; [exact Q0|]. split; [exact Q8|]. split; [exact Q16 | exact WQ].
Qed.

Lemma g_newblk : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 k' sz,
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> In (k', sz) Lam2 -> new_blks gL gA [(k', sz)] -> incl gDi Lam2 ->
  56 * Z.of_nat gn <= sz ->
  4112 <= k' /\ k' + sz <= alloc_ceiling /\
  (forall i, 0 <= i < 56 * Z.of_nat gn -> writable_at segs mem2 (k' + i)) /\
  pis_apart_n gDi k' (56 * Z.of_nat gn) /\ pj_apart [(k', sz)] v.
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 k' sz RP2 LG2 Hin NBk INC Hsz.
  pose proof RP2 as (M2 & _). destruct (g_post_common L2 A2 regs2 mem2 md2 RP2) as (RPc & _).
  pose proof gGL as (_ & _ & RP & _).
  destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ k' sz M2 LG2 Hin) as (R1 & R2 & _).
  split; [lia|]. split; [lia|].
  split.
  { intros i Hi. pose proof (ledger_block_present B API L2 A2 mem2 md2 Lam2 _ _ _ k' sz i M2 LG2 Hin ltac:(lia)) as Hpr.
    exact (present_writable B mem2 _ Hpr). }
  split.
  { intros (a & k) x Hb Hx Hk. unfold pj_holds in Hx; cbn [fst snd] in Hx.
    assert (Hne : (a, k) <> (k', sz)).
    { intros E. injection E as -> ->.
      pose proof gLG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ (g_Di_incl _ Hb)) as (_ & Lin & _). cbn [fst snd] in Lin.
      exact (NBk k' sz (or_introl eq_refl) Lin). }
    destruct (pi_lam_disj L2 A2 mem2 md2 Lam2 _ _ _ a k k' sz M2 LG2 (INC _ Hb) Hin Hne); lia. }
  pose proof LG2 as (_ & _ & _ & _ & _ & LF2). rewrite Forall_forall in LF2.
  destruct (LF2 _ Hin) as (_ & Lin2 & _). cbn [fst snd] in Lin2.
  exact (pi_new_apart gL gA gm gmd L2 A2 mem2 md2 k' sz RP RPc Lin2 (NBk k' sz (or_introl eq_refl))).
Qed.

Lemma g_arm_f1 : forall L2 A2 regs2 mem2 md2 R',
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 -> rd_cells B mem2 ->
  ledger B L2 A2 mem2 gLam (Z.max peak0 (lsum Lam0 + hpeak gtr)) (cnt0 + Z.of_nat (calls gtr) + 1) (2 ^ 64 - 1) ->
  rf_ok RF A2 (rf_run RF b0 gtr) ->
  Z.of_nat gn = Z.of_nat gcap -> cnt0 + Z.of_nat (calls gtr) = fail0 ->
  pj_hdr segs mem2 v (5 + pis_oz o) gnum 0 gkids gkeys (Z.of_nat gn) (Z.of_nat gcap) ->
  pis_moved segs gm mem2 gkids gkids (56 * Z.of_nat gcap) ->
  (5 + pis_oz o = 6 -> pis_moved segs gm mem2 gkeys gkeys (8 * Z.of_nat gcap)) ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst gfx R' (getr regs0 1) mem2 (seg_rom segs)) md2).
Proof.
  intros L2 A2 regs2 mem2 md2 R' RP2 RD2 LG2 RS2 Hnc Hcf Hh2 Hmk Hmy RPF R10F.
  assert (Enc : gn = gcap) by lia.
  destruct (g_post_common L2 A2 regs2 mem2 md2 RP2) as (RPc & FR2 & PIN2 & AUX2 & _).
  pose proof gGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP2 as (M2 & _).
  assert (G1 : grow o gn gcap (skipn (calls gtr) pi_ok) =
               (None, [EFail (56 * pi_c2 gcap)%nat], skipn (S (calls gtr)) pi_ok)).
  { rewrite pi_grow_val, Enc, Nat.ltb_irrefl, (proj2 (Z.eqb_eq _ _) Hcf). reflexivity. }
  pose proof (pi_turn_none gtr gn gcap gacc _ _ _ G1 gEXT) as JI.
  apply (pi_exit gfx L2 A2 mem2 md2 gLam (Z.max peak0 (lsum Lam0 + hpeak gtr)) (cnt0 + Z.of_nat (calls gtr) + 1)
    (2 ^ 64 - 1) (gtr ++ [EFail (56 * pi_c2 gcap)%nat]) gD R' None (skipn (S (calls gtr)) pi_ok) FZ FK RPc RD2 LG2 PERM).
  - rewrite pi_lsz_app. exact HP.
  - rewrite pi_nlive_app. cbn [nlive nlive_ev]. lia.
  - exact NB.
  - rewrite hpeak_app. cbn [hpeak held_ev]. pose proof (pi_hpeak_held gtr). lia.
  - rewrite rf_run_app. exact RS2.
  - rewrite calls_app. cbn [calls is_call]. lia.
  - rewrite calls_app. cbn [calls is_call]. split; intros H; [reflexivity | exfalso; lia].
  - exact RPF.
  - exact JI.
  - split; [exact R10F|]. split; [exact (g_after mem2 gP PIN2)|].
    rewrite gED.
    assert (PO' : pis_open segs gm (lin gLam) v o gnum gkids gkeys (Z.of_nat gcap)
                    (Z.of_nat (length (map snd (rev gacc)))) (map snd (rev gacc)) (map fst (rev gacc)) gDi)
      by (rewrite g_ts; exact gPO).
    apply (pis_exit_grow_kept segs gm mem2 (lin gLam) v o gnum gkids gkeys (Z.of_nat gcap) _ _ gDi d PO' gHD gDEP).
    + rewrite g_ts. exact Hh2.
    + exact Hmk.
    + intros Eo. apply Hmy. rewrite Eo. reflexivity.
    + intros i Hi _. rewrite g_ts in Hi. assert (E0 : Z.of_nat gcap <> 0) by lia.
      pose proof (ledger_block_present B API L2 A2 mem2 md2 gLam _ _ _ gkids (56 * Z.of_nat gcap) i M2 LG2 (g_kids_in E0)
        ltac:(lia)) as Hpr.
      exact (present_writable B mem2 _ Hpr).
    + exact (g_Di_same L2 A2 regs2 mem2 md2 gLam _ _ _ RP2 LG2 g_Di_incl).
Qed.

Lemma g_arm_f2 : forall L2 A2 regs2 mem2 md2 Lam2 k' Lr R',
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 -> rd_cells B mem2 ->
  ledger B L2 A2 mem2 Lam2 (Z.max (Z.max peak0 (lsum Lam0 + hpeak gtr)) (lsum Lam2)) (cnt0 + Z.of_nat (calls gtr) + 2)
    (2 ^ 64 - 1) ->
  rf_ok RF A2 (rf_grow RF (rf_run RF b0 gtr) (56 * Z.of_nat gcap) (56 * cap2 (Z.of_nat gcap))) ->
  Z.of_nat gn = Z.of_nat gcap -> cnt0 + Z.of_nat (calls gtr) <> fail0 -> 5 + pis_oz o = 6 ->
  cnt0 + Z.of_nat (calls gtr) + 1 = fail0 ->
  k' mod 16 = 0 -> new_blks gL gA [(k', 56 * cap2 (Z.of_nat gcap))] ->
  Permutation gLam (kids_blk gkids (Z.of_nat gcap) ++ Lr) ->
  Permutation Lam2 ((k', 56 * cap2 (Z.of_nat gcap)) :: Lr) ->
  pis_moved segs gm mem2 gkids k' (56 * Z.of_nat gcap) ->
  pj_hdr segs mem2 v (5 + pis_oz o) gnum 0 k' gkeys (Z.of_nat gn) (Z.of_nat gcap) ->
  pis_moved segs gm mem2 gkeys gkeys (8 * Z.of_nat gcap) ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst gfx R' (getr regs0 1) mem2 (seg_rom segs)) md2).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 k' Lr R' RP2 RD2 LG2 RS2 Hnc Hcf Ety Hcf1 Hk16 NBk HPk HPL2 Hmk Hh2 Hmy RPF R10F.
  assert (Enc : gn = gcap) by lia.
  assert (Eo : o = true) by (destruct o; [reflexivity | cbn in Ety; lia]).
  destruct (g_post_common L2 A2 regs2 mem2 md2 RP2) as (RPc & FR2 & PIN2 & AUX2 & _).
  pose proof gGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP2 as (M2 & _).
  pose proof (pi_cap2_gt (Z.of_nat gcap) ltac:(lia)) as C2.
  set (tg := [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat; EFail (8 * pi_c2 gcap)%nat]).
  assert (G1 : grow o gn gcap (skipn (calls gtr) pi_ok) = (None, tg, skipn (S (S (calls gtr))) pi_ok)).
  { rewrite pi_grow_val, Enc, Nat.ltb_irrefl, (proj2 (Z.eqb_neq _ _) Hcf), Eo, (proj2 (Z.eqb_eq _ _) Hcf1).
    reflexivity. }
  pose proof (pi_turn_none gtr gn gcap gacc _ _ _ G1 gEXT) as JI.
  rewrite gED in PERM, HP, NL. unfold pis_slots in PERM, HP, NL. rewrite Ety in PERM, HP, NL.
  assert (HLr : Permutation Lr (keys_blk 6 gkeys (Z.of_nat gcap) ++ gDi ++ Lam0)).
  { apply (Permutation_app_inv_l (kids_blk gkids (Z.of_nat gcap))).
    rewrite <- !app_assoc in PERM. exact (Permutation_trans (Permutation_sym HPk) PERM). }
  set (D' := (k', 56 * cap2 (Z.of_nat gcap)) :: keys_blk 6 gkeys (Z.of_nat gcap) ++ gDi).
  assert (PL2 : Permutation Lam2 (D' ++ Lam0)).
  { eapply Permutation_trans; [exact HPL2|]. unfold D'. cbn [app]. apply perm_skip. rewrite <- app_assoc. exact HLr. }
  assert (INC : incl gDi Lam2).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPL2)). right.
    apply (Permutation_in _ (Permutation_sym HLr)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (Hk2 : In (k', 56 * cap2 (Z.of_nat gcap)) Lam2) by (apply (Permutation_in _ (Permutation_sym HPL2)); left; reflexivity).
  destruct (g_newblk L2 A2 regs2 mem2 md2 Lam2 _ _ _ k' _ RP2 LG2 Hk2 NBk INC ltac:(lia))
    as (Kb0 & Kb1 & KW & KAp & KAv).
  pose proof (lsz_counts _ _ HP NL) as HELD.
  rewrite !pi_lsum_app, pi_lsum_kids, pi_lsum_keys in HELD by lia.
  apply (pi_exit gfx L2 A2 mem2 md2 Lam2 (Z.max (Z.max peak0 (lsum Lam0 + hpeak gtr)) (lsum Lam2))
    (cnt0 + Z.of_nat (calls gtr) + 2) (2 ^ 64 - 1) (gtr ++ tg) D' R' None (skipn (S (S (calls gtr))) pi_ok) FZ FK RPc RD2 LG2
    PL2).
  - rewrite pi_lsz_app.
    replace (fold_left lsz_ev tg (lsz gtr)) with (lsz_ev (lsz gtr) (EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat))
      by reflexivity.
    unfold D'. cbn [map snd]. rewrite map_app.
    replace (56 * cap2 (Z.of_nat gcap)) with (Z.of_nat (56 * pi_c2 gcap)) by (rewrite Nat2Z.inj_mul, pi_cap2; reflexivity).
    apply (pi_lsz_blk _ _ gkids). rewrite <- app_assoc, !map_app in HP. exact HP.
  - unfold D', tg. rewrite pi_nlive_app. cbn [length nlive]. rewrite length_app, Nat2Z.inj_succ, Nat2Z.inj_add.
    rewrite !length_app, !Nat2Z.inj_add in NL.
    pose proof (pi_nl_kids gkids gcap (56 * pi_c2 gcap)) as N1. cbn [nlive_ev] in N1 |- *. lia.
  - intros a k Hin. unfold D' in Hin. destruct Hin as [E|Hin].
    + injection E as <- <-. exact (pi_new_keep gL gA gm gmd _ RP NBk _ _ (or_introl eq_refl)).
    + apply NB. rewrite gED. unfold pis_slots. rewrite Ety. apply in_or_app. apply in_app_or in Hin.
      destruct Hin as [Hin|Hin]; [left; apply in_or_app; right; exact Hin | right; exact Hin].
  - unfold tg. rewrite hpeak_app. cbn [hpeak held_ev]. rewrite (pi_lsum_perm _ _ PL2), pi_lsum_app. unfold D'. cbn [lsum].
    rewrite pi_lsum_app, pi_lsum_keys by lia. rewrite !Nat2Z.inj_mul, pi_cap2. lia.
  - rewrite rf_run_app.
    replace (rf_run RF (rf_run RF b0 gtr) tg)
      with (rf_grow RF (rf_run RF b0 gtr) (Z.of_nat (56 * gcap)) (Z.of_nat (56 * pi_c2 gcap))) by reflexivity.
    rewrite !Nat2Z.inj_mul, pi_cap2. exact RS2.
  - unfold tg. rewrite calls_app. cbn [calls is_call]. lia.
  - unfold tg. rewrite calls_app. cbn [calls is_call]. split; intros H; [reflexivity | exfalso; lia].
  - exact RPF.
  - exact JI.
  - split; [exact R10F|]. split; [exact (g_after mem2 gP PIN2)|].
    assert (PO' : pis_open segs gm (lin gLam) v true gnum gkids gkeys (Z.of_nat gcap)
                    (Z.of_nat (length (map snd (rev gacc)))) (map snd (rev gacc)) (map fst (rev gacc)) gDi)
      by (rewrite g_ts, <- Eo; exact gPO).
    pose proof LG2 as (_ & _ & _ & _ & HN2 & _).
    apply (pis_exit_grow_half segs gm mem2 gLam Lam2 Lr v gnum gkids gkeys (Z.of_nat gcap) _ _ gDi k' d PO' gHD gDEP
      HPk HPL2 HN2 Hmk Hmy).
    + rewrite g_ts. rewrite Ety in Hh2. exact Hh2.
    + lia.
    + lia.
    + rewrite g_ts. pose proof rk_ceil. lia.
    + rewrite g_ts. exact KW.
    + exact (g_Di_same L2 A2 regs2 mem2 md2 Lam2 _ _ _ RP2 LG2 INC).
    + rewrite g_ts. exact KAp.
    + exact KAv.
Qed.

Lemma g_arm_arr : forall L2 A2 regs2 mem2 md2 Lam2 k' Lr R',
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 -> rd_cells B mem2 ->
  ledger B L2 A2 mem2 Lam2 (Z.max (Z.max peak0 (lsum Lam0 + hpeak gtr)) (lsum Lam2)) (cnt0 + Z.of_nat (calls gtr) + 1)
    fail0 ->
  rf_ok RF A2 (rf_grow RF (rf_run RF b0 gtr) (56 * Z.of_nat gcap) (56 * cap2 (Z.of_nat gcap))) ->
  Z.of_nat gn = Z.of_nat gcap -> cnt0 + Z.of_nat (calls gtr) <> fail0 -> 5 + pis_oz o <> 6 ->
  k' mod 16 = 0 -> new_blks gL gA [(k', 56 * cap2 (Z.of_nat gcap))] ->
  Permutation gLam (kids_blk gkids (Z.of_nat gcap) ++ Lr) ->
  Permutation Lam2 ((k', 56 * cap2 (Z.of_nat gcap)) :: Lr) ->
  pis_moved segs gm mem2 gkids k' (56 * Z.of_nat gcap) ->
  pj_hdr segs mem2 v (5 + pis_oz o) gnum 0 k' gkeys (Z.of_nat gn) (cap2 (Z.of_nat gcap)) ->
  pj_slots_at (lin Lam2) (5 + pis_oz o) k' gkeys (Z.of_nat gn) (cap2 (Z.of_nat gcap)) ->
  pi_cs R' ->
  pi_inv (length (rest_at tb text gP)) (mkCfg (@mkst gfx R' (Z_to_bv 64 0x150d8) mem2 (seg_rom segs)) md2).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 k' Lr R' RP2 RD2 LG2 RS2 Hnc Hcf Hty Hk16 NBk HPk HPL2 Hmv Hh2 Hs2 CS'.
  assert (Enc : gn = gcap) by lia.
  assert (Eo : o = false) by (destruct o; [cbn in Hty; lia | reflexivity]).
  pose proof gGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP2 as (M2 & _).
  pose proof (pi_cap2_gt (Z.of_nat gcap) ltac:(lia)) as C2.
  pose proof gPO as PO. rewrite Eo in PO.
  assert (EK : keys_blk (5 + pis_oz false) gkeys (Z.of_nat gcap) = []).
  { unfold keys_blk. change (5 + pis_oz false =? 6) with false. cbn [negb]. destruct (Z.of_nat gcap =? 0); reflexivity. }
  rewrite gED in PERM, HP, NL. unfold pis_slots in PERM, HP, NL. rewrite Eo, EK, app_nil_r in PERM, HP, NL.
  assert (HLr : Permutation Lr (gDi ++ Lam0)).
  { apply (Permutation_app_inv_l (kids_blk gkids (Z.of_nat gcap))).
    rewrite <- app_assoc in PERM. exact (Permutation_trans (Permutation_sym HPk) PERM). }
  assert (INC : incl gDi Lam2).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPL2)). right.
    apply (Permutation_in _ (Permutation_sym HLr)). apply in_or_app. left. exact Hb. }
  assert (Hk2 : In (k', 56 * cap2 (Z.of_nat gcap)) Lam2)
    by (apply (Permutation_in _ (Permutation_sym HPL2)); left; reflexivity).
  destruct (g_newblk L2 A2 regs2 mem2 md2 Lam2 _ _ _ k' _ RP2 LG2 Hk2 NBk INC ltac:(lia))
    as (Kb0 & Kb1 & KW & KAp & KAv).
  pose proof (lsz_counts _ _ HP NL) as HELD. rewrite pi_lsum_app, pi_lsum_kids in HELD by lia.
  assert (ED' : pis_slots o k' gkeys (Z.of_nat (pi_c2 gcap)) ++ gDi = (k', 56 * cap2 (Z.of_nat gcap)) :: gDi).
  { rewrite Eo, pi_cap2. unfold pis_slots, kids_blk, keys_blk.
    rewrite (proj2 (Z.eqb_neq (cap2 (Z.of_nat gcap)) 0)) by lia. reflexivity. }
  assert (G1 : grow o gn gcap (skipn (calls gtr) pi_ok) =
    (Some (pi_c2 gcap), [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat],
     skipn (calls gtr + calls [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat]) pi_ok)).
  { rewrite pi_grow_val, Enc, Nat.ltb_irrefl, (proj2 (Z.eqb_neq _ _) Hcf), Eo. cbn [calls is_call].
    rewrite Nat.add_1_r. reflexivity. }
  assert (G0 : grow o gn gcap [] = (Some (pi_c2 gcap), [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat], [])).
  { rewrite pi_grow_nil, Enc, Nat.ltb_irrefl, Eo. reflexivity. }
  apply (g_inv L2 A2 regs2 mem2 md2 Lam2 R' _ (pi_c2 gcap) k' gkeys RP2 RD2 G1 G0).
  - assert (EPK : Z.max peak0 (lsum Lam0 + hpeak (gtr ++ [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat])) =
                  Z.max (Z.max peak0 (lsum Lam0 + hpeak gtr)) (lsum Lam2)).
    { rewrite hpeak_app. cbn [hpeak held_ev]. rewrite (pi_lsum_perm _ _ HPL2). cbn [lsum].
      rewrite (pi_lsum_perm _ _ HLr), pi_lsum_app. rewrite !Nat2Z.inj_mul, pi_cap2. lia. }
    rewrite EPK, calls_app. cbn [calls is_call]. rewrite Nat2Z.inj_add, Z.add_assoc. exact LG2.
  - rewrite calls_app. cbn [calls is_call]. lia.
  - rewrite rf_run_app.
    replace (rf_run RF (rf_run RF b0 gtr) [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat])
      with (rf_grow RF (rf_run RF b0 gtr) (Z.of_nat (56 * gcap)) (Z.of_nat (56 * pi_c2 gcap))) by reflexivity.
    rewrite !Nat2Z.inj_mul, pi_cap2. exact RS2.
  - rewrite ED'. eapply Permutation_trans; [exact HPL2|]. cbn [app]. apply perm_skip. exact HLr.
  - rewrite ED', pi_lsz_app. cbn [fold_left map snd].
    replace (56 * cap2 (Z.of_nat gcap)) with (Z.of_nat (56 * pi_c2 gcap)) by (rewrite Nat2Z.inj_mul, pi_cap2; reflexivity).
    apply (pi_lsz_blk _ _ gkids). rewrite map_app in HP. exact HP.
  - rewrite ED', pi_nlive_app. cbn [length nlive]. rewrite length_app, Nat2Z.inj_add in NL.
    pose proof (pi_nl_kids gkids gcap (56 * pi_c2 gcap)) as N1. cbn [nlive_ev] in N1 |- *. lia.
  - rewrite ED'. intros a k [E|Hin].
    + injection E as <- <-. exact (pi_new_keep gL gA gm gmd _ RP NBk _ _ (or_introl eq_refl)).
    + apply NB. rewrite gED. apply in_or_app. right. exact Hin.
  - rewrite pi_cap2, Eo. pose proof LG2 as (_ & _ & _ & _ & HN2 & _).
    apply (pis_grow_arr segs gm mem2 gLam Lam2 Lr v gnum gkids gkeys (Z.of_nat gcap) (Z.of_nat gn) _ _ gDi k' PO HPk HPL2
      HN2 Hmv).
    + rewrite Eo in Hh2. exact Hh2.
    + rewrite Eo in Hs2. exact Hs2.
    + rewrite g_ts. lia.
    + lia.
    + lia.
    + rewrite g_ts. pose proof rk_ceil. lia.
    + rewrite g_ts. exact KW.
    + exact (g_Di_same L2 A2 regs2 mem2 md2 Lam2 _ _ _ RP2 LG2 INC).
    + rewrite g_ts. exact KAp.
    + exact KAv.
  - exact CS'.
Qed.

Lemma g_arm_obj : forall L2 A2 regs2 mem2 md2 Lam2 k' y' Lr R',
  rpost B API GROW_K gL gA gR gm gmd gWr gGo L2 A2 regs2 mem2 md2 -> rd_cells B mem2 ->
  ledger B L2 A2 mem2 Lam2
    (Z.max (Z.max peak0 (lsum Lam0 + hpeak gtr))
       (Z.max (lsum gLam + 56 * (cap2 (Z.of_nat gcap) - Z.of_nat gcap)) (lsum Lam2)))
    (cnt0 + Z.of_nat (calls gtr) + 2) fail0 ->
  rf_ok RF A2 (rf_grow RF (rf_grow RF (rf_run RF b0 gtr) (56 * Z.of_nat gcap) (56 * cap2 (Z.of_nat gcap)))
    (8 * Z.of_nat gcap) (8 * cap2 (Z.of_nat gcap))) ->
  Z.of_nat gn = Z.of_nat gcap -> cnt0 + Z.of_nat (calls gtr) <> fail0 -> 5 + pis_oz o = 6 ->
  cnt0 + Z.of_nat (calls gtr) + 1 <> fail0 ->
  k' mod 16 = 0 -> y' mod 16 = 0 ->
  new_blks gL gA [(y', 8 * cap2 (Z.of_nat gcap)); (k', 56 * cap2 (Z.of_nat gcap))] ->
  Permutation gLam (kids_blk gkids (Z.of_nat gcap) ++ keys_blk (5 + pis_oz o) gkeys (Z.of_nat gcap) ++ Lr) ->
  Permutation Lam2 ((y', 8 * cap2 (Z.of_nat gcap)) :: (k', 56 * cap2 (Z.of_nat gcap)) :: Lr) ->
  pis_moved segs gm mem2 gkids k' (56 * Z.of_nat gcap) -> pis_moved segs gm mem2 gkeys y' (8 * Z.of_nat gcap) ->
  pj_hdr segs mem2 v (5 + pis_oz o) gnum 0 k' y' (Z.of_nat gn) (cap2 (Z.of_nat gcap)) ->
  pj_slots_at (lin Lam2) (5 + pis_oz o) k' y' (Z.of_nat gn) (cap2 (Z.of_nat gcap)) ->
  pi_cs R' ->
  pi_inv (length (rest_at tb text gP)) (mkCfg (@mkst gfx R' (Z_to_bv 64 0x150d8) mem2 (seg_rom segs)) md2).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 k' y' Lr R' RP2 RD2 LG2 RS2 Hnc Hcf Ety Hcf1 Hk16 Hy16 NBk HPk HPL2 Hmk Hmy Hh2 Hs2
    CS'.
  assert (Enc : gn = gcap) by lia.
  assert (Eo : o = true) by (destruct o; [reflexivity | cbn in Ety; lia]).
  pose proof gGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP2 as (M2 & _).
  pose proof (pi_cap2_gt (Z.of_nat gcap) ltac:(lia)) as C2.
  pose proof gPO as PO. rewrite Eo in PO.
  rewrite gED in PERM, HP, NL. unfold pis_slots in PERM, HP, NL. rewrite Ety in PERM, HP, NL, HPk.
  pose proof PERM as PERM0.
  assert (HLr : Permutation Lr (gDi ++ Lam0)).
  { apply (Permutation_app_inv_l (keys_blk 6 gkeys (Z.of_nat gcap))).
    apply (Permutation_app_inv_l (kids_blk gkids (Z.of_nat gcap))).
    rewrite <- !app_assoc in PERM. exact (Permutation_trans (Permutation_sym HPk) PERM). }
  assert (INC : incl gDi Lam2).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPL2)). right. right.
    apply (Permutation_in _ (Permutation_sym HLr)). apply in_or_app. left. exact Hb. }
  assert (Hk2 : In (k', 56 * cap2 (Z.of_nat gcap)) Lam2)
    by (apply (Permutation_in _ (Permutation_sym HPL2)); right; left; reflexivity).
  assert (NBk' : new_blks gL gA [(k', 56 * cap2 (Z.of_nat gcap))])
    by (intros a k Hin; apply NBk; destruct Hin as [E|[]]; right; left; exact E).
  destruct (g_newblk L2 A2 regs2 mem2 md2 Lam2 _ _ _ k' _ RP2 LG2 Hk2 NBk' INC ltac:(lia))
    as (Kb0 & Kb1 & KW & KAp & KAv).
  assert (Hy2 : In (y', 8 * cap2 (Z.of_nat gcap)) Lam2)
    by (apply (Permutation_in _ (Permutation_sym HPL2)); left; reflexivity).
  destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ y' _ M2 LG2 Hy2) as (Yb0 & Yb1 & _).
  assert (Hav2 : pj_apart [(k', 56 * cap2 (Z.of_nat gcap)); (y', 8 * cap2 (Z.of_nat gcap))] v).
  { destruct (g_post_common L2 A2 regs2 mem2 md2 RP2) as (RPc & _).
    pose proof LG2 as (_ & _ & _ & _ & _ & LF2). rewrite Forall_forall in LF2.
    destruct (LF2 _ Hy2) as (_ & Lin2 & _). cbn [fst snd] in Lin2.
    pose proof (pi_new_apart gL gA gm gmd L2 A2 mem2 md2 y' _ RP RPc Lin2 (NBk _ _ (or_introl eq_refl))) as KAy.
    intros bb x [E|[E|[]]] Hx; [exact (KAv bb x (or_introl E) Hx) | exact (KAy bb x (or_introl E) Hx)]. }
  pose proof (lsz_counts _ _ HP NL) as HELD.
  rewrite !pi_lsum_app, pi_lsum_kids, pi_lsum_keys in HELD by lia.
  assert (ED' : pis_slots o k' y' (Z.of_nat (pi_c2 gcap)) ++ gDi =
                (k', 56 * cap2 (Z.of_nat gcap)) :: (y', 8 * cap2 (Z.of_nat gcap)) :: gDi).
  { rewrite Eo, pi_cap2. unfold pis_slots, kids_blk, keys_blk.
    rewrite (proj2 (Z.eqb_neq (cap2 (Z.of_nat gcap)) 0)) by lia. reflexivity. }
  set (tg := [EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat; EGrow (8 * gcap)%nat (8 * pi_c2 gcap)%nat]).
  assert (G1 : grow o gn gcap (skipn (calls gtr) pi_ok) = (Some (pi_c2 gcap), tg, skipn (calls gtr + calls tg) pi_ok)).
  { rewrite pi_grow_val, Enc, Nat.ltb_irrefl, (proj2 (Z.eqb_neq _ _) Hcf), Eo, (proj2 (Z.eqb_neq _ _) Hcf1).
    unfold tg. cbn [calls is_call]. replace (calls gtr + 2)%nat with (S (S (calls gtr))) by lia. reflexivity. }
  assert (G0 : grow o gn gcap [] = (Some (pi_c2 gcap), tg, [])).
  { rewrite pi_grow_nil, Enc, Nat.ltb_irrefl, Eo. reflexivity. }
  apply (g_inv L2 A2 regs2 mem2 md2 Lam2 R' tg (pi_c2 gcap) k' y' RP2 RD2 G1 G0).
  - assert (EPK : Z.max peak0 (lsum Lam0 + hpeak (gtr ++ tg)) =
                  Z.max (Z.max peak0 (lsum Lam0 + hpeak gtr))
                    (Z.max (lsum gLam + 56 * (cap2 (Z.of_nat gcap) - Z.of_nat gcap)) (lsum Lam2))).
    { unfold tg. rewrite hpeak_app. cbn [hpeak held_ev]. rewrite (pi_lsum_perm _ _ HPL2), (pi_lsum_perm _ _ PERM0).
      cbn [lsum]. rewrite (pi_lsum_perm _ _ HLr), !pi_lsum_app, pi_lsum_kids, pi_lsum_keys by lia.
      rewrite !Nat2Z.inj_mul, pi_cap2. lia. }
    rewrite EPK. unfold tg. rewrite calls_app. cbn [calls is_call]. rewrite Nat2Z.inj_add, Z.add_assoc. exact LG2.
  - unfold tg. rewrite calls_app. cbn [calls is_call]. lia.
  - rewrite rf_run_app.
    replace (rf_run RF (rf_run RF b0 gtr) tg)
      with (rf_grow RF (rf_grow RF (rf_run RF b0 gtr) (Z.of_nat (56 * gcap)) (Z.of_nat (56 * pi_c2 gcap)))
              (Z.of_nat (8 * gcap)) (Z.of_nat (8 * pi_c2 gcap))) by reflexivity.
    rewrite !Nat2Z.inj_mul, pi_cap2. exact RS2.
  - rewrite ED'. eapply Permutation_trans; [exact HPL2|]. cbn [app].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_skip. exact HLr.
  - rewrite ED', pi_lsz_app.
    replace (fold_left lsz_ev tg (lsz gtr))
      with (lsz_ev (lsz_ev (lsz gtr) (EGrow (56 * gcap)%nat (56 * pi_c2 gcap)%nat)) (EGrow (8 * gcap)%nat (8 * pi_c2 gcap)%nat))
      by reflexivity.
    cbn [map snd].
    replace (56 * cap2 (Z.of_nat gcap)) with (Z.of_nat (56 * pi_c2 gcap)) by (rewrite Nat2Z.inj_mul, pi_cap2; reflexivity).
    replace (8 * cap2 (Z.of_nat gcap)) with (Z.of_nat (8 * pi_c2 gcap)) by (rewrite Nat2Z.inj_mul, pi_cap2; reflexivity).
    eapply Permutation_trans; [apply perm_swap|].
    apply (pi_lsz_kblk _ _ gkeys gcap).
    change (map snd (keys_blk 6 gkeys (Z.of_nat gcap)) ++ Z.of_nat (56 * pi_c2 gcap) :: map snd gDi)
      with (map snd (keys_blk 6 gkeys (Z.of_nat gcap)) ++ [Z.of_nat (56 * pi_c2 gcap)] ++ map snd gDi).
    eapply Permutation_trans; [apply Permutation_app_swap_app|]. cbn [app].
    apply (pi_lsz_blk _ _ gkids gcap).
    rewrite <- !app_assoc, !map_app in HP. exact HP.
  - rewrite ED', pi_nlive_app. unfold tg. cbn [length nlive]. rewrite !length_app, !Nat2Z.inj_add in NL.
    pose proof (pi_nl_kids gkids gcap (56 * pi_c2 gcap)) as N1. pose proof (pi_nl_keys gkeys gcap (8 * pi_c2 gcap)) as N2.
    cbn [nlive_ev] in N1, N2 |- *. lia.
  - rewrite ED'. intros a k [E|[E|Hin]].
    + injection E as <- <-. exact (pi_new_keep gL gA gm gmd _ RP NBk _ _ (or_intror (or_introl eq_refl))).
    + injection E as <- <-. exact (pi_new_keep gL gA gm gmd _ RP NBk _ _ (or_introl eq_refl)).
    + apply NB. rewrite gED. apply in_or_app. right. exact Hin.
  - rewrite pi_cap2, Eo. pose proof LG2 as (_ & _ & _ & _ & HN2 & _).
    apply (pis_grow_obj segs gm mem2 gLam Lam2 Lr v gnum gkids gkeys (Z.of_nat gcap) (Z.of_nat gn) _ _ gDi k' y' PO HPk
      HPL2 HN2 Hmk Hmy).
    + rewrite Ety in Hh2. exact Hh2.
    + rewrite Ety in Hs2. exact Hs2.
    + rewrite g_ts. lia.
    + lia.
    + lia.
    + rewrite g_ts. pose proof rk_ceil. lia.
    + rewrite g_ts. exact KW.
    + lia.
    + rewrite g_ts. pose proof rk_ceil. lia.
    + exact (g_Di_same L2 A2 regs2 mem2 md2 Lam2 _ _ _ RP2 LG2 INC).
    + rewrite g_ts. exact KAp.
    + exact Hav2.
  - exact CS'.
Qed.

Lemma pi_sep_core : forall w, (length (rest_at tb text gP) < w)%nat ->
  SR segs (mkCfg (@mkst gfx gR (Z_to_bv 64 0x147e8) gm (seg_rom segs)) gmd) (pi_next w).
Proof using All.
  intros w HW.
  pose proof (pi_K_bounds gHD) as (KG & _ & _ & _ & KG0 & _).
  pose proof gGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof gPO as (HN & HA & Hh & Hs & _).
  assert (ENVg : reader_env (fx := gfx) B API GROW_K gL gA gR gm gmd).
  { apply (pi_env0 gfx gL gA gm gmd gLam gtr gD gR GROW_K gGL gCS); [|exact KG|exact KG0].
    destruct gG1 as [(E & _)|E]; rewrite E; apply YK0s.ret_ok_even; vm_compute; reflexivity. }
  assert (RPv : rplace B gL gA gLam gR gm v) by exact (pi_rplace gfx gL gA gm gmd gLam gtr gD gR _ _ _ gGL gLG g_SP).
  assert (HAP : pj_apart (kids_blk gkids (Z.of_nat gcap) ++ keys_blk (5 + pis_oz o) gkeys (Z.of_nat gcap)) v)
    by (intros b x Hb; apply (HA b x); apply in_or_app; left; exact Hb).
  assert (DJg : Frame.disjoint_from [(v, v + 56)] (spZ gR - GROW_K) GROW_K).
  { pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ |- *. rewrite g_SP. unfold pi_f. lia. }
  assert (CNTg : cnt0 + Z.of_nat (calls gtr) + 2 < 2 ^ 64 - 1)
    by (pose proof CNT; pose proof gCB as CB; unfold pi_x in CB; lia).
  assert (ROOMg : Z.of_nat gn = Z.of_nat gcap ->
      rf_room RF (rf_run RF b0 gtr) (56 * cap2 (Z.of_nat gcap) + 16) /\ 56 * cap2 (Z.of_nat gcap) + 16 <= 2 ^ 28 /\
      (5 + pis_oz o = 6 -> rf_room RF (rf_grow RF (rf_run RF b0 gtr) (56 * Z.of_nat gcap) (56 * cap2 (Z.of_nat gcap)))
                              (8 * cap2 (Z.of_nat gcap) + 16)))
    by (intros E; apply Nat2Z.inj in E; exact (pi_room_call _ gn gcap gacc _ E gROOM)).
  eapply SR_bind.
  { change (Z_to_bv 64 0x147e8) with (Z_to_bv 64 GROW).
    exact (GRC gfx gL gA gR gm gmd gLam _ _ _ _ v (5 + pis_oz o) gnum 0 gkids gkeys (Z.of_nat gn) (Z.of_nat gcap)
      ENVg gLG RS gG10 VNZ Hh Hs HAP RPv DJg CNTg ROOMg). }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & b2 & res & -> & RP2 & RD2 & R102 & LG2 & RS2 &
    ARMS).
  destruct (g_post_common L2 A2 regs2 mem2 md2 RP2) as (RPc & FR2 & PIN2 & AUX2 & CS2).
  pose proof RP2 as (M2 & _ & _ & _ & _ & _ & _ & _ & _ & RPr2 & _).
  destruct (mr_model B _ (aa_laws API) L2 A2 mem2 md2 M2) as (Hh2 & Hl2 & _).
  assert (TAIL : forall (Pc : config -> Prop),
      (bv_unsigned (getr regs2 10) = 0 -> forall R', pi_cs R' ->
         Pc (mkCfg (@mkst gfx R' (Z_to_bv 64 0x150d8) mem2 (seg_rom segs)) md2)) ->
      (bv_unsigned (getr regs2 10) <> 0 -> forall R', regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
         Pc (mkCfg (@mkst gfx R' (getr regs0 1) mem2 (seg_rom segs)) md2)) ->
      SR segs (mkCfg (@mkst gfx regs2 (getr gR 1) mem2 (seg_rom segs)) md2) Pc).
  { intros Pc K0 K1. destruct gG1 as [(E & CSg) | E]; rewrite E.
    - exact (pi_g2_tail gfx regs2 mem2 md2 Pc (pi_cs_rp gR regs2 CSg RPr2) FR2 Hh2 Hl2 K0 K1).
    - exact (pi_g1_tail gfx regs2 mem2 md2 Pc CS2 FR2 Hh2 Hl2 K0 K1). }
  apply TAIL.
  - intros H0 R' CS'.
    assert (Hr : res mod 2 ^ 64 = 0) by (rewrite <- (MState.unsigned_lit_wrap res), <- R102; exact H0).
    destruct ARMS as [A1 | [A2' | [A3 | [A4 | A5]]]].
    + destruct A1 as (Hlt & _ & -> & -> & -> & -> & -> & -> & -> & Hh2').
      right. exists (length (rest_at tb text gP)). split; [exact HW|].
      exact (g_arm_lt regs2 mem2 md2 R' RP2 RD2 LG2 RS2 Hlt Hh2' CS').
    + destruct A2' as (_ & _ & Er & _). subst res. exfalso. lia.
    + destruct A3 as (Hnc & Hcf & Hty & _ & k' & Lr & _ & Hk16 & NBk & HPk & HPL2 & -> & -> & -> & -> & Hmv & Hh2' & Hs2').
      right. exists (length (rest_at tb text gP)). split; [exact HW|].
      exact (g_arm_arr L2 A2 regs2 mem2 md2 Lam2 k' Lr R' RP2 RD2 LG2 RS2 Hnc Hcf Hty Hk16 NBk HPk HPL2 Hmv Hh2' Hs2' CS').
    + destruct A4 as (_ & _ & _ & _ & Er & _). subst res. exfalso. lia.
    + destruct A5 as (Hnc & Hcf & Hty & Hcf1 & _ & k' & y' & Lr & _ & Hk16 & _ & Hy16 & NBk & HPk & HPL2 & -> & -> & -> &
        -> & Hmk & Hmy & Hh2' & Hs2').
      right. exists (length (rest_at tb text gP)). split; [exact HW|].
      exact (g_arm_obj L2 A2 regs2 mem2 md2 Lam2 k' y' Lr R' RP2 RD2 LG2 RS2 Hnc Hcf Hty Hcf1 Hk16 Hy16 NBk HPk HPL2 Hmk Hmy
        Hh2' Hs2' CS').
  - intros H0 R' RPF R10F.
    assert (Hr : res mod 2 ^ 64 <> 0) by (rewrite <- (MState.unsigned_lit_wrap res), <- R102; exact H0).
    destruct ARMS as [A1 | [A2' | [A3 | [A4 | A5]]]].
    + destruct A1 as (_ & Er & _). subst res. exfalso. apply Hr. reflexivity.
    + destruct A2' as (Hnc & Hcf & _ & -> & -> & -> & -> & -> & Hh2' & Hmk & Hmy). left.
      exact (g_arm_f1 L2 A2 regs2 mem2 md2 R' RP2 RD2 LG2 RS2 Hnc Hcf Hh2' Hmk Hmy RPF R10F).
    + destruct A3 as (_ & _ & _ & Er & _). subst res. exfalso. apply Hr. reflexivity.
    + destruct A4 as (Hnc & Hcf & Hty & Hcf1 & _ & k' & Lr & _ & Hk16 & NBk & HPk & HPL2 & -> & -> & -> & -> & Hmk & Hh2' &
        Hmy). left.
      exact (g_arm_f2 L2 A2 regs2 mem2 md2 Lam2 k' Lr R' RP2 RD2 LG2 RS2 Hnc Hcf Hty Hcf1 Hk16 NBk HPk HPL2 Hmk Hh2' Hmy RPF
        R10F).
    + destruct A5 as (_ & _ & _ & _ & Er & _). subst res. exfalso. apply Hr. reflexivity.
Qed.

End Sep.

Lemma pi_sep : forall w c, pi_gc w c -> SR segs c (pi_next w).
Proof.
  intros w c (fxc & R & m & mdc & Lc & Ac & Lamc & tr & D & n & cap & acc & P & num & kids & keys & Di & -> & HD & CS & G1 &
    G10 & GL & LG & NF & PIN & HW & CB & EXT & RMh & LA & INV & ED & PO & DEP).
  exact (pi_sep_core fxc R m mdc Lc Ac Lamc tr D n cap acc P num kids keys Di HD (pi_cs_cs0 R CS) (or_introl (conj G1 CS))
    G10 GL LG NF PIN CB EXT RMh LA INV ED PO DEP w HW).
Qed.

Lemma pi_after_mv : forall m m' lo hi, pj_in_after B m q text len lo hi ->
  (forall x, q <= x < q + 24 -> mbyte segs m' x = mbyte segs m x /\ (writable_at segs m x -> writable_at segs m' x)) ->
  pj_in_after B m' q text len lo hi.
Proof.
  intros m m' lo hi (p' & d' & H1 & H2 & B0 & B8 & B16 & W) HQ.
  pose proof W as (W0 & W1 & W2). exists p', d'. split; [exact H1|]. split; [exact H2|].
  split.
  { apply (pis_bytes_mv segs m m' q q _ B0); [lia | rewrite length_le8; cbn; lia |].
    intros i Hi. rewrite length_le8 in Hi. cbn in Hi. exact (proj1 (HQ (q + i) ltac:(lia))). }
  split.
  { apply (pis_bytes_mv segs m m' (q + 8) (q + 8) _ B8); [lia | rewrite length_le8; cbn; lia |].
    intros i Hi. rewrite length_le8 in Hi. cbn in Hi. exact (proj1 (HQ (q + 8 + i) ltac:(lia))). }
  split.
  { apply (pis_bytes_mv segs m m' (q + 16) (q + 16) _ B16); [lia | rewrite length_le4; cbn; lia |].
    intros i Hi. rewrite length_le4 in Hi. cbn in Hi. exact (proj1 (HQ (q + 16 + i) ltac:(lia))). }
  split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (HQ (q + i) ltac:(lia))). exact (W2 i Hi).
Qed.

Lemma pi_kA3 : forall L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 D2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  Permutation Lam2 (D2 ++ Lam0) -> new_blks L0 A0 D2 -> pi_frm mem2 ->
  (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo mem2) ->
  chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] mem2 m3 ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m3 md2 /\
  rd_cells B m3 /\ ledger B L2 A2 m3 Lam2 peak2 cnt2 fail2 /\ pi_frm m3 /\
  (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo m3) /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (v + 40 <= x < v + 48) -> ~ (q <= x < q + 24) -> pis_same segs mem2 m3 x).
Proof.
  intros L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 D2 RPc RD2 LG2 PL2 NB2 FR2 AUX2 (MU & WM & PR).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof RPL as (_ & _ & PNO). pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof RPc as (M2 & _).
  assert (WM' : wmono segs mem2 m3) by (rewrite pi_seg; exact WM).
  assert (INW : forall x, ~ outside [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] x ->
             v + 40 <= x < v + 48 \/ q <= x < q + 8 \/ q + 16 <= x < q + 20).
  { intros x Ho. cbn [outside] in Ho.
    destruct (Z_lt_le_dec x (v + 40)) as [A1|A1]; destruct (Z_lt_le_dec x (v + 48)) as [A2'|A2'];
    destruct (Z_lt_le_dec x q) as [A3|A3]; destruct (Z_lt_le_dec x (q + 8)) as [A4|A4];
    destruct (Z_lt_le_dec x (q + 16)) as [A5|A5]; destruct (Z_lt_le_dec x (q + 20)) as [A6|A6];
    first [lia | exfalso; apply Ho; repeat split; lia]. }
  assert (OUT : forall x, ~ (v + 40 <= x < v + 48) -> ~ (q <= x < q + 24) ->
             outside [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] x).
  { intros x H1 H2. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (MB : forall x, 0 <= x < 2 ^ 64 -> ~ (v + 40 <= x < v + 48) -> ~ (q <= x < q + 24) -> pis_same segs mem2 m3 x).
  { intros x Hx H1 H2. pose proof (OUT x H1 H2) as Ho.
    split; [exact (MemNorm.mbyte_munch _ _ _ _ x MU Hx Ho) | intros Hw; exact (proj1 (rk_writable_munch _ _ mem2 m3 x MU Hx Ho) Hw)]. }
  assert (NIW : forall x, 0 <= x < 2 ^ 64 -> ~ outside [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] x -> ~ in_img B x).
  { intros x Hx Ho Hi. destruct (INW x Ho) as [Hv|Hq].
    - destruct (PNO (x - v) ltac:(lia)) as (_ & _ & _ & N4). apply N4. replace (v + (x - v)) with x by lia. exact Hi.
    - pose proof (rk_img_bound pi_seg x Hi). lia. }
  split.
  { apply (pi_rp_A L2 A2 mem2 md2 m3 [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] RPc MU WM').
    intros x Hx Ho. split; [exact (NIW x Hx Ho)|]. destruct (INW x Ho) as [Hv|Hq].
    - split; [replace x with (v + (x - v)) by lia; exact (pi_v_noown L2 A2 mem2 md2 RPc (x - v) ltac:(lia))|].
      left. left. lia.
    - split; [intros Ho'; pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M2 Ho'); lia|].
      left. right. left. unfold pj_in_set. lia. }
  split; [exact (pi_rd_munch mem2 m3 _ RD2 MU NIW)|].
  split.
  { apply (rk_ledger_keep L2 A2 mem2 m3 Lam2 peak2 cnt2 fail2 LG2).
    - intros a Ha. pose proof (pi_statics_img a Ha) as Hi. pose proof (rk_img_bound pi_seg a Hi) as Ra.
      refine (proj1 (MB a ltac:(lia) _ _)); [|lia].
      intros Hv. destruct (PNO (a - v) ltac:(lia)) as (_ & _ & _ & N4). apply N4.
      replace (v + (a - v)) with a by lia. exact Hi.
    - intros a k i HIn Hi.
      destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ a k M2 LG2 HIn) as (R1 & R2 & _).
      pose proof LG2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ HIn) as (Lk & _). cbn [fst snd] in Lk.
      pose proof (pi_v_heads L2 A2 mem2 md2 Lam2 D2 _ _ _ RPc LG2 PL2 NB2 a k (a - 16 + i) HIn ltac:(lia)) as NV.
      refine (proj1 (MB (a - 16 + i) ltac:(lia) _ _)); lia. }
  split.
  { unfold pi_frm in FR2 |- *.
    apply (pi_frame_mv mem2 m3 pi_f _ _ _ _ _ _ _ _ _ _ FR2); [|unfold pi_f; lia | unfold pi_f; lia].
    intros x Hx. rewrite <- pi_seg. unfold pi_f in Hx. refine (proj1 (MB x ltac:(lia) _ _)); lia. }
  split.
  { intros HD. apply (rk_auxv_keep (ly_sec L0) pi_lo mem2 m3 (AUX2 HD)).
    - intros i Hi.
      assert (So : owned B L0 A0 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ pi_HM0 So) as Lo.
      refine (proj1 (MB (ms_libc B + 8 + i) ltac:(lia) _ _)); [|lia].
      intros Hv. destruct (PNO (ms_libc B + 8 + i - v) ltac:(lia)) as (N1 & _).
      apply N1. replace (v + (ms_libc B + 8 + i - v)) with (ms_libc B + 8 + i) by lia. exact So.
    - intros a Ha. pose proof pi_vlo as VL. unfold pi_lo in Ha.
      refine (proj1 (MB a ltac:(lia) _ _)); [|lia].
      destruct (Z.leb_spec (spZ regs0) v); lia. }
  exact MB.
Qed.

Lemma pi_apart_new : forall L2 A2 m2 md2 Lam2 peak2 cnt2 fail2 D2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m2 md2 ->
  ledger B L2 A2 m2 Lam2 peak2 cnt2 fail2 -> incl D2 Lam2 -> new_blks L0 A0 D2 -> pj_apart D2 v.
Proof.
  intros L2 A2 m2 md2 Lam2 peak2 cnt2 fail2 D2 RP2 LG2 INC NB (a & k) x Hb Hx.
  pose proof LG2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  destruct (LF _ (INC _ Hb)) as (_ & Lin & _). cbn [fst snd] in Lin.
  exact (pi_new_apart0 L2 A2 m2 md2 a k RP2 Lin (NB a k Hb) (a, k) x (or_introl eq_refl) Hx).
Qed.

Lemma pi_after_of : forall m P, pj_in_ok segs m q text len P (Z.of_nat d + 1) tb ->
  pj_in_after B m q text len (Z.of_nat d + 1) 33.
Proof.
  intros m P (Q0 & Q8 & Q16 & WQ & _ & _ & _ & Tp & _ & _ & _ & Dd).
  exists P, (Z.of_nat d + 1). split; [lia|]. split; [lia|].
  split; [exact Q0|]. split; [exact Q8|]. split; [exact Q16 | exact WQ].
Qed.

Lemma pi_text_new : forall Lc Ac mc mdc a k,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 mc mdc ->
  In (a, k) (blocks Lc Ac) -> ~ In (a, k) (blocks L0 A0) -> forall i, 0 <= i < len -> ~ (a <= text + i < a + k).
Proof.
  intros Lc Ac mc mdc a k RPc Hb Hn i Hi Hx. pose proof RPc as (M & _).
  pose proof TOK as (TXL & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  destruct (rk_blk_facts Lc Ac mc mdc a k M Hb) as (B1 & B2 & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws API) Lc Ac mc mdc M) as PW.
  assert (OLD : forall a0 k0, In (a0, k0) (blocks L0 A0) -> a0 <= text -> text + len <= a0 + k0 -> False).
  { intros a0 k0 Hb0 Ha Hk.
    pose proof (pi_blk_keep _ _ _ _ _ _ RPc Hb0) as H2.
    assert (Hne : (a0, k0) <> (a, k)) by (intros E; rewrite E in Hb0; exact (Hn Hb0)).
    destruct (rk_pairwise_in _ _ _ _ PW H2 Hb Hne) as [Rd|Rd]; unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia. }
  destruct TXL as [Hs | [Him | [(a0 & k0 & Hb0 & _ & Ha & Hk) | (a0 & k0 & Hl & Ha & Hk)]]].
  - lia.
  - destruct (rk_blk_user Lc Ac a k Hb) as (pp & Hp & Ep).
    apply (YL01.ax_blocks_img AX Lc Ac mc mdc pp k (text + i - a) M Hp ltac:(lia)). rewrite Ep.
    replace (a + (text + i - a)) with (text + i) by lia. exact (Him i Hi).
  - exact (OLD a0 k0 Hb0 Ha Hk).
  - pose proof LG0 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. unfold lin in Hl.
    destruct (LF _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0. exact (OLD _ _ Hb0 ltac:(lia) ltac:(lia)).
Qed.

Definition pi_vc (w : nat) (c : config) : Prop :=
  exists (fxc : YK11.FPState) (R : bvmap 5 word) (m : word -> option byte) (mdc : Model) (Lc : layout) (Ac : astate)
    (Lamc : list (Z * Z)) (tr : list ev) (D : list (Z * Z)) (n cap : nat) (acc : list (list Z * jv))
    (P num kids keys : Z) (Di : list (Z * Z)) (nm : list Z) (Dn : list (Z * Z)),
    c = mkCfg (@mkst fxc R (Z_to_bv 64 0x14330) m (seg_rom segs)) mdc /\
    (d < MAXD)%nat /\ pi_cs R /\ getr R 1 = Z_to_bv 64 0x151bc /\ getr R 10 = Z_to_bv 64 q /\
    getr R 11 = Z_to_bv 64 (kids + 56 * Z.of_nat n) /\
    pi_glob fxc Lc Ac m mdc Lamc tr D /\
    ledger B Lc Ac m Lamc (Z.max peak0 (lsum Lam0 + hpeak tr)) (cnt0 + Z.of_nat (calls tr)) fail0 /\
    ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls tr)) /\
    pj_in_ok segs m q text len P (Z.of_nat d + 1) tb /\
    (length (rest_at tb text P) <= w)%nat /\
    Z.of_nat (calls tr) + 2 * Z.of_nat (length (rest_at tb text P)) <= 2 * Z.of_nat (length pi_x) /\
    ext (jr_items jr_strtod d o pi_x pi_ok) tr (jval d o n cap acc nm (rest_at tb text P) (skipn (calls tr) pi_ok)) /\
    room_run RF (rf_run RF b0 tr) (snd (fst (jval d o n cap acc nm (rest_at tb text P) []))) /\
    length acc = n /\ inv (S n) cap /\
    D = pis_slots o kids keys (Z.of_nat cap) ++ Di ++ Dn /\
    pis_open segs m (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) (map snd (rev acc)) (map fst (rev acc)) Di /\
    (if o then exists x k, Dn = [(x, k)] /\ pj_u64 segs m (keys + 8 * Z.of_nat n) x /\ pj_cstr segs m (lin Lamc) x k nm
     else Dn = []) /\
    pj_zero segs m (kids + 56 * Z.of_nat n) /\
    Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev acc)).

Section Val.
Variables (vfx : YK11.FPState) (vR : bvmap 5 word) (vm : word -> option byte) (vmd : Model) (vL : layout)
  (vA : astate) (vLam : list (Z * Z)) (vtr : list ev) (vD : list (Z * Z)) (vn vcap : nat)
  (vacc : list (list Z * jv)) (vP vnum vkids vkeys : Z) (vDi : list (Z * Z)) (vnm : list Z) (vDn : list (Z * Z)).
Hypothesis vHD : (d < MAXD)%nat.
Hypothesis vCS : pi_cs vR.
Hypothesis vG1 : getr vR 1 = Z_to_bv 64 0x151bc.
Hypothesis vG10 : getr vR 10 = Z_to_bv 64 q.
Hypothesis vG11 : getr vR 11 = Z_to_bv 64 (vkids + 56 * Z.of_nat vn).
Hypothesis vGL : pi_glob vfx vL vA vm vmd vLam vtr vD.
Hypothesis vLG : ledger B vL vA vm vLam (Z.max peak0 (lsum Lam0 + hpeak vtr)) (cnt0 + Z.of_nat (calls vtr)) fail0.
Hypothesis vNF : ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls vtr)).
Hypothesis vPIN : pj_in_ok segs vm q text len vP (Z.of_nat d + 1) tb.
Hypothesis vCB : Z.of_nat (calls vtr) + 2 * Z.of_nat (length (rest_at tb text vP)) <= 2 * Z.of_nat (length pi_x).
Hypothesis vEXT :
  ext (jr_items jr_strtod d o pi_x pi_ok) vtr (jval d o vn vcap vacc vnm (rest_at tb text vP) (skipn (calls vtr) pi_ok)).
Hypothesis vROOM : room_run RF (rf_run RF b0 vtr) (snd (fst (jval d o vn vcap vacc vnm (rest_at tb text vP) []))).
Hypothesis vLA : length vacc = vn.
Hypothesis vINV : inv (S vn) vcap.
Hypothesis vED : vD = pis_slots o vkids vkeys (Z.of_nat vcap) ++ vDi ++ vDn.
Hypothesis vPO : pis_open segs vm (lin vLam) v o vnum vkids vkeys (Z.of_nat vcap) (Z.of_nat vn) (map snd (rev vacc))
  (map fst (rev vacc)) vDi.
Hypothesis vKEY : if o then exists x k, vDn = [(x, k)] /\ pj_u64 segs vm (vkeys + 8 * Z.of_nat vn) x /\
  pj_cstr segs vm (lin vLam) x k vnm else vDn = [].
Hypothesis vZ : pj_zero segs vm (vkids + 56 * Z.of_nat vn).
Hypothesis vDEP : Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev vacc)).

Local Notation vsl := (vkids + 56 * Z.of_nat vn).

Lemma v_lt : (vn < vcap)%nat.
Proof. destruct vINV as (H & _). lia. Qed.

Lemma v_ts : length (map snd (rev vacc)) = vn.
Proof. rewrite length_map, length_rev. exact vLA. Qed.

Lemma v_slots_in : incl (pis_slots o vkids vkeys (Z.of_nat vcap) ++ vDi) vLam.
Proof. exact (pis_open_incl segs vm vLam v o vnum vkids vkeys _ _ _ _ vDi vPO). Qed.

Lemma v_kids_slot : In (vkids, 56 * Z.of_nat vcap) (pis_slots o vkids vkeys (Z.of_nat vcap)).
Proof.
  pose proof v_lt. unfold pis_slots, kids_blk. rewrite (proj2 (Z.eqb_neq (Z.of_nat vcap) 0)) by lia.
  apply in_or_app. left. left. reflexivity.
Qed.

Lemma v_keys_slot : o = true -> In (vkeys, 8 * Z.of_nat vcap) (pis_slots o vkids vkeys (Z.of_nat vcap)).
Proof.
  intros Eo. pose proof v_lt. unfold pis_slots, kids_blk, keys_blk. rewrite Eo.
  rewrite (proj2 (Z.eqb_neq (Z.of_nat vcap) 0)) by lia. cbn. right. left. reflexivity.
Qed.

Lemma v_kids_in : In (vkids, 56 * Z.of_nat vcap) vLam.
Proof. apply v_slots_in. apply in_or_app. left. exact v_kids_slot. Qed.

Lemma v_kids_rng : 4112 <= vkids /\ vkids + 56 * Z.of_nat vcap <= alloc_ceiling /\ vkids mod 16 = 0.
Proof.
  pose proof vGL as (_ & _ & RP & _). pose proof RP as (M & _).
  destruct (ledger_block_range B API vL vA vm vmd vLam _ _ _ _ _ M vLG v_kids_in) as (R1 & R2 & _).
  pose proof (ledger_block_aligned B API vL vA vm vmd vLam _ _ _ _ _ M vLG v_kids_in) as R3. lia.
Qed.

Lemma v_D_nodup : NoDup vD.
Proof. pose proof vGL as (_ & _ & _ & _ & _ & PERM & _). exact (pi_D_nodup _ _ _ _ _ _ _ vD vLG PERM). Qed.

Lemma v_D_in : incl vD vLam.
Proof.
  pose proof vGL as (_ & _ & _ & _ & _ & PERM & _). intros b Hb.
  apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. left. exact Hb.
Qed.

Lemma v_kids_apart : forall a k x, In (a, k) vLam -> (a, k) <> (vkids, 56 * Z.of_nat vcap) -> a <= x < a + k ->
  ~ (vsl <= x < vsl + 56).
Proof.
  intros a k x Hb Hne Hx Hs. pose proof vGL as (_ & _ & RP & _). pose proof RP as (M & _). pose proof v_lt.
  destruct (pi_lam_disj vL vA vm vmd vLam _ _ _ a k _ _ M vLG Hb v_kids_in Hne); lia.
Qed.

Lemma v_fresh_slot : forall x, vsl <= x < vsl + 56 -> pi_fresh x.
Proof.
  intros x Hx. pose proof vGL as (_ & _ & RP & _ & _ & PERM & _ & _ & NB & _). pose proof v_lt.
  apply (pi_fresh_D vL vA vm vmd vLam _ _ _ vD x RP vLG PERM NB).
  exists vkids, (56 * Z.of_nat vcap). split; [rewrite vED; apply in_or_app; left; exact v_kids_slot | lia].
Qed.

Lemma v_HE : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 Dv,
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> incl Dv Lam2 -> new_blks vL vA Dv ->
  forall a, rd_writes q vsl Dv a -> pi_E0 a \/ pi_fresh a.
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 Dv RP2 LG2 INC NB a [Ha|[Ha|[Ha|Ha]]].
  - right. exact (v_fresh_slot a Ha).
  - left. right. left. exact Ha.
  - right. pose proof vGL as (_ & _ & RP & _).
    exact (pi_fresh_call vL vA vm vmd _ vR _ L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv a RP RP2 LG2 INC NB Ha).
  - left. right. right. exact Ha.
Qed.

Lemma v_post : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 Dv,
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> Permutation Lam2 (Dv ++ vLam) -> new_blks vL vA Dv ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 /\
  pi_frm mem2 /\ (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo mem2) /\ pi_cs regs2 /\
  pis_open segs mem2 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (Z.of_nat vn) (map snd (rev vacc))
    (map fst (rev vacc)) vDi /\
  (if o then exists x k, vDn = [(x, k)] /\ pj_u64 segs mem2 (vkeys + 8 * Z.of_nat vn) x /\
     pj_cstr segs mem2 (lin Lam2) x k vnm else vDn = []).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 Dv RP2 LG2 PL2 NB2.
  pose proof (pi_K_bounds vHD) as (_ & _ & _ & KV & _ & _ & _ & KV0).
  pose proof vGL as (_ & _ & RP & _ & FR & PERM & _ & _ & NB & _ & AUX).
  pose proof RP as (M & _). pose proof RP2 as (M2 & _).
  pose proof (pi_sp vR vCS) as SP. pose proof v_lt as LT. pose proof v_kids_rng as KR.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  assert (INC : incl Dv Lam2)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym PL2)); apply in_or_app; left; exact Hb).
  assert (INCo : incl vLam Lam2)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym PL2)); apply in_or_app; right; exact Hb).
  pose proof (v_HE L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 INC NB2) as HE.
  assert (RPc : rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2)
    by exact (pi_rp_call vL vA vm vmd _ vR _ _ L2 A2 regs2 mem2 md2 RP RP2 SP KV KV0 HE (fun p n _ Hf => Hf)).
  assert (OLD : forall a k x, In (a, k) vLam -> a <= x < a + k -> ~ (vsl <= x < vsl + 56) -> pis_same segs vm mem2 x).
  { intros a k x Hb Hx Hs.
    apply (pi_lam_same vL vA vm vmd vLam _ _ _ _ vR _ _ L2 A2 regs2 mem2 md2 Lam2 _ _ _ a k x vLG RP2 LG2 Hb (INCo _ Hb)
      (fun Hf => Hf) Hx).
    destruct (ledger_block_range B API vL vA vm vmd vLam _ _ _ a k M vLG Hb) as (R1 & R2 & _).
    intros [Hv|[Hq|[(a' & k' & Hin & Hx')|Hst]]].
    - exact (Hs Hv).
    - unfold pj_in_set in Hq. lia.
    - assert (Hne : (a, k) <> (a', k')).
      { intros E. injection E as <- <-. pose proof vLG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
        destruct (LF _ Hb) as (_ & Lin & _). cbn [fst snd] in Lin. exact (NB2 a k Hin Lin). }
      destruct (pi_lam_disj L2 A2 mem2 md2 Lam2 _ _ _ a k a' k' M2 LG2 (INCo _ Hb) (INC _ Hin) Hne); lia.
    - apply (ledger_block_not_img B vL vA vm vLam _ _ _ a k (x - a) vLG Hb ltac:(lia)).
      replace (a + (x - a)) with x by lia. exact (pi_statics_img x Hst). }
  assert (VS : forall x, v <= x < v + 56 -> pis_same segs vm mem2 x).
  { apply (pi_v_same vL vA vm vmd _ vR _ _ L2 A2 regs2 mem2 md2 RP RP2 ltac:(lia)); [|intros a k _ Hf; exact Hf].
    intros x Hx [Hs|[Hq|[(a' & k' & Hin & Hx')|Hst]]].
    - pose proof vPO as (_ & HA & _).
      apply (HA (vkids, 56 * Z.of_nat vcap) x); [apply in_or_app; left; exact v_kids_slot | unfold pj_holds; cbn [fst snd]; lia
        | exact Hx].
    - pose proof DJV as DV. cbn [Frame.disjoint_from] in DV. unfold pj_in_set in Hq. lia.
    - pose proof LG2 as (_ & _ & _ & _ & _ & LF2). rewrite Forall_forall in LF2.
      destruct (LF2 _ (INC _ Hin)) as (_ & Lin2 & _). cbn [fst snd] in Lin2.
      apply (pi_new_raw L2 A2 mem2 md2 (a' - 16) (k' + 16) x RPc Lin2); [|lia|exact Hx].
      intros Hb0. exact (NB2 a' k' Hin (pi_blk_keep _ _ _ _ _ _ RP Hb0)).
    - pose proof RPL as (_ & _ & PNO). destruct (PNO (x - v) ltac:(lia)) as (_ & N2 & _).
      apply N2. replace (v + (x - v)) with x by lia. exact Hst. }
  pose proof vPO as PO. pose proof PO as (HN & HA & Hh & Hs & Hk & Hi).
  pose proof v_D_nodup as DND. rewrite vED in DND.
  split; [exact RPc|].
  split; [exact (pi_frm_call vL vA vm vmd _ vR _ _ L2 A2 regs2 mem2 md2 RP2 ltac:(lia) HE FR)|].
  split; [exact (pi_aux_call vL vA vm vmd _ vR _ _ L2 A2 regs2 mem2 md2 RP2 ltac:(lia) HE AUX)|].
  split; [pose proof RP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _); exact (pi_cs_rp vR regs2 vCS RPr)|].
  split.
  { apply (pis_frame segs vm (lin vLam) mem2 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (Z.of_nat vn) _ _ vDi vnum
      (Z.of_nat vn) PO).
    - exact (pis_hdr_frame segs vm mem2 v _ _ _ _ _ _ _ Hh VS).
    - lia.
    - intros a k Hak. exact (INCo _ (v_slots_in _ Hak)).
    - intros x [Hx|[(Eo & Hx)|((a & k) & Hb & Hx)]].
      + rewrite v_ts in Hx. apply (OLD vkids (56 * Z.of_nat vcap) x v_kids_in); lia.
      + rewrite v_ts in Hx. pose proof (v_keys_slot Eo) as Hks.
        assert (Hne : (vkeys, 8 * Z.of_nat vcap) <> (vkids, 56 * Z.of_nat vcap)).
        { intros E. pose proof (pis_nodup_l _ _ _ HN) as N0. unfold pis_slots, kids_blk, keys_blk in N0, Hks.
          rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat vcap) 0)) in N0, Hks by lia. cbn in N0. rewrite E in N0.
          apply NoDup_ListNoDup in N0. inversion N0 as [|? ? Hn0 _]. apply Hn0. left. reflexivity. }
        apply (OLD vkeys (8 * Z.of_nat vcap) x (v_slots_in _ ltac:(apply in_or_app; left; exact Hks))); [lia|].
        apply (v_kids_apart _ _ x (v_slots_in _ ltac:(apply in_or_app; left; exact Hks)) Hne). lia.
      + unfold pj_holds in Hx; cbn [fst snd] in Hx.
        assert (HbL : In (a, k) vLam) by (apply v_slots_in; apply in_or_app; right; exact Hb).
        apply (OLD a k x HbL Hx).
        apply (v_kids_apart a k x HbL); [|exact Hx].
        intros E. rewrite E in Hb. exact (pis_nodup_app_disj _ _ _ _ HN v_kids_slot Hb). }
  pose proof vKEY as KY. destruct (Bool.bool_dec o true) as [Eo|Eo].
  - rewrite Eo in KY |- *. cbv beta iota in KY |- *.
    destruct KY as (x & k & -> & Hu & Hc). exists x, k. split; [reflexivity|].
    pose proof (v_keys_slot Eo) as Hks.
    assert (HkL : In (vkeys, 8 * Z.of_nat vcap) vLam) by (apply v_slots_in; apply in_or_app; left; exact Hks).
    destruct (ledger_block_range B API vL vA vm vmd vLam _ _ _ _ _ M vLG HkL) as (Y1 & Y2 & _).
    assert (Hne : (vkeys, 8 * Z.of_nat vcap) <> (vkids, 56 * Z.of_nat vcap)).
    { intros E. pose proof (pis_nodup_l _ _ _ HN) as N0. unfold pis_slots, kids_blk, keys_blk in N0, Hks.
      rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat vcap) 0)) in N0, Hks by lia. cbn in N0. rewrite E in N0.
      apply NoDup_ListNoDup in N0. inversion N0 as [|? ? Hn0 _]. apply Hn0. left. reflexivity. }
    split.
    + apply (pis_u64_frame segs vm mem2 _ x Hu). intros y Hy.
      refine (proj1 (OLD vkeys (8 * Z.of_nat vcap) y HkL ltac:(lia) _)).
      apply (v_kids_apart _ _ y HkL Hne). lia.
    + pose proof Hc as (Hl & _ & _).
      apply (pis_cstr_frame segs vm (lin vLam) mem2 (lin Lam2) x k vnm Hc (INCo _ Hl)). intros y Hy.
      unfold pj_holds in Hy; cbn [fst snd] in Hy.
      refine (proj1 (OLD x k y Hl Hy _)).
      apply (v_kids_apart x k y Hl); [|exact Hy].
      intros E. apply (pis_nodup_app_disj _ _ _ (vkids, 56 * Z.of_nat vcap) DND v_kids_slot).
      rewrite <- E. apply in_or_app. right. left. reflexivity.
  - assert (Eo' : o = false) by (destruct o; [contradiction | reflexivity]).
    rewrite Eo' in KY |- *. exact KY.
Qed.

Lemma v_glue : forall (A2 : astate) Lam2 peak2 cnt2 fail2 tv Dv,
  Permutation Lam2 (Dv ++ vLam) -> Permutation (map snd Dv) (map Z.of_nat (lsz tv)) ->
  Z.of_nat (length Dv) = nlive tv -> new_blks vL vA Dv ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak vtr)) (lsum vLam + hpeak tv) ->
  cnt2 = cnt0 + Z.of_nat (calls vtr) + Z.of_nat (calls tv) ->
  fail_after (cnt0 + Z.of_nat (calls vtr)) fail0 (calls tv) fail2 ->
  rf_ok RF A2 (rf_run RF (rf_run RF b0 vtr) tv) ->
  Permutation Lam2 ((vD ++ Dv) ++ Lam0) /\ Permutation (map snd (vD ++ Dv)) (map Z.of_nat (lsz (vtr ++ tv))) /\
  Z.of_nat (length (vD ++ Dv)) = nlive (vtr ++ tv) /\ new_blks L0 A0 (vD ++ Dv) /\
  peak2 = Z.max peak0 (lsum Lam0 + hpeak (vtr ++ tv)) /\ rf_ok RF A2 (rf_run RF b0 (vtr ++ tv)) /\
  cnt2 = cnt0 + Z.of_nat (calls (vtr ++ tv)) /\ fail_after cnt0 fail0 (calls (vtr ++ tv)) fail2.
Proof.
  intros A2 Lam2 peak2 cnt2 fail2 tv Dv PL2 HP2 NL2 NB2 PK2 CN2 FA2 RS2.
  pose proof vGL as (_ & _ & RP & _ & _ & PERM & HP & NL & NB & _).
  assert (HLtv : Z.of_nat (length (lsz tv)) = nlive tv).
  { rewrite <- NL2. f_equal. rewrite <- (length_map Z.of_nat (lsz tv)), <- (Permutation_length HP2). apply length_map. }
  split.
  { eapply Permutation_trans; [exact PL2|]. eapply Permutation_trans; [apply Permutation_app_head; exact PERM|].
    rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  split.
  { rewrite (lsz_app vtr tv HLtv), !map_app. eapply Permutation_trans; [apply Permutation_app_comm|].
    apply Permutation_app; [exact HP2 | exact HP]. }
  split; [rewrite length_app, Nat2Z.inj_add, pi_nlive_app; lia|].
  split.
  { intros a k Hin. apply in_app_or in Hin.
    destruct Hin as [Hin|Hin]; [exact (NB a k Hin) | exact (pi_new_keep vL vA vm vmd Dv RP NB2 a k Hin)]. }
  split.
  { pose proof (lsz_counts vD vtr HP NL) as HL. rewrite (pi_lsum_perm _ _ PERM), pi_lsum_app in PK2.
    rewrite hpeak_app. lia. }
  split; [rewrite rf_run_app; exact RS2|].
  split; [rewrite calls_app, Nat2Z.inj_add; lia|].
  rewrite calls_app. exact (fail_after_app cnt0 fail0 (calls vtr) (calls tv) fail2 vNF FA2).
Qed.

Lemma v_arm_fail : forall fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 tv okr Dv m3 R',
  frm_zero (@fp_csr fx2) -> fregs_kept vfx fx2 ->
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok) = (None, tv, okr) ->
  cnt2 = cnt0 + Z.of_nat (calls vtr) + Z.of_nat (calls tv) ->
  fail_after (cnt0 + Z.of_nat (calls vtr)) fail0 (calls tv) fail2 ->
  Permutation Lam2 (Dv ++ vLam) -> Permutation (map snd Dv) (map Z.of_nat (lsz tv)) ->
  Z.of_nat (length Dv) = nlive tv -> new_blks vL vA Dv ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak vtr)) (lsum vLam + hpeak tv) ->
  rf_ok RF A2 (rf_run RF (rf_run RF b0 vtr) tv) ->
  pj_in_after B mem2 q text len (Z.of_nat (S d)) 33 -> pj_fd segs mem2 (lin Lam2) (MAXD - S d) vsl Dv ->
  chg [(v + 40, v + 48)] mem2 m3 -> bytes_at rsegs m3 (v + 40) (le8 (Z_to_bv 64 (Z.of_nat vn + 1))) ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst fx2 R' (getr regs0 1) m3 (seg_rom segs)) md2).
Proof.
  intros fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 tv okr Dv m3 R' FZ2 FK2 RP2 RD2 LG2 JV CN2 FA2 PL2 HP2 NL2 NB2
    PK2 RS2 PA2 FD2 CH3 BV3 RPF R10F.
  destruct (v_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 PL2 NB2) as (RPc & FR2 & AUX2 & CS2 & PO2 & KY2).
  destruct (v_glue A2 Lam2 peak2 cnt2 fail2 tv Dv PL2 HP2 NL2 NB2 PK2 CN2 FA2 RS2)
    as (PL' & HP' & NL' & NB' & PK' & RS' & CN' & FA').
  pose proof CH3 as (MU3 & WM3 & _).
  assert (CH3' : chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] mem2 m3)
    by (eapply chg_weaken; [|exact CH3]; intros z Hz; cbn [outside] in Hz |- *; tauto).
  destruct (pi_kA3 L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 (vD ++ Dv) RPc RD2 LG2 PL' NB' FR2 AUX2 CH3')
    as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  pose proof RP3 as (M3 & _).
  pose proof (pi_jval_none vtr vn vcap vacc vnm _ tv okr JV vEXT) as JI.
  pose proof vGL as (_ & FK & _).
  assert (FKt : fregs_kept fx fx2) by (intros r Hr; rewrite (FK2 r Hr); exact (FK r Hr)).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ vPIN) as (Q0 & Q1 & _).
  assert (S1 : forall x, 0 <= x < 2 ^ 64 -> ~ (v + 40 <= x < v + 48) -> pis_same segs mem2 m3 x).
  { intros x Hx Hv. assert (Ho : outside [(v + 40, v + 48)] x) by (cbn [outside]; split; [lia | exact I]).
    split; [exact (MemNorm.mbyte_munch _ _ _ _ x MU3 Hx Ho) | intros Hw; exact (proj1 (rk_writable_munch _ _ mem2 m3 x MU3 Hx Ho) Hw)]. }
  apply (pi_exit fx2 L2 A2 m3 md2 Lam2 peak2 cnt2 fail2 (vtr ++ tv) (vD ++ Dv) R' None okr FZ2 FKt RP3 RD3 LG3 PL' HP'
    NL' NB' PK' RS' CN' FA' RPF JI).
  split; [exact R10F|]. split.
  - rewrite Nat2Z.inj_succ in PA2. apply (pi_after_mv mem2 m3 _ _ PA2). intros x Hx. apply S1; lia.
  - rewrite vED, <- !app_assoc. rewrite (pis_maxd d vHD).
    apply (pi_fd_store segs mem2 m3 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (map snd (rev vacc)) (map fst (rev vacc))
      vDi (MAXD - S d) vDn Dv q).
    + rewrite v_ts. exact PO2.
    + rewrite v_ts. pose proof v_lt. lia.
    + exact vDEP.
    + rewrite v_ts. exact FD2.
    + destruct (Bool.bool_dec o true) as [Eo|Eo].
      * rewrite Eo in KY2 |- *. cbv beta iota in KY2 |- *. destruct KY2 as (x & k & -> & Hu & Hc).
        cbn [pj_key]. exists x. split; [rewrite v_ts; exact Hu | right; exists k; split; [exact (proj1 Hc) | reflexivity]].
      * assert (Eo' : o = false) by (destruct o; [contradiction | reflexivity]). rewrite Eo' in KY2 |- *. exact KY2.
    + pose proof (pi_D_nodup L2 A2 m3 Lam2 _ _ _ (vD ++ Dv) LG3 PL') as ND. rewrite vED, <- !app_assoc in ND. exact ND.
    + apply (pi_apart_new L2 A2 m3 md2 Lam2 _ _ _ (vDn ++ Dv) RP3 LG3).
      * intros b Hb. apply (Permutation_in _ (Permutation_sym PL')). apply in_or_app. left. rewrite vED.
        apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        -- apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hb.
        -- apply in_or_app. right. exact Hb.
      * intros a k Hb. apply NB'. rewrite vED. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        -- apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hb.
        -- apply in_or_app. right. exact Hb.
    + rewrite v_ts. pose proof PO2 as (_ & _ & Hh2 & (_ & HNC & _) & _).
      apply (pis_hdr_n segs mem2 m3 v _ _ _ _ _ _ _ (Z.of_nat vn + 1) Hh2); [lia | rewrite pi_seg; exact BV3 | |].
      * intros x Hx Hx'. pose proof VZ as ((_ & (V0 & V1 & _)) & _). destruct (S1 x ltac:(lia) Hx') as [E _]. exact E.
      * intros x _ Hw. unfold writable_at in Hw |- *. rewrite pi_seg in Hw |- *. exact (WM3 _ Hw).
    + intros b x Hb Hx. assert (HbL : In b Lam2).
      { assert (HbD : In b (vD ++ Dv)) by (rewrite vED, <- !app_assoc; exact Hb).
        apply (Permutation_in _ (Permutation_sym PL')). apply in_or_app. left. exact HbD. }
      destruct b as (a & k). unfold pj_holds in Hx; cbn [fst snd] in Hx.
      pose proof LG3 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ HbL) as (Lk & _). cbn [fst snd] in Lk.
      destruct (ledger_block_range B API L2 A2 m3 md2 Lam2 _ _ _ a k M3 LG3 HbL) as (R1 & R2 & _).
      pose proof rk_ceil. pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof pi_K80. lia.
    + intros x Hx Hv Hq. apply S1; lia.
Qed.

Lemma v_vspec : forall t r tv okr,
  jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok) = (Some (t, r), tv, okr) ->
  (length r < length (rest_at tb text vP))%nat /\ (calls tv + 2 * length r <= 2 * length (rest_at tb text vP))%nat /\
  rk_suf r (rest_at tb text vP) /\ (depth t <= MAXD - S d)%nat.
Proof.
  intros t r tv okr JV.
  pose proof (vspec_jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok)) as H. rewrite JV in H.
  unfold vspec in H. cbn [fst snd] in H. destruct H as (_ & _ & H). destruct (H t r eq_refl) as (H1 & H2 & _).
  split; [exact H1|]. split; [exact H2|]. unfold jr_value in JV.
  split; [exact (proj1 (rk_suf_fuel _) _ _ _ _ _ _ _ JV) | exact (proj1 (depth_fuel jr_strtod _) _ _ _ _ _ _ _ JV)].
Qed.

Lemma v_succ : forall a tv okr,
  jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok) = (Some a, tv, okr) ->
  ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls (vtr ++ tv))).
Proof.
  intros a tv okr JV (H1 & H2).
  pose proof (agrees_some_upto _ _ _ _ _ _ (agrees_jr_value jr_strtod (S d) (rest_at tb text vP)) JV) as UP.
  rewrite calls_app, Nat2Z.inj_add in H2.
  destruct (Z_lt_le_dec fail0 (cnt0 + Z.of_nat (calls vtr))) as [Hlt|Hge]; [apply vNF; lia|].
  pose proof (UP (Z.to_nat (fail0 - cnt0 - Z.of_nat (calls vtr))) ltac:(lia)) as U.
  rewrite pi_ok_skip in U. replace (cnt0 + Z.of_nat (calls vtr) + Z.of_nat (Z.to_nat (fail0 - cnt0 - Z.of_nat (calls vtr))))
    with fail0 in U by lia.
  rewrite Z.eqb_refl in U. discriminate.
Qed.

Lemma v_snoc3 : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 Dv t m3,
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  Permutation Lam2 (Dv ++ vLam) -> new_blks vL vA Dv -> pj_node segs mem2 (lin Lam2) vsl t Dv ->
  chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] mem2 m3 ->
  bytes_at rsegs m3 (v + 40) (le8 (Z_to_bv 64 (Z.of_nat vn + 1))) ->
  pis_open segs m3 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (Z.of_nat (S vn)) (map snd (rev ((vnm, t) :: vacc)))
    (map fst (rev ((vnm, t) :: vacc))) (vDi ++ vDn ++ Dv).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 Dv t m3 RP2 RD2 LG2 PL2 NB2 HT CH3 BV3.
  destruct (v_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 PL2 NB2) as (RPc & FR2 & AUX2 & CS2 & PO2 & KY2).
  pose proof vGL as (_ & _ & RP & _ & _ & PERM & _ & _ & NB & _).
  pose proof RPc as (M2 & _).
  assert (PL' : Permutation Lam2 ((vD ++ Dv) ++ Lam0)).
  { eapply Permutation_trans; [exact PL2|]. eapply Permutation_trans; [apply Permutation_app_head; exact PERM|].
    rewrite app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  assert (NB' : new_blks L0 A0 (vD ++ Dv)).
  { intros a k Hin. apply in_app_or in Hin.
    destruct Hin as [Hin|Hin]; [exact (NB a k Hin) | exact (pi_new_keep vL vA vm vmd Dv RP NB2 a k Hin)]. }
  destruct (pi_kA3 L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 (vD ++ Dv) RPc RD2 LG2 PL' NB' FR2 AUX2 CH3)
    as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  pose proof CH3 as (MU3 & WM3 & _).
  assert (INL : forall b, In b (pis_slots o vkids vkeys (Z.of_nat vcap) ++ vDi ++ vDn ++ Dv) -> In b Lam2).
  { intros b Hb. assert (HbD : In b (vD ++ Dv)) by (rewrite vED, <- !app_assoc; exact Hb).
    apply (Permutation_in _ (Permutation_sym PL')). apply in_or_app. left. exact HbD. }
  assert (ND : NoDup (pis_slots o vkids vkeys (Z.of_nat vcap) ++ vDi ++ vDn ++ Dv)).
  { pose proof (pi_D_nodup L2 A2 mem2 Lam2 _ _ _ (vD ++ Dv) LG2 PL') as N. rewrite vED, <- !app_assoc in N. exact N. }
  assert (AP : pj_apart (vDn ++ Dv) v).
  { apply (pi_apart_new L2 A2 mem2 md2 Lam2 _ _ _ (vDn ++ Dv) RPc LG2).
    - intros b Hb. apply INL. apply in_or_app. right. apply in_or_app. right. exact Hb.
    - intros a k Hb. apply NB'. rewrite vED. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      + apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hb.
      + apply in_or_app. right. exact Hb. }
  assert (PO2' : pis_open segs mem2 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap)
                   (Z.of_nat vn) (map snd (rev vacc)) (map fst (rev vacc)) vDi) by exact PO2.
  pose proof (pis_snoc segs mem2 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (Z.of_nat vn) _ _ vDi t vnm vDn Dv PO2'
    ltac:(rewrite v_ts; exact HT) ltac:(rewrite v_ts; exact KY2) ND AP) as SN.
  replace (map snd (rev ((vnm, t) :: vacc))) with (map snd (rev vacc) ++ [t]) by (cbn [rev]; rewrite map_app; reflexivity).
  replace (map fst (rev ((vnm, t) :: vacc))) with (map fst (rev vacc) ++ [vnm]) by (cbn [rev]; rewrite map_app; reflexivity).
  pose proof PO2 as (_ & _ & Hh2 & (_ & HNC & _) & _).
  pose proof SN as (_ & HA' & _).
  pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  apply (pis_frame segs mem2 (lin Lam2) m3 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (Z.of_nat vn) _ _ _ vnum
    (Z.of_nat (S vn)) SN).
  - rewrite Nat2Z.inj_succ. apply (pis_hdr_n segs mem2 m3 v _ _ _ _ _ _ _ (Z.of_nat vn + 1) Hh2); [lia | rewrite pi_seg; exact BV3 | |].
    + intros x Hx Hx'. exact (proj1 (MB3 x ltac:(lia) Hx' ltac:(lia))).
    + intros x _ Hw. unfold writable_at in Hw |- *. rewrite pi_seg in Hw |- *. exact (WM3 _ Hw).
  - pose proof v_lt. lia.
  - intros a k Hak. exact (INL _ Hak).
  - assert (BL : forall b x, In b (pis_slots o vkids vkeys (Z.of_nat vcap) ++ vDi ++ vDn ++ Dv) -> pj_holds b x ->
                   pis_same segs mem2 m3 x).
    { intros (a & k) x Hb Hx. unfold pj_holds in Hx; cbn [fst snd] in Hx.
      pose proof LG2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ (INL _ Hb)) as (Lk & _). cbn [fst snd] in Lk.
      destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ a k M2 LG2 (INL _ Hb)) as (R1 & R2 & _).
      pose proof rk_ceil. pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof pi_K80.
      apply MB3; [lia | | lia].
      intros Hv. apply (HA' (a, k) x Hb); [unfold pj_holds; cbn [fst snd]; lia | lia]. }
    intros x [Hx|[(Eo & Hx)|(b & Hb & Hx)]].
    + rewrite length_app, v_ts in Hx. cbn [length] in Hx. pose proof v_lt.
      apply (BL (vkids, 56 * Z.of_nat vcap) x); [apply in_or_app; left; exact v_kids_slot | unfold pj_holds; cbn [fst snd]; lia].
    + rewrite length_app, v_ts in Hx. cbn [length] in Hx. pose proof v_lt.
      apply (BL (vkeys, 8 * Z.of_nat vcap) x); [apply in_or_app; left; exact (v_keys_slot Eo) | unfold pj_holds; cbn [fst snd]; lia].
    + apply (BL b x); [apply in_or_app; right; exact Hb | exact Hx].
Qed.

Lemma v_arm_refuse : forall fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv okr Dv m3 x R',
  frm_zero (@fp_csr fx2) -> fregs_kept vfx fx2 ->
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok) = (Some (t, r), tv, okr) ->
  cnt2 = cnt0 + Z.of_nat (calls vtr) + Z.of_nat (calls tv) ->
  fail_after (cnt0 + Z.of_nat (calls vtr)) fail0 (calls tv) fail2 ->
  Permutation Lam2 (Dv ++ vLam) -> Permutation (map snd Dv) (map Z.of_nat (lsz tv)) ->
  Z.of_nat (length Dv) = nlive tv -> new_blks vL vA Dv ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak vtr)) (lsum vLam + hpeak tv) ->
  rf_ok RF A2 (rf_run RF (rf_run RF b0 vtr) tv) ->
  pj_node segs mem2 (lin Lam2) vsl t Dv ->
  chg [(v + 40, v + 48); (q, q + 8)] mem2 m3 -> bytes_at rsegs m3 (v + 40) (le8 (Z_to_bv 64 (Z.of_nat vn + 1))) ->
  rest_at tb text x = skip r -> (forall c r', rest_at tb text x = c :: r' -> c <> 44 /\ c <> closer o) ->
  pj_in_ok rsegs m3 q text len x (Z.of_nat d + 1) tb ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst fx2 R' (getr regs0 1) m3 (seg_rom segs)) md2).
Proof.
  intros fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv okr Dv m3 x R' FZ2 FK2 RP2 RD2 LG2 JV CN2 FA2 PL2 HP2 NL2
    NB2 PK2 RS2 HT CH3 BV3 RX NC PX RPF R10F.
  destruct (v_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 PL2 NB2) as (RPc & FR2 & AUX2 & CS2 & PO2 & KY2).
  destruct (v_glue A2 Lam2 peak2 cnt2 fail2 tv Dv PL2 HP2 NL2 NB2 PK2 CN2 FA2 RS2)
    as (PL' & HP' & NL' & NB' & PK' & RS' & CN' & FA').
  assert (CH3' : chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] mem2 m3)
    by (eapply chg_weaken; [|exact CH3]; intros z Hz; cbn [outside] in Hz |- *; tauto).
  destruct (pi_kA3 L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 (vD ++ Dv) RPc RD2 LG2 PL' NB' FR2 AUX2 CH3')
    as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  pose proof RP3 as (M3 & _). pose proof CH3 as (MU3 & WM3 & _).
  destruct (v_vspec t r tv okr JV) as (_ & _ & _ & DT).
  pose proof (pi_jval_some vtr vn vcap vacc vnm _ t r tv okr JV vEXT) as E1.
  assert (JT : jtail d o vn vcap vacc vnm t r okr = (None, [], okr)).
  { unfold jtail. rewrite <- RX. destruct (rest_at tb text x) as [|c r'] eqn:Er; [reflexivity|].
    destruct (NC c r' eq_refl) as [N1 N2].
    rewrite (proj2 (Z.eqb_neq c 44) N1), (proj2 (Z.eqb_neq c (closer o)) N2). reflexivity. }
  pose proof (ext_eq _ _ _ _ _ _ _ JT E1) as JI. rewrite app_nil_r in JI.
  pose proof vGL as (_ & FK & _).
  assert (FKt : fregs_kept fx fx2) by (intros r0 Hr; rewrite (FK2 r0 Hr); exact (FK r0 Hr)).
  pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  apply (pi_exit fx2 L2 A2 m3 md2 Lam2 peak2 cnt2 fail2 (vtr ++ tv) (vD ++ Dv) R' None okr FZ2 FKt RP3 RD3 LG3 PL' HP'
    NL' NB' PK' RS' CN' FA' RPF JI).
  split; [exact R10F|]. split.
  - apply (pi_after_of m3 x). rewrite pi_seg. exact PX.
  - rewrite vED, <- !app_assoc. rewrite (pis_maxd d vHD).
    apply (pi_fd_store segs mem2 m3 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) (map snd (rev vacc)) (map fst (rev vacc))
      vDi (MAXD - S d) vDn Dv q).
    + rewrite v_ts. exact PO2.
    + rewrite v_ts. pose proof v_lt. lia.
    + exact vDEP.
    + rewrite v_ts. apply (pj_fd_mono segs mem2 (lin Lam2) (depth t)); [exact DT|]. exact (pj_node_fd segs t mem2 (lin Lam2) _ Dv HT).
    + destruct (Bool.bool_dec o true) as [Eo|Eo].
      * rewrite Eo in KY2 |- *. cbv beta iota in KY2 |- *. destruct KY2 as (x0 & k & -> & Hu & Hc).
        cbn [pj_key]. exists x0. split; [rewrite v_ts; exact Hu | right; exists k; split; [exact (proj1 Hc) | reflexivity]].
      * assert (Eo' : o = false) by (destruct o; [contradiction | reflexivity]). rewrite Eo' in KY2 |- *. exact KY2.
    + pose proof (pi_D_nodup L2 A2 m3 Lam2 _ _ _ (vD ++ Dv) LG3 PL') as ND. rewrite vED, <- !app_assoc in ND. exact ND.
    + apply (pi_apart_new L2 A2 m3 md2 Lam2 _ _ _ (vDn ++ Dv) RP3 LG3).
      * intros b Hb. apply (Permutation_in _ (Permutation_sym PL')). apply in_or_app. left. rewrite vED.
        apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        -- apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hb.
        -- apply in_or_app. right. exact Hb.
      * intros a k Hb. apply NB'. rewrite vED. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        -- apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hb.
        -- apply in_or_app. right. exact Hb.
    + rewrite v_ts. pose proof PO2 as (_ & _ & Hh2 & (_ & HNC & _) & _).
      apply (pis_hdr_n segs mem2 m3 v _ _ _ _ _ _ _ (Z.of_nat vn + 1) Hh2); [lia | rewrite pi_seg; exact BV3 | |].
      * intros x0 Hx Hx'. exact (proj1 (MB3 x0 ltac:(lia) Hx' ltac:(lia))).
      * intros x0 _ Hw. unfold writable_at in Hw |- *. rewrite pi_seg in Hw |- *. exact (WM3 _ Hw).
    + intros b x0 Hb Hx. assert (HbL : In b Lam2).
      { assert (HbD : In b (vD ++ Dv)) by (rewrite vED, <- !app_assoc; exact Hb).
        apply (Permutation_in _ (Permutation_sym PL')). apply in_or_app. left. exact HbD. }
      destruct b as (a & k). unfold pj_holds in Hx; cbn [fst snd] in Hx.
      pose proof LG3 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ HbL) as (Lk & _). cbn [fst snd] in Lk.
      destruct (ledger_block_range B API L2 A2 m3 md2 Lam2 _ _ _ a k M3 LG3 HbL) as (R1 & R2 & _).
      pose proof rk_ceil. pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _). pose proof pi_K80. lia.
    + intros x0 Hx Hv Hq. apply MB3; lia.
Qed.

Lemma v_arm_close : forall fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv okr Dv m3 x R',
  frm_zero (@fp_csr fx2) -> fregs_kept vfx fx2 ->
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok) = (Some (t, r), tv, okr) ->
  cnt2 = cnt0 + Z.of_nat (calls vtr) + Z.of_nat (calls tv) ->
  fail_after (cnt0 + Z.of_nat (calls vtr)) fail0 (calls tv) fail2 ->
  Permutation Lam2 (Dv ++ vLam) -> Permutation (map snd Dv) (map Z.of_nat (lsz tv)) ->
  Z.of_nat (length Dv) = nlive tv -> new_blks vL vA Dv ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak vtr)) (lsum vLam + hpeak tv) ->
  rf_ok RF A2 (rf_run RF (rf_run RF b0 vtr) tv) ->
  pj_node segs mem2 (lin Lam2) vsl t Dv ->
  chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] mem2 m3 ->
  bytes_at rsegs m3 (v + 40) (le8 (Z_to_bv 64 (Z.of_nat vn + 1))) ->
  skip r = closer o :: rest_at tb text (x + 1) ->
  pj_in_ok rsegs m3 q text len (x + 1) (Z.of_nat d + 1 - 1) tb ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 0 ->
  pi_post (mkCfg (@mkst fx2 R' (getr regs0 1) m3 (seg_rom segs)) md2).
Proof.
  intros fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv okr Dv m3 x R' FZ2 FK2 RP2 RD2 LG2 JV CN2 FA2 PL2 HP2 NL2
    NB2 PK2 RS2 HT CH3 BV3 SK PX RPF R10F.
  destruct (v_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 PL2 NB2) as (RPc & FR2 & AUX2 & CS2 & PO2 & KY2).
  destruct (v_glue A2 Lam2 peak2 cnt2 fail2 tv Dv PL2 HP2 NL2 NB2 PK2 CN2 FA2 RS2)
    as (PL' & HP' & NL' & NB' & PK' & RS' & CN' & FA').
  destruct (pi_kA3 L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 (vD ++ Dv) RPc RD2 LG2 PL' NB' FR2 AUX2 CH3)
    as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  pose proof (pi_jval_some vtr vn vcap vacc vnm _ t r tv okr JV vEXT) as E1.
  assert (JT : jtail d o vn vcap vacc vnm t r okr =
               (Some (mk o (rev ((vnm, t) :: vacc)), rest_at tb text (x + 1)), [], okr)).
  { unfold jtail. rewrite SK. assert (C44 : (closer o =? 44) = false) by (destruct o; reflexivity).
    rewrite C44, Z.eqb_refl. reflexivity. }
  pose proof (ext_eq _ _ _ _ _ _ _ JT E1) as JI. rewrite app_nil_r in JI.
  pose proof vGL as (_ & FK & _).
  assert (FKt : fregs_kept fx fx2) by (intros r0 Hr; rewrite (FK2 r0 Hr); exact (FK r0 Hr)).
  apply (pi_exit fx2 L2 A2 m3 md2 Lam2 peak2 cnt2 fail2 (vtr ++ tv) (vD ++ Dv) R'
    (Some (mk o (rev ((vnm, t) :: vacc)), rest_at tb text (x + 1))) okr FZ2 FKt RP3 RD3 LG3 PL' HP' NL' NB' PK' RS' CN' FA'
    RPF JI).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PX) as (_ & _ & _ & XB & _ & _ & TL & _).
  split; [exact R10F|]. split.
  - rewrite (pi_rest_len tb text len (x + 1) TL XB).
    replace (text + len - (text + len - (x + 1))) with (x + 1) by lia.
    replace (Z.of_nat d) with (Z.of_nat d + 1 - 1) by lia. rewrite pi_seg. exact PX.
  - rewrite vED, <- !app_assoc.
    apply (pis_close segs m3 (lin Lam2) v o vnum vkids vkeys (Z.of_nat vcap) ((vnm, t) :: vacc) (vDi ++ vDn ++ Dv)).
    replace (Z.of_nat (length ((vnm, t) :: vacc))) with (Z.of_nat (S vn)) by (cbn [length]; rewrite vLA; reflexivity).
    exact (v_snoc3 L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv t m3 RP2 RD2 LG2 PL2 NB2 HT CH3 BV3).
Qed.

Lemma v_arm_comma : forall w fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv Dv m3 x R'',
  (length (rest_at tb text vP) <= w)%nat ->
  frm_zero (@fp_csr fx2) -> fregs_kept vfx fx2 ->
  rpost B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd (rd_writes q vsl Dv) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  jr_value jr_strtod (S d) (rest_at tb text vP) (skipn (calls vtr) pi_ok) =
    (Some (t, r), tv, skipn (calls tv) (skipn (calls vtr) pi_ok)) ->
  cnt2 = cnt0 + Z.of_nat (calls vtr) + Z.of_nat (calls tv) ->
  fail_after (cnt0 + Z.of_nat (calls vtr)) fail0 (calls tv) fail2 ->
  Permutation Lam2 (Dv ++ vLam) -> Permutation (map snd Dv) (map Z.of_nat (lsz tv)) ->
  Z.of_nat (length Dv) = nlive tv -> new_blks vL vA Dv ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak vtr)) (lsum vLam + hpeak tv) ->
  rf_ok RF A2 (rf_run RF (rf_run RF b0 vtr) tv) ->
  pj_node segs mem2 (lin Lam2) vsl t Dv ->
  chg [(v + 40, v + 48); (q, q + 8)] mem2 m3 -> bytes_at rsegs m3 (v + 40) (le8 (Z_to_bv 64 (Z.of_nat vn + 1))) ->
  skip r = 44 :: rest_at tb text (x + 1) ->
  pj_in_ok rsegs m3 q text len (x + 1) (Z.of_nat d + 1) tb ->
  pi_cs R'' -> getr R'' 1 = Z_to_bv 64 0x15214 -> getr R'' 10 = Z_to_bv 64 v ->
  pi_gc w (mkCfg (@mkst fx2 R'' (Z_to_bv 64 0x147e8) m3 (seg_rom segs)) md2).
Proof.
  intros w fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv Dv m3 x R'' HW FZ2 FK2 RP2 RD2 LG2 JV CN2 FA2 PL2 HP2
    NL2 NB2 PK2 RS2 HT CH3 BV3 SK PX CS'' G1'' G10''.
  destruct (v_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 PL2 NB2) as (RPc & FR2 & AUX2 & CS2 & PO2 & KY2).
  destruct (v_glue A2 Lam2 peak2 cnt2 fail2 tv Dv PL2 HP2 NL2 NB2 PK2 CN2 FA2 RS2)
    as (PL' & HP' & NL' & NB' & PK' & RS' & CN' & FA').
  assert (CH3' : chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] mem2 m3)
    by (eapply chg_weaken; [|exact CH3]; intros z Hz; cbn [outside] in Hz |- *; tauto).
  destruct (pi_kA3 L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 (vD ++ Dv) RPc RD2 LG2 PL' NB' FR2 AUX2 CH3')
    as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  destruct (v_vspec t r tv _ JV) as (Hr & Hc & Hsuf & DT).
  pose proof (v_succ (t, r) tv _ JV) as NF'.
  pose proof (skip_len r) as SL. rewrite SK in SL. cbn [length] in SL.
  pose proof (pi_jval_some vtr vn vcap vacc vnm _ t r tv _ JV vEXT) as E1.
  assert (JT : forall ok, jtail d o vn vcap vacc vnm t r ok =
                jturn d o (S vn) vcap ((vnm, t) :: vacc) (rest_at tb text (x + 1)) ok).
  { intros ok. unfold jtail. rewrite SK, Z.eqb_refl. reflexivity. }
  rewrite JT, skipn_skipn in E1.
  destruct (agrees_some _ _ _ _ _ _ (agrees_jr_value jr_strtod (S d) (rest_at tb text vP)) JV) as (J0 & _).
  pose proof vROOM as RM. unfold jval in RM.
  rewrite (bind_nil_trace _ _ _ _ (t, r) tv (agrees_jr_value jr_strtod (S d) _) J0) in RM.
  cbv beta in RM. cbn [fst snd] in RM. rewrite JT in RM.
  destruct (room_run_app RF tv (rf_run RF b0 vtr) _ RM) as [_ RM2].
  pose proof vGL as (_ & FK & _).
  assert (FKt : fregs_kept fx fx2) by (intros r0 Hr0; rewrite (FK2 r0 Hr0); exact (FK r0 Hr0)).
  exists fx2, R'', m3, md2, L2, A2, Lam2, (vtr ++ tv), (vD ++ Dv), (S vn), vcap, ((vnm, t) :: vacc), (x + 1), vnum, vkids,
    vkeys, (vDi ++ vDn ++ Dv).
  split; [reflexivity|]. split; [exact vHD|]. split; [exact CS''|]. split; [exact G1''|]. split; [exact G10''|].
  split.
  { split; [exact FZ2|]. split; [exact FKt|]. split; [exact RP3|]. split; [exact RD3|]. split; [exact FR3|].
    split; [exact PL'|]. split; [exact HP'|]. split; [exact NL'|]. split; [exact NB'|].
    split; [exact RS' | exact AUX3]. }
  split; [rewrite PK', CN', (proj2 FA' NF') in LG3; exact LG3|].
  split; [exact NF'|].
  split; [rewrite pi_seg; exact PX|].
  split; [lia|].
  split; [rewrite calls_app, Nat2Z.inj_add; pose proof vCB; lia|].
  split; [rewrite calls_app, Nat.add_comm; exact E1|].
  split; [rewrite rf_run_app; exact RM2|].
  split; [cbn [length]; rewrite vLA; reflexivity|].
  split; [exact vINV|].
  split; [rewrite vED, <- !app_assoc; reflexivity|].
  split; [exact (v_snoc3 L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv t m3 RP2 RD2 LG2 PL2 NB2 HT CH3' BV3)|].
  cbn [rev]. rewrite map_app. apply Forall_app. split; [exact vDEP|]. constructor; [exact DT | constructor].
Qed.

Lemma pi_val_core : forall w, (length (rest_at tb text vP) <= w)%nat ->
  SR segs (mkCfg (@mkst vfx vR (Z_to_bv 64 0x14330) vm (seg_rom segs)) vmd) (pi_next w).
Proof using All.
  intros w HW.
  pose proof (pi_K_bounds vHD) as (_ & _ & _ & KV & _ & _ & _ & KV0).
  pose proof vGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP as (M & _ & _ & Y & _).
  pose proof (pi_sp vR vCS) as SP. pose proof v_lt as LT. pose proof v_kids_rng as KR.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ vPIN) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (_ & _ & _ & TP0 & _).
  assert (ENVv : reader_env (fx := vfx) B API (PARSE_VALUE_K (S d)) vL vA vR vm vmd).
  { apply (pi_env vfx vL vA vm vmd vLam vtr vD vR _ vGL vCS); [|exact KV | exact KV0].
    rewrite vG1. apply YK0s.ret_ok_even. vm_compute. reflexivity. }
  assert (PINv : pj_in_ok segs vm q text len vP (Z.of_nat (S d)) tb) by (rewrite Nat2Z.inj_succ; exact vPIN).
  assert (QSPv : spZ vR <= q) by (rewrite SP; unfold pi_f; lia).
  assert (AUXq : st_init_done vA = false -> auxv_pre B (ly_sec vL) (q + 24) vm).
  { intros HDn. destruct Y as (_ & Hsec & _). rewrite Hsec.
    apply (auxv_pre_mono B _ pi_lo); [unfold pi_lo; lia | exact (AUX HDn)]. }
  assert (TOKv : text_ok B vL vA vLam vR text len) by exact (pi_text_ok vfx vL vA vm vmd vLam vtr vD vR _ _ _ vGL vLG SP).
  assert (SNZ : vsl <> 0) by lia.
  assert (RPs : rplace B vL vA vLam vR vm vsl)
    by exact (pi_blk_rplace vL vA vm vmd vLam _ _ _ vR _ _ vsl M vLG SP v_kids_in ltac:(lia) ltac:(lia)).
  assert (KB : In (vkids - 16, 56 * Z.of_nat vcap + 16) (blocks vL vA) /\ ~ In (vkids - 16, 56 * Z.of_nat vcap + 16) (blocks L0 A0)).
  { pose proof vLG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
    destruct (LF _ v_kids_in) as (_ & Lin & _). cbn [fst snd] in Lin. split; [exact Lin|].
    apply NB. rewrite vED. apply in_or_app. left. exact v_kids_slot. }
  assert (DJ1 : Frame.disjoint_from [(text, text + len); (q, q + 24)] vsl 56).
  { cbn [Frame.disjoint_from]. split; [|split; [lia | exact I]].
    destruct KB as (KB1 & KB2).
    pose proof (pi_text_new vL vA vm vmd _ _ RP KB1 KB2) as TN.
    destruct (Z_le_gt_dec (text + len) vsl) as [Ha|Ha]; [right; exact Ha|].
    destruct (Z_le_gt_dec (vsl + 56) text) as [Hb|Hb]; [left; exact Hb|].
    exfalso. apply (TN (Z.max text vsl - text) ltac:(lia)). lia. }
  assert (DJ2 : Frame.disjoint_from [(q, q + 24); (text, text + len); (vsl, vsl + 56)]
                  (spZ vR - PARSE_VALUE_K (S d)) (PARSE_VALUE_K (S d))).
  { cbn [Frame.disjoint_from]. rewrite SP. unfold pi_f. lia. }
  assert (CNTv : cnt0 + Z.of_nat (calls vtr) + 2 * Z.of_nat (length (rest_at tb text vP)) + 2 < 2 ^ 64 - 1)
    by (pose proof CNT; pose proof vCB as CB; unfold pi_x in CB; lia).
  assert (ROOMv : room_run RF (rf_run RF b0 vtr) (snd (fst (jr_value jr_strtod (S d) (rest_at tb text vP) []))))
    by (pose proof vROOM as RM; unfold jval in RM; exact (pi_room_bind RF _ _ _ _ _ RM)).
  eapply SR_bind.
  { change (Z_to_bv 64 0x14330) with (Z_to_bv 64 PARSE_VALUE).
    exact (PVC vHD vfx vL vA vR vm vmd vLam _ _ _ _ q text len vP tb vsl ENVv vLG RS vG10 vG11 PINv QSPv AUXq MXR TOKv SNZ
      vZ RPs DJ1 DJ2 CNTv ROOMv). }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & okv & res & tv & okr & Dv & -> & FZ2 & FK2 &
    RP2 & RD2 & LG2 & JV & OKS & CN2 & FA2 & PL2 & HP2 & NL2 & NB2 & PK2 & HPB & RS2 & ARM).
  pose proof (pi_pv_agree vtr _ okv res tv okr JV OKS) as JV'.
  destruct (v_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ Dv RP2 LG2 PL2 NB2) as (RPc & FR2 & AUX2 & CS2 & PO2 & KY2).
  pose proof RP2 as (M2 & _).
  destruct (mr_model B _ (aa_laws API) L2 A2 mem2 md2 M2) as (Hh2 & Hl2 & _).
  pose proof PO2 as (_ & _ & (HRW & _ & _ & _ & _ & _ & (_ & HN40) & _) & (_ & HNC & _) & _).
  pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  assert (HNr : bytes_at rsegs mem2 (v + 40) (le8 (Z_to_bv 64 (Z.of_nat vn)))) by (rewrite <- pi_seg; exact HN40).
  assert (WNr : wr_at rsegs mem2 (v + 40) 8) by (rewrite <- pi_seg; destruct HRW as (_ & HS); apply (pi_wr_stk _ _ _ _ _ _ HS); lia).
  unfold pi_frm in FR2.
  rewrite vG1, pi_seg.
  destruct res as [[t r]|].
  - destruct ARM as (R10s & PINs & HTs & _).
    destruct (v_vspec t r tv _ JV') as (Hr & Hc & Hsuf & DT).
    pose proof (pi_rest_suf tb text len vP r TL ltac:(lia) Hsuf) as RR.
    eapply rk_kA; [exact Hh2 | exact Hl2 | |].
    + rewrite (pi_canon regs2 CS2).
      eapply pip_pv with (p := text + len - Z.of_nat (length r)) (d := Z.of_nat d + 1) (n := Z.of_nat vn) (tb := tb).
      * rewrite <- pi_seg. rewrite Nat2Z.inj_succ in PINs. exact PINs.
      * lia.
      * exact FR2.
      * left. unfold pi_f. lia.
      * exact HNr.
      * exact WNr.
      * lia.
      * lia.
      * cbn [disjoint_from]. unfold pi_f. lia.
    + intros ms' (can & HQ & EQV). destruct HQ as (a1' & a2' & m3 & ARMS & BV3).
      destruct ARMS as [(Hw & -> & CH3 & PX3) | [(Hw & x & -> & HX1 & RX & NC & CH3 & PX3) |
        [(Hw & x & -> & HX1 & SK & CH3 & PX3) | (Hw & x & -> & HX1 & SK & CH3 & PX3)]]].
      * exfalso. assert (E : reg_get regs2 10 = Z_to_bv 64 0) by exact R10s. rewrite E in Hw. apply Hw. reflexivity.
      * rewrite <- pi_seg. eapply pi_ret; [exact EQV|]. intros R' RPF R10F. left.
        rewrite RR in RX.
        exact (v_arm_refuse fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv _ Dv m3 x R' FZ2 FK2 RP2 RD2 LG2 JV' CN2 FA2
          PL2 HP2 NL2 NB2 PK2 RS2 HTs CH3 BV3 RX NC PX3 RPF R10F).
      * rewrite <- pi_seg. eapply pi_ret; [exact EQV|]. intros R' RPF R10F. left.
        rewrite RR in SK.
        exact (v_arm_close fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv _ Dv m3 x R' FZ2 FK2 RP2 RD2 LG2 JV' CN2 FA2
          PL2 HP2 NL2 NB2 PK2 RS2 HTs CH3 BV3 SK PX3 RPF R10F).
      * destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems, <- pi_seg.
        rewrite RR in SK.
        apply (pi_sep w).
        apply (v_arm_comma w fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 t r tv Dv m3 x (ms_regs ms') HW FZ2 FK2 RP2 RD2 LG2
          JV' CN2 FA2 PL2 HP2 NL2 NB2 PK2 RS2 HTs CH3 BV3 SK PX3).
        -- unfold pi_cs. repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]). rewrite (rk_getr_eqv _ _ XR). reflexivity.
        -- rewrite (rk_getr_eqv _ _ XR). reflexivity.
        -- rewrite (rk_getr_eqv _ _ XR). reflexivity.
  - destruct ARM as (R10n & PAn & FDn).
    eapply rk_kA; [exact Hh2 | exact Hl2 | |].
    + rewrite (pi_canon regs2 CS2).
      eapply pip_pv_fail with (n := Z.of_nat vn).
      * assert (E : reg_get regs2 10 = Z_to_bv 64 (-1)) by exact R10n. rewrite E. intros Hc. vm_compute in Hc. discriminate Hc.
      * exact FR2.
      * exact HNr.
      * exact WNr.
      * lia.
      * lia.
      * cbn [disjoint_from]. unfold pi_f. lia.
    + intros ms' (can & HQ & EQV). destruct HQ as (m3 & -> & CH3 & BV3).
      rewrite <- pi_seg. eapply pi_ret; [exact EQV|]. intros R' RPF R10F. left.
      exact (v_arm_fail fx2 L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 tv _ Dv m3 R' FZ2 FK2 RP2 RD2 LG2 JV' CN2 FA2 PL2 HP2 NL2
        NB2 PK2 RS2 PAn FDn CH3 BV3 RPF R10F).
Qed.

End Val.

Lemma pi_val : forall w c, pi_vc w c -> SR segs c (pi_next w).
Proof.
  intros w c (fxc & R & m & mdc & Lc & Ac & Lamc & tr & D & n & cap & acc & P & num & kids & keys & Di & nm & Dn & -> & HD &
    CS & G1 & G10 & G11 & GL & LG & NF & PIN & HW & CB & EXT & RMh & LA & INV & ED & PO & KY & ZR & DEP).
  exact (pi_val_core fxc R m mdc Lc Ac Lamc tr D n cap acc P num kids keys Di nm Dn HD CS G1 G10 G11 GL LG NF PIN CB EXT RMh
    LA INV ED PO KY ZR DEP w HW).
Qed.

Lemma pi_cs_xeq : forall R1 R2, pi_cs R1 -> xregs_eqv R1 R2 -> pi_cs R2.
Proof.
  intros R1 R2 CS XR. unfold pi_cs in *. rewrite !(rk_getr_eqv _ _ XR). exact CS.
Qed.

Lemma pi_ms_run : forall fxc R m mdc (P : config -> Prop) slot n vals,
  pi_cs R -> getr R 1 = Z_to_bv 64 0x1519c -> getr R 10 = Z_to_bv 64 slot -> getr R 11 = Z_to_bv 64 0 ->
  getr R 12 = Z_to_bv 64 56 -> m_halted mdc = None -> m_vm_lazy mdc = [] -> MemNorm.ro_agree rsegs m ->
  stk rsegs m slot (slot + 56) -> (forall i, 0 <= i < 56 -> ~ in_img B (slot + i)) ->
  bytes_at rsegs m (v + 24) (le8 (Z_to_bv 64 vals)) -> bytes_at rsegs m (v + 40) (le8 (Z_to_bv 64 n)) ->
  0 <= n -> 0 <= vals -> vals + 56 * n < 2 ^ 64 -> slot = vals + 56 * n ->
  disjoint_from [(slot, slot + 56)] (v + 24) 8 -> disjoint_from [(slot, slot + 56)] (v + 40) 8 ->
  (forall R' m', pi_cs R' -> getr R' 1 = Z_to_bv 64 0x151bc -> getr R' 10 = Z_to_bv 64 q ->
     getr R' 11 = Z_to_bv 64 slot -> munch [(slot, slot + 56)] m m' -> wmono rsegs m m' -> MemNorm.ro_same rsegs m m' ->
     rw_cells rsegs m' slot [CB 56 (repeat (Z_to_bv 8 0) 56)] ->
     SR segs (mkCfg (@mkst fxc R' (Z_to_bv 64 0x14330) m' (seg_rom segs)) mdc) P) ->
  SR segs (mkCfg (@mkst fxc R (Z_to_bv 64 0x20b28) m (seg_rom segs)) mdc) P.
Proof.
  intros fxc R m mdc P slot n vals CS G1 G10 G11 G12 Hh Hl RO ST NI HV HN Hn Hv Hb Es D24 D40 K.
  pose proof ST as (S0 & S1 & _).
  assert (E1 : reg_get R 1 = Z_to_bv 64 0x1519c) by exact G1.
  assert (E10 : reg_get R 10 = Z_to_bv 64 slot) by exact G10.
  assert (E11 : reg_get R 11 = Z_to_bv 64 0) by exact G11.
  assert (E12 : reg_get R 12 = Z_to_bv 64 56) by exact G12.
  assert (STn : stk rsegs (MemNorm.normalize rsegs m) slot (slot + 56)).
  { apply rk_stk_norm; [|exact ST]. intros a Ha. apply (rk_noimg_fs pi_seg).
    replace a with (slot + (a - slot)) by lia. apply NI. lia. }
  destruct (stk_carve rsegs _ slot (slot + 56) 56 STn ltac:(lia)) as [_ (junk & RJ)].
  replace (slot + 56 - Z.of_nat 56) with slot in RJ by lia.
  pose proof (MemNorm.mem_rel_normalize rsegs m RO) as MR0.
  rewrite pi_seg.
  eapply rk_kA with (Q := fun s => exists s0, (exists R1 m1, s0 = MS R1 (@fp_regs fxc) (Z_to_bv 64 0x14330) (@fp_csr fxc)
      None m1 (seg_rom rsegs) /\ pi_cs R1 /\ getr R1 1 = Z_to_bv 64 0x151bc /\ getr R1 10 = Z_to_bv 64 q /\
      getr R1 11 = Z_to_bv 64 slot /\ munch [(slot, slot + 56)] (MemNorm.normalize rsegs m) m1 /\
      wmono rsegs (MemNorm.normalize rsegs m) m1 /\ rw_cells rsegs m1 slot [CB 56 (repeat (Z_to_bv 8 0) 56)]) /\
      MemNorm.ms_rel rsegs s s0 /\ MemNorm.ro_same rsegs m (ms_mem s)); [exact Hh | exact Hl | |].
  { rewrite (pi_canon R CS). rewrite E1, E10, E11, E12.
    apply (MemNorm.evt_normalize rsegs); [exact rk_wx | exact RO |].
    eapply evt_cut.
    { eapply MSC with (junk := junk).
      - rewrite (MState.unsigned_lit slot) by lia. change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat. exact RJ.
      - apply MemNorm.mem_inv_normalize. }
    intros ms1 POST. unfold memset_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 &
      MI1 & RV1).
    rewrite (MState.unsigned_lit slot) in MU1, RV1 by lia. change (bv_unsigned (Z_to_bv 64 56)) with 56 in MU1.
    change (Z.to_nat (bv_unsigned (Z_to_bv 64 56))) with 56%nat in RV1.
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in RV1.
    replace (ret_pc (Z_to_bv 64 0x1519c)) with (Z_to_bv 64 0x1519c) by (apply bv_eq; vm_compute; reflexivity).
    assert (HV1 : bytes_at rsegs m1 (v + 24) (le8 (Z_to_bv 64 vals))).
    { apply (bytes_at_transport rsegs [(slot, slot + 56)] (MemNorm.normalize rsegs m)); [|exact MU1|].
      - exact (proj1 (MemNorm.bytes_at_rel rsegs m _ _ _ MR0) HV).
      - rewrite length_le8. exact D24. }
    assert (HN1 : bytes_at rsegs m1 (v + 40) (le8 (Z_to_bv 64 n))).
    { apply (bytes_at_transport rsegs [(slot, slot + 56)] (MemNorm.normalize rsegs m)); [|exact MU1|].
      - exact (proj1 (MemNorm.bytes_at_rel rsegs m _ _ _ MR0) HN).
      - rewrite length_le8. exact D40. }
    eapply evt_mono; [eapply pip_ms with (q := q) (v := v) (vals := vals) (n := n); first [exact HV1 | exact HN1 | lia]|].
    intros ms' ->. eexists _, m1. split; [reflexivity|].
    split; [unfold pi_cs; repeat (split; [reflexivity|]); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [rewrite Es; reflexivity|].
    split; [exact MU1|]. split; [exact WM1 | exact RV1]. }
  intros ms' (can & (s0 & (R1 & m1 & -> & CS1 & G1' & G10' & G11' & MU1 & WM1 & RV1) & REL & ROS) & EQV).
  destruct (rk_rel_shape _ _ _ _ _ _ REL EQV) as (Ems & XR & MR1).
  rewrite Ems, <- pi_seg.
  apply K.
  - exact (pi_cs_xeq R1 _ CS1 XR).
  - rewrite (rk_getr_eqv _ _ XR). exact G1'.
  - rewrite (rk_getr_eqv _ _ XR). exact G10'.
  - rewrite (rk_getr_eqv _ _ XR). exact G11'.
  - exact (MemNorm.munch_rel rsegs _ _ _ _ _ MR0 MR1 ROS MU1).
  - exact (MemNorm.wmono_rel rsegs _ _ _ _ MR0 MR1 ROS WM1).
  - exact ROS.
  - exact (rk_rw_cells_rel _ _ _ _ MR1 RV1).
Qed.

Definition pi_mc (w : nat) (c : config) : Prop :=
  exists (fxc : YK11.FPState) (R : bvmap 5 word) (m : word -> option byte) (mdc : Model) (Lc : layout) (Ac : astate)
    (Lamc : list (Z * Z)) (tr : list ev) (D : list (Z * Z)) (n cap : nat) (acc : list (list Z * jv))
    (P num kids keys : Z) (Di : list (Z * Z)) (nm : list Z) (Dn : list (Z * Z)),
    c = mkCfg (@mkst fxc R (Z_to_bv 64 0x20b28) m (seg_rom segs)) mdc /\
    (d < MAXD)%nat /\ pi_cs R /\ getr R 1 = Z_to_bv 64 0x1519c /\
    getr R 10 = Z_to_bv 64 (kids + 56 * Z.of_nat n) /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 56 /\
    pi_glob fxc Lc Ac m mdc Lamc tr D /\
    ledger B Lc Ac m Lamc (Z.max peak0 (lsum Lam0 + hpeak tr)) (cnt0 + Z.of_nat (calls tr)) fail0 /\
    ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls tr)) /\
    pj_in_ok segs m q text len P (Z.of_nat d + 1) tb /\
    (length (rest_at tb text P) <= w)%nat /\
    Z.of_nat (calls tr) + 2 * Z.of_nat (length (rest_at tb text P)) <= 2 * Z.of_nat (length pi_x) /\
    ext (jr_items jr_strtod d o pi_x pi_ok) tr (jval d o n cap acc nm (rest_at tb text P) (skipn (calls tr) pi_ok)) /\
    room_run RF (rf_run RF b0 tr) (snd (fst (jval d o n cap acc nm (rest_at tb text P) []))) /\
    length acc = n /\ inv (S n) cap /\
    D = pis_slots o kids keys (Z.of_nat cap) ++ Di ++ Dn /\
    pis_open segs m (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) (map snd (rev acc)) (map fst (rev acc)) Di /\
    (if o then exists x k, Dn = [(x, k)] /\ pj_u64 segs m (keys + 8 * Z.of_nat n) x /\ pj_cstr segs m (lin Lamc) x k nm
     else Dn = []) /\
    Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev acc)).

Lemma pi_mc_val : forall w c, pi_mc w c -> SR segs c (pi_next w).
Proof.
  intros w c (fxc & R & m & mdc & Lc & Ac & Lamc & tr & D & n & cap & acc & P & num & kids & keys & Di & nm & Dn & -> & HD &
    CS & G1 & G10 & G11 & G12 & GL & LG & NF & PIN & HW & CB & EXT & RMh & LA & INV & ED & PO & KY & DEP).
  pose proof GL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP as (M & _).
  destruct (mr_model B _ (aa_laws API) Lc Ac m mdc M) as (Hh & Hl & _).
  pose proof RD as (RO & _).
  assert (LT : (n < cap)%nat) by (destruct INV as (H & _); lia).
  pose proof PO as (HN & HA & Hh0 & (_ & HNC & _) & _).
  pose proof Hh0 as ((HRW & _) & _ & _ & _ & (_ & HK24) & _ & (_ & HN40) & _).
  assert (KS : In (kids, 56 * Z.of_nat cap) (pis_slots o kids keys (Z.of_nat cap))).
  { unfold pis_slots, kids_blk. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia.
    apply in_or_app. left. left. reflexivity. }
  assert (SL : incl (pis_slots o kids keys (Z.of_nat cap) ++ Di) Lamc)
    by exact (pis_open_incl segs m Lamc v o num kids keys _ _ _ _ Di PO).
  assert (KL : In (kids, 56 * Z.of_nat cap) Lamc) by (apply SL; apply in_or_app; left; exact KS).
  destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ _ _ M LG KL) as (KR1 & KR2 & _).
  pose proof (ledger_block_aligned B API Lc Ac m mdc Lamc _ _ _ _ _ M LG KL) as KR3.
  pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _).
  pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN) as (Q0 & Q1 & _).
  assert (KAP : forall x, kids <= x < kids + 56 * Z.of_nat cap -> ~ (v <= x < v + 56))
    by (intros x Hx; apply (HA (kids, 56 * Z.of_nat cap) x); [apply in_or_app; left; exact KS | unfold pj_holds; cbn [fst snd]; lia]).
  assert (ST : stk rsegs m (kids + 56 * Z.of_nat n) (kids + 56 * Z.of_nat n + 56)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (ledger_block_present B API Lc Ac m mdc Lamc _ _ _ kids _ (a - kids) M LG KL ltac:(lia)) as (b & Hb).
    replace (kids + (a - kids)) with a in Hb by lia.
    split; [unfold wview, wa; rewrite Hb; discriminate|].
    exists b. unfold lib.Lib.Mem.mrd, wa. rewrite Hb. reflexivity. }
  assert (NI : forall i, 0 <= i < 56 -> ~ in_img B (kids + 56 * Z.of_nat n + i)).
  { intros i Hi. replace (kids + 56 * Z.of_nat n + i) with (kids + (56 * Z.of_nat n + i)) by lia.
    exact (ledger_block_not_img B Lc Ac m Lamc _ _ _ kids (56 * Z.of_nat cap) (56 * Z.of_nat n + i) LG KL ltac:(lia)). }
  apply (pi_ms_run fxc R m mdc (pi_next w) (kids + 56 * Z.of_nat n) (Z.of_nat n) kids CS G1 G10 G11 G12 Hh Hl
    ltac:(rewrite <- pi_seg; exact RO) ST NI ltac:(rewrite <- pi_seg; exact HK24) ltac:(rewrite <- pi_seg; exact HN40));
    [lia | lia | lia | reflexivity | | |].
  { cbn [disjoint_from]. split; [|exact I].
    destruct (Z_le_gt_dec (v + 24 + 8) (kids + 56 * Z.of_nat n)) as [Ha|Ha]; [left; exact Ha|].
    destruct (Z_le_gt_dec (kids + 56 * Z.of_nat n + 56) (v + 24)) as [Hb|Hb]; [right; exact Hb|].
    exfalso. apply (KAP (Z.max (v + 24) (kids + 56 * Z.of_nat n))); lia. }
  { cbn [disjoint_from]. split; [|exact I].
    destruct (Z_le_gt_dec (v + 40 + 8) (kids + 56 * Z.of_nat n)) as [Ha|Ha]; [left; exact Ha|].
    destruct (Z_le_gt_dec (kids + 56 * Z.of_nat n + 56) (v + 40)) as [Hb|Hb]; [right; exact Hb|].
    exfalso. apply (KAP (Z.max (v + 40) (kids + 56 * Z.of_nat n))); lia. }
  intros R' m' CS' G1' G10' G11' MU WM ROS RV.
  assert (WM' : wmono segs m m') by (rewrite pi_seg; exact WM).
  assert (MS : forall x, 0 <= x < 2 ^ 64 -> ~ (kids + 56 * Z.of_nat n <= x < kids + 56 * Z.of_nat n + 56) ->
                 pis_same segs m m' x).
  { intros x Hx Hs. assert (Ho : outside [(kids + 56 * Z.of_nat n, kids + 56 * Z.of_nat n + 56)] x)
      by (cbn [outside]; split; [lia | exact I]).
    split; [exact (MemNorm.mbyte_munch _ _ _ _ x MU Hx Ho) | intros Hw; exact (proj1 (rk_writable_munch _ _ m m' x MU Hx Ho) Hw)]. }
  assert (NOTSL : forall a k x, In (a, k) Lamc -> (a, k) <> (kids, 56 * Z.of_nat cap) -> a <= x < a + k ->
                    pis_same segs m m' x).
  { intros a k x Hb Hne Hx.
    destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ a k M LG Hb) as (R1 & R2 & _).
    pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF. destruct (LF _ Hb) as (Lk & _). cbn [fst snd] in Lk.
    apply MS; [lia|].
    destruct (pi_lam_disj Lc Ac m mdc Lamc _ _ _ a k _ _ M LG Hb KL Hne); lia. }
  assert (HWA : forall x, 0 <= x < 2 ^ 64 -> ~ outside [(kids + 56 * Z.of_nat n, kids + 56 * Z.of_nat n + 56)] x ->
                  ~ in_img B x /\ ~ owned B Lc Ac x /\ (pi_E0 x \/ pi_fresh x)).
  { intros x Hx Ho. cbn [outside] in Ho. assert (Hs : kids + 56 * Z.of_nat n <= x < kids + 56 * Z.of_nat n + 56) by tauto.
    split; [replace x with (kids + 56 * Z.of_nat n + (x - (kids + 56 * Z.of_nat n))) by lia; apply NI; lia|].
    split.
    - pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ KL) as (_ & Lin & _). cbn [fst snd] in Lin.
      destruct (rk_blk_facts Lc Ac m mdc _ _ M Lin) as (_ & _ & B3).
      replace x with (kids - 16 + (x - (kids - 16))) by lia. exact (proj2 (B3 (x - (kids - 16)) ltac:(lia))).
    - right. apply (pi_fresh_D Lc Ac m mdc Lamc _ _ _ D x RP LG PERM NB).
      exists kids, (56 * Z.of_nat cap). split; [rewrite ED; apply in_or_app; left; exact KS | lia]. }
  assert (RP' : rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) Lc Ac regs0 m' mdc)
    by exact (pi_rp_A Lc Ac m mdc m' _ RP MU WM' HWA).
  apply (pi_val w).
  exists fxc, R', m', mdc, Lc, Ac, Lamc, tr, D, n, cap, acc, P, num, kids, keys, Di, nm, Dn.
  split; [reflexivity|]. split; [exact HD|]. split; [exact CS'|]. split; [exact G1'|]. split; [exact G10'|].
  split; [exact G11'|].
  split.
  { split; [exact FZ|]. split; [exact FK|]. split; [exact RP'|].
    split; [exact (pi_rd_munch m m' _ RD MU (fun x Hx Ho => proj1 (HWA x Hx Ho)))|].
    split.
    { unfold pi_frm in FR |- *.
      apply (pi_frame_mv m m' pi_f _ _ _ _ _ _ _ _ _ _ FR); [|unfold pi_f; lia | unfold pi_f; lia].
      intros x Hx. rewrite <- pi_seg. unfold pi_f in Hx. refine (proj1 (MS x ltac:(lia) _)). lia. }
    split; [exact PERM|]. split; [exact HP|]. split; [exact NL|]. split; [exact NB|]. split; [exact RS|].
    intros HDn. apply (rk_auxv_keep (ly_sec L0) pi_lo m m' (AUX HDn)).
    - intros i Hi.
      assert (So : owned B Lc Ac (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M So) as Lo.
      refine (proj1 (MS (ms_libc B + 8 + i) ltac:(lia) _)). intros Hs.
      pose proof LG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ KL) as (_ & Lin & _). cbn [fst snd] in Lin.
      destruct (rk_blk_facts Lc Ac m mdc _ _ M Lin) as (_ & _ & B3).
      apply (proj2 (B3 (ms_libc B + 8 + i - (kids - 16)) ltac:(lia))).
      replace (kids - 16 + (ms_libc B + 8 + i - (kids - 16))) with (ms_libc B + 8 + i) by lia. exact So.
    - intros a Ha. unfold pi_lo in Ha. refine (proj1 (MS a ltac:(lia) _)). lia. }
  split.
  { apply (rk_ledger_keep Lc Ac m m' Lamc _ _ _ LG).
    - intros a Ha. pose proof (pi_statics_img a Ha) as Hi. pose proof (rk_img_bound pi_seg a Hi) as Ra.
      refine (proj1 (MS a ltac:(lia) _)). intros Hs. apply (NI (a - (kids + 56 * Z.of_nat n)) ltac:(lia)).
      replace (kids + 56 * Z.of_nat n + (a - (kids + 56 * Z.of_nat n))) with a by lia. exact Hi.
    - intros a k i HIn Hi.
      destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ a k M LG HIn) as (R1 & R2 & _).
      pose proof LG as (_ & _ & _ & _ & _ & LF0). rewrite Forall_forall in LF0.
      destruct (LF0 _ HIn) as (Lk0 & _). cbn [fst snd] in Lk0.
      refine (proj1 (MS (a - 16 + i) ltac:(lia) _)).
      destruct (Z.eq_dec a kids) as [->|Ne]; [lia|].
      assert (Hne : (a, k) <> (kids, 56 * Z.of_nat cap)) by (intros E; injection E as E1 _; exact (Ne E1)).
      destruct (pi_lam_disj Lc Ac m mdc Lamc _ _ _ a k _ _ M LG HIn KL Hne); lia. }
  split; [exact NF|].
  split.
  { apply (pi_in_mv segs m m' q text len P (Z.of_nat d + 1) tb PIN); [|exact (pi_text Lc Ac m' mdc RP')].
    intros x Hx. apply MS; lia. }
  split; [exact HW|]. split; [exact CB|]. split; [exact EXT|]. split; [exact RMh|]. split; [exact LA|].
  split; [exact INV|]. split; [exact ED|].
  pose proof (pi_D_nodup _ _ _ _ _ _ _ D LG PERM) as DND. rewrite ED in DND.
  split.
  { apply (pis_frame segs m (lin Lamc) m' (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) _ _ Di num
      (Z.of_nat n) PO).
    - apply (pis_hdr_frame segs m m' v _ _ _ _ _ _ _ Hh0). intros x Hx. apply MS; [lia|].
      intros Hs. apply (KAP x); [lia | exact Hx].
    - lia.
    - intros a k Hak. exact (SL _ Hak).
    - intros x [Hx|[(Eo & Hx)|((a & k) & Hb & Hx)]].
      + rewrite length_map, length_rev, LA in Hx. apply MS; lia.
      + rewrite length_map, length_rev, LA in Hx.
        assert (YS : In (keys, 8 * Z.of_nat cap) (pis_slots o kids keys (Z.of_nat cap))).
        { unfold pis_slots, kids_blk, keys_blk. rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia.
          cbn. right. left. reflexivity. }
        apply (NOTSL keys (8 * Z.of_nat cap) x (SL _ ltac:(apply in_or_app; left; exact YS))); [|lia].
        intros E. pose proof (pis_nodup_l _ _ _ HN) as N0. unfold pis_slots, kids_blk, keys_blk in N0.
        rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) in N0 by lia. cbn in N0. rewrite E in N0.
        apply NoDup_ListNoDup in N0. inversion N0 as [|? ? Hn0 _]. apply Hn0. left. reflexivity.
      + unfold pj_holds in Hx; cbn [fst snd] in Hx.
        apply (NOTSL a k x (SL _ ltac:(apply in_or_app; right; exact Hb))); [|exact Hx].
        intros E. rewrite E in Hb. exact (pis_nodup_app_disj _ _ _ _ HN KS Hb). }
  split.
  { destruct (Bool.bool_dec o true) as [Eo|Eo].
    - rewrite Eo in KY |- *. cbv beta iota in KY |- *. destruct KY as (x & k & -> & Hu & Hc). exists x, k.
      split; [reflexivity|].
      assert (YS : In (keys, 8 * Z.of_nat cap) (pis_slots o kids keys (Z.of_nat cap))).
      { unfold pis_slots, kids_blk, keys_blk. rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia.
        cbn. right. left. reflexivity. }
      assert (YK : (keys, 8 * Z.of_nat cap) <> (kids, 56 * Z.of_nat cap)).
      { intros E. pose proof (pis_nodup_l _ _ _ HN) as N0. unfold pis_slots, kids_blk, keys_blk in N0.
        rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) in N0 by lia. cbn in N0. rewrite E in N0.
        apply NoDup_ListNoDup in N0. inversion N0 as [|? ? Hn0 _]. apply Hn0. left. reflexivity. }
      split.
      + apply (pis_u64_frame segs m m' _ x Hu). intros y Hy.
        exact (proj1 (NOTSL keys (8 * Z.of_nat cap) y (SL _ ltac:(apply in_or_app; left; exact YS)) YK ltac:(lia))).
      + pose proof Hc as (Hl0 & _ & _).
        apply (pis_cstr_frame segs m (lin Lamc) m' (lin Lamc) x k nm Hc Hl0). intros y Hy.
        unfold pj_holds in Hy; cbn [fst snd] in Hy.
        refine (proj1 (NOTSL x k y Hl0 _ Hy)).
        intros E. apply (pis_nodup_app_disj _ _ _ (kids, 56 * Z.of_nat cap) DND KS).
        rewrite <- E. apply in_or_app. right. left. reflexivity.
    - assert (Eo' : o = false) by (destruct o; [contradiction | reflexivity]). rewrite Eo' in KY |- *. exact KY. }
  split.
  { assert (STz : stk rsegs m' (kids + 56 * Z.of_nat n) (kids + 56 * Z.of_nat n + 56))
      by exact (stk_of_rw_cells rsegs m' _ _ RV).
    pose proof RV as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
    split; [split; [lia | rewrite pi_seg; exact STz] | rewrite pi_seg; exact Hb]. }
  exact DEP.
Qed.

Lemma pi_rp_nn : forall K L A regs mem md (E : Z -> Prop) gone L' A' regs' mem' md',
  aa_MR API L A mem md ->
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  rpost B API K L A regs mem md (fun x => 0 <= x /\ E x) gone L' A' regs' mem' md'.
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' HM (M & W & Bd & Y & HI & X & G & UB & PA & RP & Dv & H & IM & Kb & C).
  pose proof rk_ceil as HC.
  refine (conj M (conj W (conj Bd (conj Y (conj HI (conj X (conj G (conj UB (conj PA (conj RP (conj Dv
    (conj _ (conj _ (conj _ C)))))))))))))).
  - intros a Ha Hs He. apply H; [exact Ha | exact Hs | intros E1; apply He; split; [lia | exact E1]].
  - intros a Ha Hn Hs He. apply IM; [exact Ha | exact Hn | exact Hs |].
    intros E1; apply He; split; [exact (proj1 (rk_img_bound pi_seg a Ha)) | exact E1].
  - intros p n i Hp Hp' Hi He. apply (Kb p n i Hp Hp' Hi). intros E1. apply He. split; [|exact E1].
    destruct (mr_blocks B _ (aa_laws API) L A mem md p n i HM Hp Hi) as (_ & B1 & _). lia.
Qed.

Lemma pi_ff_rpost : forall L A regs mem md pp kk L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md (free_writes pp kk) L' A' regs' mem' md' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  (st_init_done A' = false -> forall i, 0 <= i < 8 ->
     mbyte segs mem' (ms_libc B + 8 + i) = mbyte segs mem (ms_libc B + 8 + i)) ->
  (length (st_regions A) <= length (st_regions A'))%nat ->
  ublocks_kept L A A' (pp - 16, kk + 16) ->
  rpost B API ALLOC_STACK L A regs mem md (free_writes pp kk) (fun a n => a = pp - 16 /\ n = kk + 16)
    L' A' regs' mem' md'.
Proof.
  intros L A regs mem md pp kk L' A' regs' mem' md' HM (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HI HX HR UK.
  assert (NO : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho.
    - pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
    - pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ H1 Ho). lia. }
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact HI|].
  split; [exact HX|]. split; [exact HR|].
  split; [intros p n Hp Hg; apply (UK p n Hp); intros E; injection E as E1 E2; apply Hg; split; [exact E1 | exact E2]|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
  split.
  { intros a Ha Hs He. destruct (NO a ltac:(lia)) as [N1 N2]. exact (H8 a (or_introl Ha) N1 N2 Hs He). }
  split.
  { intros a Hi Hno Hs He. exact (H8 a (or_intror Hi) (Hno L A mem md HM) (Hno L' A' mem' md' H1) Hs He). }
  split; [intros p n i Hp Hp' Hi _; exact (H9 p n i Hp Hp' Hi)|].
  exact H10.
Qed.

Lemma pi_kAk : forall L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 D2 ka kk sl,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 ->
  Permutation Lam2 (D2 ++ Lam0) -> new_blks L0 A0 D2 -> pi_frm mem2 ->
  (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo mem2) ->
  In (ka, kk) D2 -> ka <= sl -> sl + 8 <= ka + kk ->
  chg [(sl, sl + 8); (q, q + 8)] mem2 m3 ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 m3 md2 /\
  rd_cells B m3 /\ ledger B L2 A2 m3 Lam2 peak2 cnt2 fail2 /\ pi_frm m3 /\
  (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo m3) /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sl <= x < sl + 8) -> ~ (q <= x < q + 24) -> pis_same segs mem2 m3 x).
Proof.
  intros L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 m3 D2 ka kk sl RPc RD2 LG2 PL2 NB2 FR2 AUX2 HK Hk1 Hk2 (MU & WM & PR).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ. pose proof QSP as QS.
  pose proof RPc as (M2 & _).
  assert (HKL : In (ka, kk) Lam2) by (apply (Permutation_in _ (Permutation_sym PL2)); apply in_or_app; left; exact HK).
  destruct (rk_D_facts L2 A2 mem2 md2 Lam2 peak2 cnt2 fail2 D2 Lam0 ka kk M2 LG2 PL2 HK) as (KB & K1 & K2 & K3 & K4).
  destruct (rk_blk_facts L2 A2 mem2 md2 _ _ M2 KB) as (_ & _ & KB3).
  assert (WM' : wmono segs mem2 m3) by (rewrite pi_seg; exact WM).
  assert (INW : forall x, ~ outside [(sl, sl + 8); (q, q + 8)] x -> sl <= x < sl + 8 \/ q <= x < q + 8).
  { intros x Ho. cbn [outside] in Ho.
    destruct (Z_lt_le_dec x sl) as [A1|A1]; destruct (Z_lt_le_dec x (sl + 8)) as [A2'|A2'];
    destruct (Z_lt_le_dec x q) as [A3|A3]; destruct (Z_lt_le_dec x (q + 8)) as [A4|A4];
    first [lia | exfalso; apply Ho; repeat split; lia]. }
  assert (OUT : forall x, ~ (sl <= x < sl + 8) -> ~ (q <= x < q + 24) -> outside [(sl, sl + 8); (q, q + 8)] x).
  { intros x H1 H2. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
  assert (MB : forall x, 0 <= x < 2 ^ 64 -> ~ (sl <= x < sl + 8) -> ~ (q <= x < q + 24) -> pis_same segs mem2 m3 x).
  { intros x Hx H1 H2. pose proof (OUT x H1 H2) as Ho.
    split; [exact (MemNorm.mbyte_munch _ _ _ _ x MU Hx Ho) | intros Hw; exact (proj1 (rk_writable_munch _ _ mem2 m3 x MU Hx Ho) Hw)]. }
  assert (NIW : forall x, 0 <= x < 2 ^ 64 -> ~ outside [(sl, sl + 8); (q, q + 8)] x -> ~ in_img B x).
  { intros x Hx Ho Hi. destruct (INW x Ho) as [Hs|Hq].
    - apply (K4 (x - ka) ltac:(lia)). replace (ka + (x - ka)) with x by lia. exact Hi.
    - pose proof (rk_img_bound pi_seg x Hi). lia. }
  split.
  { apply (pi_rp_A L2 A2 mem2 md2 m3 [(sl, sl + 8); (q, q + 8)] RPc MU WM').
    intros x Hx Ho. split; [exact (NIW x Hx Ho)|]. destruct (INW x Ho) as [Hs|Hq].
    - split; [replace x with (ka - 16 + (x - (ka - 16))) by lia; exact (proj2 (KB3 (x - (ka - 16)) ltac:(lia)))|].
      right. apply (pi_fresh_D L2 A2 mem2 md2 Lam2 _ _ _ D2 x RPc LG2 PL2 NB2). exists ka, kk. split; [exact HK | lia].
    - split; [intros Ho'; pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M2 Ho'); lia|].
      left. right. left. unfold pj_in_set. lia. }
  split; [exact (pi_rd_munch mem2 m3 _ RD2 MU NIW)|].
  split.
  { apply (rk_ledger_keep L2 A2 mem2 m3 Lam2 peak2 cnt2 fail2 LG2).
    - intros a Ha. pose proof (pi_statics_img a Ha) as Hi. pose proof (rk_img_bound pi_seg a Hi) as Ra.
      refine (proj1 (MB a ltac:(lia) _ _)); [|lia].
      intros Hs. apply (K4 (a - ka) ltac:(lia)). replace (ka + (a - ka)) with a by lia. exact Hi.
    - intros a k i HIn Hi.
      destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ a k M2 LG2 HIn) as (R1 & R2 & _).
      pose proof LG2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
      destruct (LF _ HIn) as (Lk & _). cbn [fst snd] in Lk.
      refine (proj1 (MB (a - 16 + i) ltac:(lia) _ _)); [|lia].
      destruct (Z.eq_dec a ka) as [->|Ne]; [lia|].
      assert (Hne : (a, k) <> (ka, kk)) by (intros E; injection E as E1 _; exact (Ne E1)).
      destruct (pi_lam_disj L2 A2 mem2 md2 Lam2 _ _ _ a k ka kk M2 LG2 HIn HKL Hne); lia. }
  split.
  { unfold pi_frm in FR2 |- *.
    apply (pi_frame_mv mem2 m3 pi_f _ _ _ _ _ _ _ _ _ _ FR2); [|unfold pi_f; lia | unfold pi_f; lia].
    intros x Hx. rewrite <- pi_seg. unfold pi_f in Hx. refine (proj1 (MB x ltac:(lia) _ _)); lia. }
  split.
  { intros HD. apply (rk_auxv_keep (ly_sec L0) pi_lo mem2 m3 (AUX2 HD)).
    - intros i Hi.
      assert (So : owned B L2 A2 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ M2 So) as Lo.
      refine (proj1 (MB (ms_libc B + 8 + i) ltac:(lia) _ _)); [|lia].
      intros Hs. apply (proj2 (KB3 (ms_libc B + 8 + i - (ka - 16)) ltac:(lia))).
      replace (ka - 16 + (ms_libc B + 8 + i - (ka - 16))) with (ms_libc B + 8 + i) by lia. exact So.
    - intros a Ha. unfold pi_lo in Ha. refine (proj1 (MB a ltac:(lia) _ _)); lia. }
  exact MB.
Qed.

Lemma pi_blk_keepK : forall K L A regs mem md E L' A' regs' mem' md' a k,
  rpost B API K L A regs mem md E (fun _ _ => False) L' A' regs' mem' md' ->
  In (a, k) (blocks L A) -> In (a, k) (blocks L' A').
Proof.
  intros K L A regs mem md E L' A' regs' mem' md' a k RP Hb. pose proof RP as (_ & _ & _ & _ & _ & _ & _ & UB & PA & _).
  destruct (rk_blk_user L A a k Hb) as (p & Hp & Ep).
  assert (Hp' : In (p, k) (user_blocks A')) by (apply UB; [exact Hp | intros Hf; exact Hf]).
  rewrite <- Ep, <- (PA p k Hp Hp'). exact (rk_blk_of_user L' A' p k Hp').
Qed.

Definition pi_sc (w : nat) (c : config) : Prop :=
  exists (fxc : YK11.FPState) (R : bvmap 5 word) (m : word -> option byte) (mdc : Model) (Lc : layout) (Ac : astate)
    (Lamc : list (Z * Z)) (tr : list ev) (D : list (Z * Z)) (n cap : nat) (acc : list (list Z * jv))
    (P x num kids keys : Z) (Di : list (Z * Z)),
    c = mkCfg (@mkst fxc R (Z_to_bv 64 0x152a4) m (seg_rom segs)) mdc /\
    (d < MAXD)%nat /\ o = true /\ pi_cs R /\ getr R 1 = Z_to_bv 64 0x1511c /\ getr R 10 = Z_to_bv 64 q /\
    pi_glob fxc Lc Ac m mdc Lamc tr D /\
    ledger B Lc Ac m Lamc (Z.max peak0 (lsum Lam0 + hpeak tr)) (cnt0 + Z.of_nat (calls tr)) fail0 /\
    ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls tr)) /\
    pj_in_ok segs m q text len x (Z.of_nat d + 1) tb /\
    text <= P /\ P <= x < text + len /\ skip (rest_at tb text P) = 34 :: rest_at tb text (x + 1) /\
    (length (rest_at tb text P) <= w)%nat /\
    Z.of_nat (calls tr) + 2 * Z.of_nat (length (rest_at tb text P)) <= 2 * Z.of_nat (length pi_x) /\
    ext (jr_items jr_strtod d o pi_x pi_ok) tr (jafter d o n cap acc (rest_at tb text P) (skipn (calls tr) pi_ok)) /\
    room_run RF (rf_run RF b0 tr) (snd (fst (jafter d o n cap acc (rest_at tb text P) []))) /\
    length acc = n /\ inv (S n) cap /\
    D = pis_slots o kids keys (Z.of_nat cap) ++ Di /\
    pis_open segs m (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) (map snd (rev acc)) (map fst (rev acc)) Di /\
    Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev acc)).

Section Str.
Variables (sfx : YK11.FPState) (sR : bvmap 5 word) (sm : word -> option byte) (smd : Model) (sL : layout)
  (sA : astate) (sLam : list (Z * Z)) (str : list ev) (sD : list (Z * Z)) (sn scap : nat)
  (sacc : list (list Z * jv)) (sP sx snum skids skeys : Z) (sDi : list (Z * Z)).
Hypothesis sHD : (d < MAXD)%nat.
Hypothesis sO : o = true.
Hypothesis sCS : pi_cs sR.
Hypothesis sG1 : getr sR 1 = Z_to_bv 64 0x1511c.
Hypothesis sG10 : getr sR 10 = Z_to_bv 64 q.
Hypothesis sGL : pi_glob sfx sL sA sm smd sLam str sD.
Hypothesis sLG : ledger B sL sA sm sLam (Z.max peak0 (lsum Lam0 + hpeak str)) (cnt0 + Z.of_nat (calls str)) fail0.
Hypothesis sNF : ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls str)).
Hypothesis sPIN : pj_in_ok segs sm q text len sx (Z.of_nat d + 1) tb.
Hypothesis sTP : text <= sP.
Hypothesis sPX : sP <= sx < text + len.
Hypothesis sSK : skip (rest_at tb text sP) = 34 :: rest_at tb text (sx + 1).
Hypothesis sCB : Z.of_nat (calls str) + 2 * Z.of_nat (length (rest_at tb text sP)) <= 2 * Z.of_nat (length pi_x).
Hypothesis sEXT :
  ext (jr_items jr_strtod d o pi_x pi_ok) str (jafter d o sn scap sacc (rest_at tb text sP) (skipn (calls str) pi_ok)).
Hypothesis sROOM : room_run RF (rf_run RF b0 str) (snd (fst (jafter d o sn scap sacc (rest_at tb text sP) []))).
Hypothesis sLA : length sacc = sn.
Hypothesis sINV : inv (S sn) scap.
Hypothesis sED : sD = pis_slots o skids skeys (Z.of_nat scap) ++ sDi.
Hypothesis sPO : pis_open segs sm (lin sLam) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
  (map fst (rev sacc)) sDi.
Hypothesis sDEP : Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev sacc)).

Lemma s_lt : (sn < scap)%nat.
Proof. destruct sINV as (H & _). lia. Qed.

Lemma s_ts : length (map snd (rev sacc)) = sn.
Proof. rewrite length_map, length_rev. exact sLA. Qed.

Lemma s_slots_in : incl (pis_slots o skids skeys (Z.of_nat scap) ++ sDi) sLam.
Proof. exact (pis_open_incl segs sm sLam v o snum skids skeys _ _ _ _ sDi sPO). Qed.

Lemma s_kids_slot : In (skids, 56 * Z.of_nat scap) (pis_slots o skids skeys (Z.of_nat scap)).
Proof.
  pose proof s_lt. unfold pis_slots, kids_blk. rewrite (proj2 (Z.eqb_neq (Z.of_nat scap) 0)) by lia.
  apply in_or_app. left. left. reflexivity.
Qed.

Lemma s_keys_slot : o = true -> In (skeys, 8 * Z.of_nat scap) (pis_slots o skids skeys (Z.of_nat scap)).
Proof.
  intros Eo. pose proof s_lt. unfold pis_slots, kids_blk, keys_blk. rewrite Eo.
  rewrite (proj2 (Z.eqb_neq (Z.of_nat scap) 0)) by lia. cbn. right. left. reflexivity.
Qed.

Lemma s_kids_in : In (skids, 56 * Z.of_nat scap) sLam.
Proof. apply s_slots_in. apply in_or_app. left. exact s_kids_slot. Qed.

Lemma s_keys_in : o = true -> In (skeys, 8 * Z.of_nat scap) sLam.
Proof. intros Eo. apply s_slots_in. apply in_or_app. left. exact (s_keys_slot Eo). Qed.

Lemma s_post : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 a nn,
  rpost B API PARSE_STRING_K sL sA sR sm smd (parse_string_writes q a nn) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> incl sLam Lam2 ->
  (forall x, 0 <= x -> a <> 0 -> a - 16 <= x < a + nn ->
     pi_fresh x /\ forall p0 k0, In (p0, k0) (blocks sL sA) -> ~ (p0 <= x < p0 + k0)) ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 /\
  pi_frm mem2 /\ (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo mem2) /\ pi_cs regs2 /\
  pis_open segs mem2 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi /\
  (forall a' k' x, In (a', k') sLam -> a' <= x < a' + k' -> pis_same segs sm mem2 x).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 a nn RPS LG2 INC HW.
  pose proof (pi_K_bounds sHD) as (_ & KS & _ & _ & _ & KS0 & _).
  pose proof sGL as (_ & _ & RP & _ & FR & PERM & _ & _ & NB & _ & AUX).
  pose proof RP as (M & _).
  pose proof (pi_sp sR sCS) as SP.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV. pose proof QSP as QS.
  pose proof RPL as (PL & _ & PNO).
  pose proof (pi_rp_nn _ _ _ _ _ _ _ _ _ _ _ _ _ M RPS) as RP2.
  assert (HE : forall x, 0 <= x /\ parse_string_writes q a nn x -> pi_E0 x \/ pi_fresh x).
  { intros x (Hx0 & _ & [Hq|[Hs|(Ha & Hx)]]).
    - left. right. left. unfold pj_in_set. lia.
    - left. right. right. exact Hs.
    - right. exact (proj1 (HW x Hx0 Ha Hx)). }
  assert (FRx : forall x, 0 <= x /\ parse_string_writes q a nn x ->
                  forall p0 k0, In (p0, k0) (blocks sL sA) -> ~ (p0 <= x < p0 + k0)).
  { intros x (Hx0 & _ & [Hq|[Hs|(Ha & Hx)]]) pz kz Hb Hx'.
    - destruct (rk_blk_facts sL sA sm smd pz kz M Hb) as (_ & B2 & _). lia.
    - destruct (rk_blk_user sL sA pz kz Hb) as (pp & Hp & Ep).
      apply (YL01.ax_blocks_img AX sL sA sm smd pp kz (x - pz) M Hp ltac:(lia)). rewrite Ep.
      replace (pz + (x - pz)) with x by lia. exact (pi_statics_img x Hs).
    - exact (proj2 (HW x Hx0 Ha Hx) pz kz Hb Hx'). }
  assert (RPc : rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2)
    by exact (pi_rp_call sL sA sm smd _ sR _ _ L2 A2 regs2 mem2 md2 RP RP2 SP KS KS0 HE (fun p n _ Hf => Hf)).
  assert (OLD : forall a' k' x, In (a', k') sLam -> a' <= x < a' + k' -> pis_same segs sm mem2 x).
  { intros a' k' x Hb Hx.
    pose proof sLG as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
    destruct (LF _ Hb) as (Lk & Lin & _). cbn [fst snd] in Lk, Lin.
    apply (pi_lam_same sL sA sm smd sLam _ _ _ _ sR _ (fun _ _ => False) L2 A2 regs2 mem2 md2 Lam2 _ _ _ a' k' x sLG RP2
      LG2 Hb (INC _ Hb) (fun Hf => Hf) Hx).
    intros HE2. exact (FRx x HE2 _ _ Lin ltac:(lia)). }
  assert (VS : forall x, v <= x < v + 56 -> pis_same segs sm mem2 x).
  { apply (pi_v_same sL sA sm smd _ sR _ _ L2 A2 regs2 mem2 md2 RP RP2 ltac:(lia)); [|intros a0 k0 _ Hf; exact Hf].
    intros x Hx (Hx0 & _ & [Hq|[Hs|(Ha & Hx')]]).
    - lia.
    - destruct (PNO (x - v) ltac:(lia)) as (_ & N2 & _). apply N2. replace (v + (x - v)) with x by lia. exact Hs.
    - destruct (HW x Hx0 Ha Hx') as ((F1 & _) & F2).
      destruct PL as [(P1 & _) | [(a0 & k0 & Hb0 & _ & Ha0 & Hk0) | (a0 & k0 & Hl & Ha0 & Hk0)]].
      + lia.
      + exact (F2 a0 k0 (pi_blk_keep _ _ _ _ _ _ RP Hb0) ltac:(lia)).
      + pose proof LG0 as (_ & _ & _ & _ & _ & LF0). rewrite Forall_forall in LF0. unfold lin in Hl.
        destruct (LF0 _ Hl) as (_ & Hb0 & _). cbn [fst snd] in Hb0.
        exact (F2 _ _ (pi_blk_keep _ _ _ _ _ _ RP Hb0) ltac:(lia)). }
  pose proof sPO as PO. pose proof PO as (HN & HA & Hh & Hs & Hk & Hi).
  split; [exact RPc|].
  split; [exact (pi_frm_call sL sA sm smd _ sR _ _ L2 A2 regs2 mem2 md2 RP2 ltac:(lia) HE FR)|].
  split; [exact (pi_aux_call sL sA sm smd _ sR _ _ L2 A2 regs2 mem2 md2 RP2 ltac:(lia) HE AUX)|].
  split; [pose proof RPS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RPr & _); exact (pi_cs_rp sR regs2 sCS RPr)|].
  split.
  { apply (pis_frame segs sm (lin sLam) mem2 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) _ _ sDi snum
      (Z.of_nat sn) PO).
    - exact (pis_hdr_frame segs sm mem2 v _ _ _ _ _ _ _ Hh VS).
    - pose proof s_lt. lia.
    - intros a' k' Hak. exact (INC _ (s_slots_in _ Hak)).
    - intros x [Hx|[(Eo & Hx)|((a' & k') & Hb & Hx)]].
      + rewrite s_ts in Hx. apply (OLD skids (56 * Z.of_nat scap) x s_kids_in). pose proof s_lt. lia.
      + rewrite s_ts in Hx. apply (OLD skeys (8 * Z.of_nat scap) x (s_keys_in Eo)). pose proof s_lt. lia.
      + unfold pj_holds in Hx; cbn [fst snd] in Hx.
        apply (OLD a' k' x); [apply s_slots_in; apply in_or_app; right; exact Hb | exact Hx]. }
  exact OLD.
Qed.

Lemma s_fin : forall L3 A3 m3 md3 Lam3 peak3 cnt3 fail3 tn okr xx R',
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L3 A3 regs0 m3 md3 ->
  rd_cells B m3 -> ledger B L3 A3 m3 Lam3 peak3 cnt3 fail3 -> Permutation Lam3 (sD ++ Lam0) ->
  pis_open segs m3 (lin Lam3) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi ->
  jr_name true (rest_at tb text sP) (skipn (calls str) pi_ok) = (None, tn, okr) ->
  peak3 = Z.max peak0 (lsum Lam0 + hpeak (str ++ tn)) -> cnt3 = cnt0 + Z.of_nat (calls (str ++ tn)) ->
  fail_after cnt0 fail0 (calls (str ++ tn)) fail3 -> rf_ok RF A3 (rf_run RF b0 (str ++ tn)) ->
  lsz (str ++ tn) = lsz str -> nlive tn = 0 ->
  pj_in_ok segs m3 q text len xx (Z.of_nat d + 1) tb ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst sfx R' (getr regs0 1) m3 (seg_rom segs)) md3).
Proof.
  intros L3 A3 m3 md3 Lam3 peak3 cnt3 fail3 tn okr xx R' RP3 RD3 LG3 PL3 PO3 JN PK CN FA RS LZ NL0 PX RPF R10F.
  pose proof sGL as (FZ & FK & _ & _ & _ & _ & HP & NL & NB & _).
  assert (JN' : jr_name o (rest_at tb text sP) (skipn (calls str) pi_ok) = (None, tn, okr)) by (rewrite sO; exact JN).
  assert (JI : jr_items jr_strtod d o pi_x pi_ok = (None, str ++ tn, okr)).
  { pose proof sEXT as E. unfold jafter in E. exact (ext_bind_none _ _ _ _ _ _ _ _ _ JN' E). }
  apply (pi_exit sfx L3 A3 m3 md3 Lam3 peak3 cnt3 fail3 (str ++ tn) sD R' None okr FZ FK RP3 RD3 LG3 PL3).
  - rewrite LZ. exact HP.
  - rewrite pi_nlive_app, NL0. lia.
  - exact NB.
  - exact PK.
  - exact RS.
  - exact CN.
  - exact FA.
  - exact RPF.
  - exact JI.
  - split; [exact R10F|]. split; [exact (pi_after_of m3 xx PX)|].
    rewrite sED. apply (pis_exit_open segs m3 (lin Lam3) v o snum skids skeys (Z.of_nat scap) (map snd (rev sacc))
      (map fst (rev sacc)) sDi d); [rewrite s_ts; exact PO3 | exact sHD | exact sDEP].
Qed.

Lemma s_kframe : forall Lam2 L2 A2 m2 md2 peak2 cnt2 fail2 m3,
  aa_MR API L2 A2 m2 md2 -> ledger B L2 A2 m2 Lam2 peak2 cnt2 fail2 -> incl sLam Lam2 ->
  pis_open segs m2 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (skeys + 8 * Z.of_nat sn <= x < skeys + 8 * Z.of_nat sn + 8) ->
     ~ (q <= x < q + 24) -> pis_same segs m2 m3 x) ->
  pis_open segs m3 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi.
Proof.
  intros Lam2 L2 A2 m2 md2 peak2 cnt2 fail2 m3 M2 LG2 INC PO2 MB3.
  pose proof PO2 as (HN & HA & Hh & Hs & Hk & Hi).
  pose proof s_lt as LT.
  pose proof (s_keys_in sO) as HKL.
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof QSP as QS. pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  destruct (ledger_block_range B API L2 A2 m2 md2 Lam2 _ _ _ _ _ M2 LG2 (INC _ HKL)) as (Y1 & Y2 & _).
  assert (BLK : forall a k x, In (a, k) Lam2 -> (a, k) <> (skeys, 8 * Z.of_nat scap) -> a <= x < a + k ->
                  pis_same segs m2 m3 x).
  { intros a k x Hb Hne Hx.
    destruct (ledger_block_range B API L2 A2 m2 md2 Lam2 _ _ _ a k M2 LG2 Hb) as (R1 & R2 & _).
    apply MB3; [lia | | lia].
    destruct (pi_lam_disj L2 A2 m2 md2 Lam2 _ _ _ a k _ _ M2 LG2 Hb (INC _ HKL) Hne); lia. }
  assert (KNE : (skids, 56 * Z.of_nat scap) <> (skeys, 8 * Z.of_nat scap)).
  { intros E. pose proof (pis_nodup_l _ _ _ HN) as N0. unfold pis_slots, kids_blk, keys_blk in N0.
    rewrite sO, (proj2 (Z.eqb_neq (Z.of_nat scap) 0)) in N0 by lia. cbn in N0. rewrite E in N0.
    apply NoDup_ListNoDup in N0. inversion N0 as [|? ? Hn0 _]. apply Hn0. left. reflexivity. }
  apply (pis_frame segs m2 (lin Lam2) m3 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) _ _ sDi snum
    (Z.of_nat sn) PO2).
  - apply (pis_hdr_frame segs m2 m3 v _ _ _ _ _ _ _ Hh). intros x Hx. apply MB3; [lia | | lia].
    intros Hs'. apply (HA (skeys, 8 * Z.of_nat scap) x);
      [apply in_or_app; left; exact (s_keys_slot sO) | unfold pj_holds; cbn [fst snd]; lia | exact Hx].
  - lia.
  - intros a k Hak. exact (pis_open_lblk segs m2 (lin Lam2) v o snum skids skeys _ _ _ _ sDi PO2 a k Hak).
  - intros x [Hx|[(Eo & Hx)|((a & k) & Hb & Hx)]].
    + rewrite s_ts in Hx. apply (BLK skids (56 * Z.of_nat scap) x (INC _ s_kids_in) KNE). lia.
    + rewrite s_ts in Hx. apply MB3; lia.
    + unfold pj_holds in Hx; cbn [fst snd] in Hx.
      apply (BLK a k x (INC _ (s_slots_in _ (in_or_app _ _ _ (or_intror Hb))))); [|exact Hx].
      intros E. rewrite E in Hb. exact (pis_nodup_app_disj _ _ _ _ HN (s_keys_slot sO) Hb).
Qed.

Lemma s_hw_succ : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 a nn,
  rpost B API PARSE_STRING_K sL sA sR sm smd (parse_string_writes q a nn) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> In (a, nn) Lam2 -> new_blks sL sA [(a, nn)] ->
  forall x, 0 <= x -> a <> 0 -> a - 16 <= x < a + nn ->
    pi_fresh x /\ forall pz kz, In (pz, kz) (blocks sL sA) -> ~ (pz <= x < pz + kz).
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 a nn RPS LG2 Hin NBa x Hx0 _ Hx.
  pose proof sGL as (_ & _ & RP & _). pose proof RPS as (M2 & _).
  split.
  - apply (pi_fresh_call sL sA sm smd _ sR _ L2 A2 regs2 mem2 md2 Lam2 _ _ _ [(a, nn)] x RP RPS LG2); [|exact NBa|].
    + intros b [<-|[]]. exact Hin.
    + exists a, nn. split; [left; reflexivity | lia].
  - intros pz kz Hb Hx'.
    pose proof (pi_blk_keepK _ _ _ _ _ _ _ _ _ _ _ _ _ _ RPS Hb) as Hb2.
    pose proof LG2 as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
    destruct (LF _ Hin) as (_ & Lin & _). cbn [fst snd] in Lin.
    assert (Hne : (pz, kz) <> (a - 16, nn + 16)).
    { intros E. apply (NBa a nn (or_introl eq_refl)). rewrite <- E. exact Hb. }
    destruct (rk_pairwise_in _ _ _ _ (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 M2) Hb2 Lin Hne) as [Rd|Rd];
      unfold ranges_disjoint in Rd; cbn [fst snd] in Rd; lia.
Qed.

Lemma s_succ : forall L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3,
  rpost B API PARSE_STRING_K sL sA sR sm smd (parse_string_writes q a nn) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> rf_ok RF A2 b2 ->
  scan (rest_at tb text (sx + 1)) = Some Q -> nn = Z.of_nat Q + 1 -> cnt2 = cnt0 + Z.of_nat (calls str) + 1 ->
  cnt0 + Z.of_nat (calls str) <> fail0 -> decode (rest_at tb text (sx + 1)) = Some (s, r) ->
  Lam2 = (a, nn) :: sLam -> new_blks sL sA [(a, nn)] ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak str)) (lsum sLam + nn) -> fail2 = fail0 ->
  b2 = rf_malloc RF (rf_run RF b0 str) (nn + 16) -> pj_cbytes segs mem2 a s ->
  chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8); (q, q + 8)] mem2 m3 ->
  pi_glob sfx L2 A2 m3 md2 Lam2 (str ++ [EAlloc (S Q)]) (sD ++ [(a, nn)]) /\
  ledger B L2 A2 m3 Lam2 (Z.max peak0 (lsum Lam0 + hpeak (str ++ [EAlloc (S Q)])))
    (cnt0 + Z.of_nat (calls (str ++ [EAlloc (S Q)]))) fail0 /\
  ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls (str ++ [EAlloc (S Q)]))) /\
  pis_open segs m3 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi /\
  pj_cbytes segs m3 a s /\ rest_at tb text (sx + nn + 1) = r /\
  (length r + S Q + 1 <= length (rest_at tb text sP))%nat /\ (length s <= Q)%nat.
Proof.
  intros L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 RPS RD2 LG2 RF2 HQ En Ec Hcf Hdc EL NBa Ep Ef Eb CB CH3.
  subst peak2 cnt2 fail2 b2 Lam2.
  pose proof sGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RPS as (M2 & _).
  pose proof s_lt as LT. pose proof rk_ceil as HC. pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & _).
  pose proof QSP as QS. pose proof pi_K80 as KP.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ sPIN) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  assert (Hin : In (a, nn) ((a, nn) :: sLam)) by (left; reflexivity).
  assert (INC : incl sLam ((a, nn) :: sLam)) by (intros bb Hb; right; exact Hb).
  pose proof (s_hw_succ L2 A2 regs2 mem2 md2 _ _ _ _ a nn RPS LG2 Hin NBa) as HW.
  destruct (s_post L2 A2 regs2 mem2 md2 _ _ _ _ a nn RPS LG2 INC HW) as (RPc & FR2 & AUX2 & CS2 & PO2 & OLD).
  destruct (ledger_block_range B API L2 A2 mem2 md2 _ _ _ _ a nn M2 LG2 Hin) as (A1 & A2' & _).
  assert (PL' : Permutation ((a, nn) :: sLam) ((sD ++ [(a, nn)]) ++ Lam0)).
  { rewrite <- app_assoc. cbn [app]. eapply Permutation_trans; [apply perm_skip; exact PERM|].
    apply Permutation_middle. }
  assert (NB' : new_blks L0 A0 (sD ++ [(a, nn)])).
  { intros a' k' Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (NB a' k' Hb)|].
    exact (pi_new_keep sL sA sm smd _ RP NBa a' k' Hb). }
  assert (HKD : In (skeys, 8 * Z.of_nat scap) (sD ++ [(a, nn)])).
  { apply in_or_app. left. rewrite sED. apply in_or_app. left. exact (s_keys_slot sO). }
  destruct (pi_kAk L2 A2 mem2 md2 _ _ _ _ m3 (sD ++ [(a, nn)]) skeys (8 * Z.of_nat scap)
    (skeys + 8 * Z.of_nat sn) RPc RD2 LG2 PL' NB' FR2 AUX2 HKD ltac:(lia) ltac:(lia) CH3)
    as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  destruct (decode_stop _ s r Hdc) as (Q' & HQ' & Er & Hls & _). rewrite HQ in HQ'. injection HQ' as <-.
  pose proof (scan_quote _ Q HQ) as (HQl & _).
  assert (Ez : rest_at tb text (sx + 1) = firstn (S Q) (rest_at tb text (sx + 1)) ++ r)
    by (rewrite Er, firstn_skipn; reflexivity).
  pose proof (pi_rest_app tb text (sx + 1) _ r ltac:(lia) Ez) as Er2.
  rewrite length_firstn, Nat.min_l in Er2 by lia.
  replace (sx + 1 + Z.of_nat (S Q)) with (sx + nn + 1) in Er2 by lia.
  assert (Lr : length r = (length (rest_at tb text (sx + 1)) - S Q)%nat) by (rewrite Er; apply length_skipn).
  pose proof (skip_len (rest_at tb text sP)) as SL. rewrite sSK in SL. cbn [length] in SL.
  pose proof (lsz_counts sD str HP NL) as HELD.
  pose proof (pi_lsum_perm _ _ PERM) as LP. rewrite pi_lsum_app, HELD in LP.
  assert (EPK : Z.max peak0 (lsum Lam0 + hpeak (str ++ [EAlloc (S Q)])) =
                Z.max (Z.max peak0 (lsum Lam0 + hpeak str)) (lsum sLam + nn)).
  { rewrite hpeak_app. cbn [hpeak held_ev]. pose proof (pi_hpeak_held str). lia. }
  assert (ECN : cnt0 + Z.of_nat (calls (str ++ [EAlloc (S Q)])) = cnt0 + Z.of_nat (calls str) + 1)
    by (rewrite calls_app; cbn [calls is_call]; lia).
  pose proof sLG as (_ & _ & _ & _ & _ & LF0). rewrite Forall_forall in LF0.
  destruct (LF0 _ (s_keys_in sO)) as (_ & KB0 & _). cbn [fst snd] in KB0.
  assert (KNE : (a, nn) <> (skeys, 8 * Z.of_nat scap)).
  { intros E. apply (NBa a nn (or_introl eq_refl)). injection E as E1 E2. rewrite E1, E2. exact KB0. }
  split.
  { split; [exact FZ|]. split; [exact FK|]. split; [exact RP3|]. split; [exact RD3|]. split; [exact FR3|].
    split; [exact PL'|].
    split.
    { rewrite pi_lsz_app, map_app. cbn [fold_left lsz_ev map snd].
      replace nn with (Z.of_nat (S Q)) by lia.
      eapply Permutation_trans; [apply Permutation_sym, Permutation_cons_append|]. apply perm_skip. exact HP. }
    split; [rewrite length_app, pi_nlive_app; cbn [length nlive nlive_ev]; lia|].
    split; [exact NB'|].
    split.
    { rewrite rf_run_app.
      replace (rf_run RF (rf_run RF b0 str) [EAlloc (S Q)]) with (rf_malloc RF (rf_run RF b0 str) (Z.of_nat (S Q) + 16))
        by reflexivity.
      replace (Z.of_nat (S Q) + 16) with (nn + 16) by lia. exact RF2. }
    exact AUX3. }
  split; [rewrite EPK, ECN; exact LG3|].
  split; [rewrite ECN; lia|].
  split; [exact (s_kframe _ L2 A2 mem2 md2 _ _ _ m3 M2 LG2 INC PO2 MB3)|].
  split.
  { destruct CB as (CF & CBt). split; [exact CF|].
    apply (pis_bytes_mv segs mem2 m3 a a _ CBt); [lia | rewrite length_map, length_app; cbn [length]; lia |].
    intros i Hi. rewrite length_map, length_app in Hi. cbn [length] in Hi.
    refine (proj1 (MB3 (a + i) ltac:(lia) _ _)); [|lia].
    destruct (pi_lam_disj L2 A2 mem2 md2 _ _ _ _ a nn skeys (8 * Z.of_nat scap) M2 LG2 Hin (INC _ (s_keys_in sO)) KNE);
      lia. }
  split; [exact Er2|].
  split; [lia | exact Hls].
Qed.

Lemma s_arm0 : forall L2 A2 mem2 md2 peak2 cnt2 fail2 tn okr m3 R',
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 sLam peak2 cnt2 fail2 -> pi_frm mem2 ->
  (st_init_done A2 = false -> auxv_pre B (ly_sec L0) pi_lo mem2) ->
  pis_open segs mem2 (lin sLam) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi ->
  jr_name true (rest_at tb text sP) (skipn (calls str) pi_ok) = (None, tn, okr) ->
  peak2 = Z.max peak0 (lsum Lam0 + hpeak (str ++ tn)) -> cnt2 = cnt0 + Z.of_nat (calls (str ++ tn)) ->
  fail_after cnt0 fail0 (calls (str ++ tn)) fail2 -> rf_ok RF A2 (rf_run RF b0 (str ++ tn)) ->
  lsz (str ++ tn) = lsz str -> nlive tn = 0 ->
  chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8)] mem2 m3 ->
  pj_in_ok rsegs m3 q text len sx (Z.of_nat d + 1) tb ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst sfx R' (getr regs0 1) m3 (seg_rom segs)) md2).
Proof.
  intros L2 A2 mem2 md2 peak2 cnt2 fail2 tn okr m3 R' RPc RD2 LG2 FR2 AUX2 PO2 JN PK CN FA RS LZ NL0 CH3 PX RPF R10F.
  pose proof sGL as (_ & _ & _ & _ & _ & PERM & _ & _ & NB & _).
  pose proof s_lt as LT. pose proof RPc as (M2 & _).
  assert (CH3' : chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8); (q, q + 8)] mem2 m3)
    by (eapply chg_weaken; [|exact CH3]; intros z Hz; cbn [outside] in Hz |- *; tauto).
  assert (HKD : In (skeys, 8 * Z.of_nat scap) sD) by (rewrite sED; apply in_or_app; left; exact (s_keys_slot sO)).
  destruct (pi_kAk L2 A2 mem2 md2 sLam peak2 cnt2 fail2 m3 sD skeys (8 * Z.of_nat scap) (skeys + 8 * Z.of_nat sn)
    RPc RD2 LG2 PERM NB FR2 AUX2 HKD ltac:(lia) ltac:(lia) CH3') as (RP3 & RD3 & LG3 & FR3 & AUX3 & MB3).
  apply (s_fin L2 A2 m3 md2 sLam peak2 cnt2 fail2 tn okr sx R' RP3 RD3 LG3 PERM
    (s_kframe sLam L2 A2 mem2 md2 peak2 cnt2 fail2 m3 M2 LG2 (fun b Hb => Hb) PO2 MB3) JN PK CN FA RS LZ NL0);
    [rewrite pi_seg; exact PX | exact RPF | exact R10F].
Qed.

Lemma s_ps : forall (P : config -> Prop) L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 P2,
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L2 A2 regs0 mem2 md2 ->
  ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> incl sLam Lam2 -> pi_frm mem2 -> pi_cs regs2 ->
  pis_open segs mem2 (lin Lam2) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) (map snd (rev sacc))
    (map fst (rev sacc)) sDi ->
  pj_in_ok segs mem2 q text len P2 (Z.of_nat d + 1) tb ->
  (bv_unsigned (getr regs2 10) = 0 -> forall m3 R',
     chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8)] mem2 m3 ->
     bytes_at rsegs m3 (skeys + 8 * Z.of_nat sn) (le8 (getr regs2 10)) ->
     pj_in_ok rsegs m3 q text len P2 (Z.of_nat d + 1) tb ->
     regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
     P (mkCfg (@mkst sfx R' (getr regs0 1) m3 (seg_rom segs)) md2)) ->
  (bv_unsigned (getr regs2 10) <> 0 -> forall x' m3 R3,
     P2 <= x' <= text + len -> rest_at tb text x' = skip (rest_at tb text P2) ->
     (forall c r0, rest_at tb text x' = c :: r0 -> c <> 58) ->
     chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8); (q, q + 8)] mem2 m3 ->
     bytes_at rsegs m3 (skeys + 8 * Z.of_nat sn) (le8 (getr regs2 10)) ->
     pj_in_ok rsegs m3 q text len x' (Z.of_nat d + 1) tb ->
     pi_cs R3 -> getr R3 1 = Z_to_bv 64 0x15270 -> getr R3 10 = getr regs2 10 ->
     SR segs (mkCfg (@mkst sfx R3 (Z_to_bv 64 0x141c4) m3 (seg_rom segs)) md2) P) ->
  (bv_unsigned (getr regs2 10) <> 0 -> forall x' m3 R'',
     P2 <= x' < text + len -> skip (rest_at tb text P2) = 58 :: rest_at tb text (x' + 1) ->
     chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8); (q, q + 8)] mem2 m3 ->
     bytes_at rsegs m3 (skeys + 8 * Z.of_nat sn) (le8 (getr regs2 10)) ->
     pj_in_ok rsegs m3 q text len (x' + 1) (Z.of_nat d + 1) tb ->
     pi_cs R'' -> getr R'' 1 = Z_to_bv 64 0x1519c -> getr R'' 10 = Z_to_bv 64 (skids + 56 * Z.of_nat sn) ->
     getr R'' 11 = Z_to_bv 64 0 -> getr R'' 12 = Z_to_bv 64 56 ->
     SR segs (mkCfg (@mkst sfx R'' (Z_to_bv 64 0x20b28) m3 (seg_rom segs)) md2) P) ->
  SR segs (mkCfg (@mkst sfx regs2 (Z_to_bv 64 0x1511c) mem2 (seg_rom segs)) md2) P.
Proof.
  intros P L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 P2 RPc LG2 INC FR2 CS2 PO2 PIN2 KA KB KC.
  pose proof RPc as (M2 & _).
  destruct (mr_model B _ (aa_laws API) L2 A2 mem2 md2 M2) as (Hh2 & Hl2 & _).
  pose proof s_lt as LT. pose proof (s_keys_in sO) as HKL.
  pose proof sGL as (_ & _ & _ & _ & _ & PERM & _ & _ & NB & _).
  pose proof PO2 as (HN & HA & ((HRW & _) & _ & _ & _ & (_ & HK24) & (_ & HK32) & (_ & HN40) & _) & _).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV. pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof QSP as QS. pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN2) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ _ _ M2 LG2 (INC _ HKL)) as (Y1 & Y2 & _).
  destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ _ _ M2 LG2 (INC _ s_kids_in)) as (Z1 & Z2 & _).
  assert (KB2 : In (skeys - 16, 8 * Z.of_nat scap + 16) (blocks L2 A2)).
  { pose proof LG2 as (_ & _ & _ & _ & _ & LF2). rewrite Forall_forall in LF2.
    destruct (LF2 _ (INC _ HKL)) as (_ & Hb & _). exact Hb. }
  assert (KN : ~ In (skeys - 16, 8 * Z.of_nat scap + 16) (blocks L0 A0)).
  { apply NB. rewrite sED. apply in_or_app. left. exact (s_keys_slot sO). }
  pose proof (pi_text_new L2 A2 mem2 md2 _ _ RPc KB2 KN) as TN.
  unfold pi_frm in FR2.
  rewrite pi_seg.
  eapply rk_kA; [exact Hh2 | exact Hl2 | |].
  { rewrite (pi_canon regs2 CS2).
    eapply pip_ps with (p := P2) (d := Z.of_nat d + 1) (keys := skeys) (vals := skids) (n := Z.of_nat sn) (tb := tb).
    - rewrite <- pi_seg. exact PIN2.
    - exact FR2.
    - left. unfold pi_f. lia.
    - rewrite <- pi_seg. exact HK24.
    - rewrite <- pi_seg. exact HK32.
    - rewrite <- pi_seg. exact HN40.
    - split; [lia|]. split; [lia|]. intros i Hi. rewrite <- pi_seg.
      pose proof (ledger_block_present B API L2 A2 mem2 md2 Lam2 _ _ _ skeys (8 * Z.of_nat scap) (8 * Z.of_nat sn + i)
        M2 LG2 (INC _ HKL) ltac:(lia)) as Hpr.
      replace (skeys + (8 * Z.of_nat sn + i)) with (skeys + 8 * Z.of_nat sn + i) in Hpr by lia.
      exact (present_writable B mem2 _ Hpr).
    - lia.
    - lia.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split.
      { destruct (Z_le_gt_dec (text + len) (skeys + 8 * Z.of_nat sn)) as [Ha|Ha]; [right; exact Ha|].
        destruct (Z_le_gt_dec (skeys + 8 * Z.of_nat sn + 8) text) as [Hb|Hb]; [left; exact Hb|].
        exfalso. apply (TN (Z.max text (skeys + 8 * Z.of_nat sn) - text) ltac:(lia)). lia. }
      split; [unfold pi_f; lia|]. split; [|exact I].
      destruct (Z_le_gt_dec (v + 32) (skeys + 8 * Z.of_nat sn)) as [Ha|Ha]; [right; exact Ha|].
      destruct (Z_le_gt_dec (skeys + 8 * Z.of_nat sn + 8) (v + 24)) as [Hb|Hb]; [left; exact Hb|].
      exfalso. apply (HA (skeys, 8 * Z.of_nat scap) (Z.max (v + 24) (skeys + 8 * Z.of_nat sn)));
        [apply in_or_app; left; exact (s_keys_slot sO) | unfold pj_holds; cbn [fst snd]; lia | lia].
    - cbn [disjoint_from]. split; [lia | exact I]. }
  intros ms' (can & HQ & EQV).
  destruct HQ as [(Hk0 & m3 & -> & CH3 & BK3 & PX3) | [(Hk0 & x' & a3' & a4' & m3 & -> & HX1 & RX & NC & CH3 & BK3 & PX3) |
    (Hk0 & x' & a3' & a4' & m3 & -> & HX1 & SK & CH3 & BK3 & PX3)]].
  - rewrite <- pi_seg. eapply pi_ret; [exact EQV|]. intros R' RPF R10F. exact (KA Hk0 m3 R' CH3 BK3 PX3 RPF R10F).
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems, <- pi_seg.
    apply (KB Hk0 x' m3 (ms_regs ms') HX1 RX NC CH3 BK3 PX3).
    + unfold pi_cs. repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]). rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems, <- pi_seg.
    apply (KC Hk0 x' m3 (ms_regs ms') HX1 SK CH3 BK3 PX3).
    + unfold pi_cs. repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]). rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
Qed.

Lemma s_ff : forall w L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 x' R3,
  (length (rest_at tb text sP) <= w)%nat ->
  rpost B API PARSE_STRING_K sL sA sR sm smd (parse_string_writes q a nn) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> rf_ok RF A2 b2 ->
  scan (rest_at tb text (sx + 1)) = Some Q -> nn = Z.of_nat Q + 1 -> cnt2 = cnt0 + Z.of_nat (calls str) + 1 ->
  cnt0 + Z.of_nat (calls str) <> fail0 -> decode (rest_at tb text (sx + 1)) = Some (s, r) ->
  Lam2 = (a, nn) :: sLam -> new_blks sL sA [(a, nn)] ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak str)) (lsum sLam + nn) -> fail2 = fail0 ->
  b2 = rf_malloc RF (rf_run RF b0 str) (nn + 16) -> pj_cbytes segs mem2 a s ->
  chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8); (q, q + 8)] mem2 m3 ->
  rest_at tb text x' = skip (rest_at tb text (sx + nn + 1)) ->
  (forall c r0, rest_at tb text x' = c :: r0 -> c <> 58) ->
  pj_in_ok rsegs m3 q text len x' (Z.of_nat d + 1) tb ->
  pi_cs R3 -> getr R3 1 = Z_to_bv 64 0x15270 -> getr R3 10 = Z_to_bv 64 a ->
  SR segs (mkCfg (@mkst sfx R3 (Z_to_bv 64 0x141c4) m3 (seg_rom segs)) md2) (pi_next w).
Proof.
  intros w L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 x' R3 HW RPS RD2 LG2 RF2 HQ En Ec Hcf Hdc EL NBa
    Ep Ef Eb CB CH3 RX NC PX CS3 G1 G10.
  destruct (s_succ L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 RPS RD2 LG2 RF2 HQ En Ec Hcf Hdc EL NBa
    Ep Ef Eb CB CH3) as (GL3 & LG3 & NF3 & PO3 & CB3 & Er & HLr & Hls).
  pose proof GL3 as (FZ3 & FK3 & RP3 & RD3 & FR3 & PL3 & HP3 & NL3 & NB3 & RS3 & AUX3).
  pose proof RP3 as (M3 & _).
  pose proof sGL as (_ & _ & _ & _ & _ & PERM & _ & _ & NB & _).
  pose proof (pi_K_bounds sHD) as (_ & _ & KA & _ & _ & _ & KA0 & _).
  pose proof (pi_sp R3 CS3) as SP3.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof QSP as QS. pose proof s_lt as LT.
  pose proof RPL as (_ & _ & PNO).
  assert (Hin : In (a, nn) Lam2) by (rewrite EL; left; reflexivity).
  destruct (ledger_block_range B API L2 A2 m3 md2 Lam2 _ _ _ a nn M3 LG3 Hin) as (A1 & A2' & _).
  assert (ENV3 : reader_env (fx := sfx) B API ALLOC_STACK L2 A2 R3 m3 md2).
  { apply (pi_env sfx L2 A2 m3 md2 Lam2 _ _ R3 ALLOC_STACK GL3 CS3); [|exact KA | exact KA0].
    rewrite G1. apply YK0s.ret_ok_even. vm_compute. reflexivity. }
  pose proof ENV3 as (_ & _ & _ & _ & _ & CP3 & _).
  pose proof RD3 as (ROA3 & _).
  eapply SR_bind.
  { change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
    exact (FFC sfx L2 A2 R3 m3 md2 a nn _ Lam2 _ _ _ CP3 G10 LG3 ROA3 (or_intror Hin) RS3). }
  intros c4 (L4 & A4 & regs4 & m4 & md4 & -> & ROA4 & GK4 & HI4 & HX4 & CPK & HRG & KP4 & UK & ARMS).
  rewrite G1.
  destruct ARMS as [(Ea & _) | (_ & _ & (l1 & l2 & EL2 & LG4) & RF4)]; [lia|].
  pose proof CPK as (M4 & _ & _ & _ & _ & RPr4 & _).
  pose proof (pi_ff_rpost L2 A2 R3 m3 md2 a nn L4 A4 regs4 m4 md4 M3 CPK HI4 HX4 HRG UK) as RP4.
  assert (HE4 : forall x, free_writes a nn x -> pi_E0 x \/ pi_fresh x).
  { intros x [Hx|(_ & Hx)].
    - left. right. right. left. exact Hx.
    - right. apply (pi_fresh_D L2 A2 m3 md2 Lam2 _ _ _ _ x RP3 LG3 PL3 NB3). exists a, nn.
      split; [apply in_or_app; right; left; reflexivity | lia]. }
  assert (NBa0 : ~ In (a - 16, nn + 16) (blocks L0 A0)) by (apply NB3; apply in_or_app; right; left; reflexivity).
  assert (HG4 : forall p n, In (p, n) (user_blocks A0) -> ~ (ptr_addr L0 p = a - 16 /\ n = nn + 16)).
  { intros p n Hp (E1 & E2). apply NBa0. rewrite <- E1, <- E2. exact (rk_blk_of_user L0 A0 p n Hp). }
  assert (RPc4 : rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L4 A4 regs0 m4 md4)
    by exact (pi_rp_call L2 A2 m3 md2 _ R3 _ _ L4 A4 regs4 m4 md4 RP3 RP4 SP3 KA KA0 HE4 HG4).
  pose proof (YL01.ax_statics AX L4 A4 m4 md4 M4) as (GW1 & (g & _ & GW2) & _).
  assert (RD4 : rd_cells B m4) by (split; [exact ROA4 | split; [exact GW1 | exists g; exact GW2]]).
  destruct (mr_model B _ (aa_laws API) L4 A4 m4 md4 M4) as (Hh4 & Hl4 & _).
  assert (CS4 : pi_cs regs4) by exact (pi_cs_rp R3 regs4 CS3 RPr4).
  assert (FR4 : pi_frm m4) by exact (pi_frm_call L2 A2 m3 md2 _ R3 _ _ L4 A4 regs4 m4 md4 RP4 ltac:(lia) HE4 FR3).
  assert (PS : Permutation sLam (l1 ++ l2)).
  { pose proof (Permutation_app_inv [] sLam l1 l2 (a, nn)) as PAI. cbn [app] in PAI. apply PAI.
    rewrite <- EL2, EL. apply Permutation_refl. }
  assert (PL4 : Permutation (l1 ++ l2) (sD ++ Lam0))
    by (eapply Permutation_trans; [apply Permutation_sym; exact PS | exact PERM]).
  pose proof LG3 as (_ & _ & _ & _ & ND3 & LF3). rewrite Forall_forall in LF3.
  destruct (LF3 _ Hin) as (_ & Lin & _). cbn [fst snd] in Lin.
  assert (NI : ~ In a (map fst sLam)).
  { rewrite EL in ND3. cbn [map fst] in ND3. apply NoDup_ListNoDup in ND3. inversion ND3 as [|? ? Hn0 _]. exact Hn0. }
  assert (BLK4 : forall b kb x, In (b, kb) sLam -> b <= x < b + kb -> pis_same segs m3 m4 x).
  { intros b kb x Hb Hx.
    assert (Hb2 : In (b, kb) Lam2) by (rewrite EL; right; exact Hb).
    assert (Nba : b <> a) by (intros E; subst b; apply NI; exact (in_map fst _ _ Hb)).
    assert (Hne : (b, kb) <> (a, nn)) by (intros E; injection E as E1 _; exact (Nba E1)).
    apply (pi_lam_same L2 A2 m3 md2 Lam2 _ _ _ _ R3 _ _ L4 A4 regs4 m4 md4 (l1 ++ l2) _ _ _ b kb x LG3 RP4 LG4 Hb2
      (Permutation_in _ PS Hb)); [intros (E1 & _); lia | exact Hx |].
    intros [Hs|(_ & Hs)].
    - apply (ledger_block_not_img B L2 A2 m3 Lam2 _ _ _ b kb (x - b) LG3 Hb2 ltac:(lia)).
      replace (b + (x - b)) with x by lia. apply pi_statics_img. left. exact Hs.
    - destruct (pi_lam_disj L2 A2 m3 md2 Lam2 _ _ _ b kb a nn M3 LG3 Hb2 Hin Hne); lia. }
  assert (VS4 : forall x, v <= x < v + 56 -> pis_same segs m3 m4 x).
  { apply (pi_v_same L2 A2 m3 md2 _ R3 _ _ L4 A4 regs4 m4 md4 RP3 RP4 ltac:(lia)).
    - intros x Hx [Hs|(_ & Hs)].
      + destruct (PNO (x - v) ltac:(lia)) as (_ & N2 & _). apply N2. replace (v + (x - v)) with x by lia. left. exact Hs.
      + exact (pi_new_raw L2 A2 m3 md2 (a - 16) (nn + 16) x RP3 Lin NBa0 ltac:(lia) Hx).
    - intros a0 k0 Hb0 (E1 & E2). apply NBa0. rewrite <- E1, <- E2. exact Hb0. }
  assert (PO4 : pis_open segs m4 (lin (l1 ++ l2)) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn)
                  (map snd (rev sacc)) (map fst (rev sacc)) sDi).
  { pose proof PO3 as (_ & _ & Hh3 & _).
    apply (pis_frame segs m3 (lin Lam2) m4 (lin (l1 ++ l2)) v o snum skids skeys (Z.of_nat scap) (Z.of_nat sn) _ _ sDi
      snum (Z.of_nat sn) PO3).
    - exact (pis_hdr_frame segs m3 m4 v _ _ _ _ _ _ _ Hh3 VS4).
    - lia.
    - intros a' k' Hak. exact (Permutation_in _ PS (s_slots_in _ Hak)).
    - intros x [Hx|[(Eo & Hx)|((a' & k') & Hb & Hx)]].
      + rewrite s_ts in Hx. apply (BLK4 skids (56 * Z.of_nat scap) x s_kids_in). lia.
      + rewrite s_ts in Hx. apply (BLK4 skeys (8 * Z.of_nat scap) x (s_keys_in Eo)). lia.
      + unfold pj_holds in Hx; cbn [fst snd] in Hx.
        apply (BLK4 a' k' x); [apply s_slots_in; apply in_or_app; right; exact Hb | exact Hx]. }
  assert (PX4 : pj_in_ok segs m4 q text len x' (Z.of_nat d + 1) tb).
  { apply (pi_in_call L2 A2 m3 md2 _ R3 _ _ L4 A4 regs4 m4 md4 x' (Z.of_nat d + 1) RPc4 RP4);
      [rewrite SP3; unfold pi_f; lia | |].
    - intros x [Hs|(_ & Hs)] Hq.
      + pose proof (rk_img_bound pi_seg x (pi_statics_img x (or_introl Hs))). lia.
      + lia.
    - rewrite pi_seg. exact PX. }
  unfold pi_frm in FR4.
  rewrite pi_seg.
  eapply rk_kA; [exact Hh4 | exact Hl4 | rewrite (pi_canon regs4 CS4); eapply pip_ff; exact FR4 |].
  intros ms' (can & -> & EQV).
  rewrite <- pi_seg. eapply pi_ret; [exact EQV|]. intros R' RPF R10F. left.
  apply (s_fin L4 A4 m4 md4 (l1 ++ l2) _ _ _ [EAlloc (S Q); EFree (S Q)] (skipn (S (calls str)) pi_ok) x' R'
    RPc4 RD4 LG4 PL4 PO4).
  - rewrite (pi_nm_val _ _ _ sSK), HQ, pi_take, pi_ok_nth. cbn [fst snd].
    rewrite (proj2 (Z.eqb_neq _ _) Hcf). cbn [negb]. rewrite Hdc. cbv beta iota. rewrite <- Er, <- RX.
    destruct (rest_at tb text x') as [|c r1] eqn:Ex; [reflexivity|].
    rewrite (proj2 (Z.eqb_neq c 58) (NC c r1 eq_refl)). reflexivity.
  - rewrite !hpeak_app. cbn [hpeak held_ev]. lia.
  - rewrite !calls_app. cbn [calls is_call]. lia.
  - split; [intros H; exfalso; apply NF3; rewrite calls_app in H |- *; cbn [calls is_call] in H |- *; lia | intros _; reflexivity].
  - assert (ER : rf_run RF b0 (str ++ [EAlloc (S Q); EFree (S Q)]) =
                 rf_free RF (rf_run RF b0 (str ++ [EAlloc (S Q)])) (nn + 16)).
    { rewrite !rf_run_app. replace (nn + 16) with (Z.of_nat (S Q) + 16) by lia. reflexivity. }
    rewrite ER. exact RF4.
  - rewrite pi_lsz_app. cbn [fold_left lsz_ev rm1n]. rewrite Nat.eqb_refl. reflexivity.
  - reflexivity.
  - exact PX4.
  - exact RPF.
  - exact R10F.
Qed.

Lemma s_colon : forall w L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 x' R'',
  (length (rest_at tb text sP) <= w)%nat ->
  rpost B API PARSE_STRING_K sL sA sR sm smd (parse_string_writes q a nn) (fun _ _ => False) L2 A2 regs2 mem2 md2 ->
  rd_cells B mem2 -> ledger B L2 A2 mem2 Lam2 peak2 cnt2 fail2 -> rf_ok RF A2 b2 ->
  scan (rest_at tb text (sx + 1)) = Some Q -> nn = Z.of_nat Q + 1 -> cnt2 = cnt0 + Z.of_nat (calls str) + 1 ->
  cnt0 + Z.of_nat (calls str) <> fail0 -> decode (rest_at tb text (sx + 1)) = Some (s, r) ->
  Lam2 = (a, nn) :: sLam -> new_blks sL sA [(a, nn)] ->
  peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak str)) (lsum sLam + nn) -> fail2 = fail0 ->
  b2 = rf_malloc RF (rf_run RF b0 str) (nn + 16) -> pj_cbytes segs mem2 a s ->
  chg [(skeys + 8 * Z.of_nat sn, skeys + 8 * Z.of_nat sn + 8); (q, q + 8)] mem2 m3 ->
  bytes_at rsegs m3 (skeys + 8 * Z.of_nat sn) (le8 (Z_to_bv 64 a)) ->
  skip (rest_at tb text (sx + nn + 1)) = 58 :: rest_at tb text (x' + 1) ->
  pj_in_ok rsegs m3 q text len (x' + 1) (Z.of_nat d + 1) tb ->
  pi_cs R'' -> getr R'' 1 = Z_to_bv 64 0x1519c -> getr R'' 10 = Z_to_bv 64 (skids + 56 * Z.of_nat sn) ->
  getr R'' 11 = Z_to_bv 64 0 -> getr R'' 12 = Z_to_bv 64 56 ->
  pi_mc w (mkCfg (@mkst sfx R'' (Z_to_bv 64 0x20b28) m3 (seg_rom segs)) md2).
Proof.
  intros w L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 x' R'' HW RPS RD2 LG2 RF2 HQ En Ec Hcf Hdc EL NBa
    Ep Ef Eb CB CH3 BK3 SK PX CS' G1' G10' G11' G12'.
  destruct (s_succ L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Q s r m3 RPS RD2 LG2 RF2 HQ En Ec Hcf Hdc EL NBa
    Ep Ef Eb CB CH3) as (GL3 & LG3 & NF3 & PO3 & CB3 & Er & HLr & Hls).
  pose proof GL3 as (_ & _ & RP3 & _). pose proof RP3 as (M3 & _). pose proof rk_ceil as HC.
  assert (Hin : In (a, nn) Lam2) by (rewrite EL; left; reflexivity).
  destruct (ledger_block_range B API L2 A2 m3 md2 Lam2 _ _ _ a nn M3 LG3 Hin) as (A1 & A2' & _).
  rewrite Er in SK.
  pose proof (skip_len r) as SLr. rewrite SK in SLr. cbn [length] in SLr.
  assert (JN : jr_name o (rest_at tb text sP) (skipn (calls str) pi_ok) =
               (Some (s, rest_at tb text (x' + 1)), [EAlloc (S Q)], skipn (S (calls str)) pi_ok)).
  { rewrite sO, (pi_nm_val _ _ _ sSK), HQ, pi_take, pi_ok_nth. cbn [fst snd].
    rewrite (proj2 (Z.eqb_neq _ _) Hcf). cbn [negb]. rewrite Hdc. cbv beta iota. rewrite SK. reflexivity. }
  assert (JN0 : jr_name o (rest_at tb text sP) [] = (Some (s, rest_at tb text (x' + 1)), [EAlloc (S Q)], [])).
  { rewrite sO, (pi_nm_val _ _ _ sSK), HQ. cbn [take fst snd]. rewrite Hdc. cbv beta iota. rewrite SK. reflexivity. }
  pose proof sEXT as E. unfold jafter in E. pose proof (ext_bind_some _ _ _ _ _ _ _ _ _ _ JN E) as E1.
  cbn [fst snd] in E1.
  pose proof sROOM as RM. unfold jafter in RM.
  rewrite (bind_nil_trace _ _ _ _ _ _ (agrees_jr_name o (rest_at tb text sP)) JN0) in RM. cbn [fst snd] in RM.
  destruct (room_run_app RF [EAlloc (S Q)] (rf_run RF b0 str) _ RM) as [_ RM2].
  exists sfx, R'', m3, md2, L2, A2, Lam2, (str ++ [EAlloc (S Q)]), (sD ++ [(a, nn)]), sn, scap, sacc, (x' + 1), snum,
    skids, skeys, sDi, s, [(a, nn)].
  split; [reflexivity|]. split; [exact sHD|]. split; [exact CS'|]. split; [exact G1'|]. split; [exact G10'|].
  split; [exact G11'|]. split; [exact G12'|]. split; [exact GL3|]. split; [exact LG3|]. split; [exact NF3|].
  split; [rewrite pi_seg; exact PX|].
  split; [lia|].
  split; [rewrite calls_app; cbn [calls is_call]; pose proof sCB; lia|].
  split; [rewrite calls_app; cbn [calls is_call]; rewrite Nat.add_1_r; exact E1|].
  split; [rewrite rf_run_app; exact RM2|].
  split; [exact sLA|]. split; [exact sINV|].
  split; [rewrite sED, <- !app_assoc; reflexivity|].
  split; [exact PO3|].
  split.
  { rewrite sO. cbv beta iota. exists a, nn. split; [reflexivity|]. split.
    - split; [lia | rewrite pi_seg; exact BK3].
    - split; [rewrite EL; left; reflexivity|]. split; [lia | exact CB3]. }
  exact sDEP.
Qed.

Lemma pi_str_core : forall w, (length (rest_at tb text sP) <= w)%nat ->
  SR segs (mkCfg (@mkst sfx sR (Z_to_bv 64 0x152a4) sm (seg_rom segs)) smd) (pi_next w).
Proof using All.
  intros w HW.
  pose proof (pi_K_bounds sHD) as (_ & KS & _ & _ & _ & KS0 & _).
  pose proof sGL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP as (M & _ & _ & Y & _).
  pose proof (pi_sp sR sCS) as SP. pose proof s_lt as LT.
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ sPIN) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ. pose proof QSP as QS.
  assert (ENVs : reader_env (fx := sfx) B API PARSE_STRING_K sL sA sR sm smd).
  { apply (pi_env sfx sL sA sm smd sLam str sD sR _ sGL sCS); [|exact KS | exact KS0].
    rewrite sG1. apply YK0s.ret_ok_even. vm_compute. reflexivity. }
  assert (RQ : rest_at tb text sx = 34 :: rest_at tb text (sx + 1))
    by exact (pi_rest_sk tb text len sP sx 34 TL ltac:(lia) ltac:(lia) sSK).
  assert (NTH : nth_error tb (Z.to_nat (sx - text)) = Some (Z_to_bv 8 34)) by exact (pi_ra_nth tb text sx 34 _ RQ).
  assert (QSPs : spZ sR <= q) by (rewrite SP; unfold pi_f; lia).
  assert (AUXq : st_init_done sA = false -> auxv_pre B (ly_sec sL) (q + 24) sm).
  { intros HDn. destruct Y as (_ & Hsec & _). rewrite Hsec.
    apply (auxv_pre_mono B _ pi_lo); [unfold pi_lo; lia | exact (AUX HDn)]. }
  assert (TOKs : text_ok B sL sA sLam sR text len)
    by exact (pi_text_ok sfx sL sA sm smd sLam str sD sR _ _ _ sGL sLG SP).
  assert (DJ2 : Frame.disjoint_from [(q, q + 24); (text, text + len)] (spZ sR - PARSE_STRING_K) PARSE_STRING_K).
  { cbn [Frame.disjoint_from]. rewrite SP. unfold pi_f. lia. }
  assert (CNTs : cnt0 + Z.of_nat (calls str) + 1 < 2 ^ 64 - 1)
    by (pose proof CNT; pose proof sCB as CB; unfold pi_x in CB; lia).
  assert (ROOMs : forall Qn, scan (rest_at tb text (sx + 1)) = Some Qn ->
      rf_room RF (rf_run RF b0 str) (Z.of_nat Qn + 17) /\ Z.of_nat Qn + 17 <= 2 ^ 28).
  { intros Qn HQ. pose proof sROOM as RM. unfold jafter in RM. apply (pi_room_bind RF) in RM.
    rewrite sO, (pi_nm_val _ _ _ sSK), HQ in RM. cbn [take fst snd] in RM.
    replace (Z.of_nat Qn + 17) with (Z.of_nat (S Qn) + 16) by lia.
    destruct (decode (rest_at tb text (sx + 1))) as [[s0' r0']|];
      [destruct (skip r0') as [|c r1]; [|destruct (c =? 58)]|];
      cbn [snd fst room_run is_call esize] in RM; destruct RM as (Hc & _); exact (Hc eq_refl). }
  eapply SR_bind.
  { change (Z_to_bv 64 0x152a4) with (Z_to_bv 64 PARSE_STRING).
    exact (PSC sfx sL sA sR sm smd sLam _ _ _ _ q text len sx (Z.of_nat d + 1) tb ENVs sLG RS sG10 sPIN
      ltac:(lia) NTH QSPs AUXq TOKs DJ2 CNTs ROOMs). }
  intros c1 (L2 & A2 & regs2 & mem2 & md2 & Lam2 & peak2 & cnt2 & fail2 & b2 & res & a & nn & -> & RPS & RD2 & G10' &
    LG2 & RF2 & ARM).
  rewrite sG1.
  pose proof RPS as (M2 & _).
  assert (CASES : (res = 0 /\ Lam2 = sLam /\ pj_in_ok segs mem2 q text len sx (Z.of_nat d + 1) tb /\
      (forall x, 0 <= x -> a <> 0 -> a - 16 <= x < a + nn ->
         pi_fresh x /\ forall pz kz, In (pz, kz) (blocks sL sA) -> ~ (pz <= x < pz + kz)) /\
      exists tn okr, jr_name true (rest_at tb text sP) (skipn (calls str) pi_ok) = (None, tn, okr) /\
        peak2 = Z.max peak0 (lsum Lam0 + hpeak (str ++ tn)) /\ cnt2 = cnt0 + Z.of_nat (calls (str ++ tn)) /\
        fail_after cnt0 fail0 (calls (str ++ tn)) fail2 /\ b2 = rf_run RF b0 (str ++ tn) /\
        lsz (str ++ tn) = lsz str /\ nlive tn = 0) \/
    (res = a /\ exists Qn s r, scan (rest_at tb text (sx + 1)) = Some Qn /\ nn = Z.of_nat Qn + 1 /\
        cnt2 = cnt0 + Z.of_nat (calls str) + 1 /\ cnt0 + Z.of_nat (calls str) <> fail0 /\
        decode (rest_at tb text (sx + 1)) = Some (s, r) /\ Lam2 = (a, nn) :: sLam /\ new_blks sL sA [(a, nn)] /\
        peak2 = Z.max (Z.max peak0 (lsum Lam0 + hpeak str)) (lsum sLam + nn) /\ fail2 = fail0 /\
        b2 = rf_malloc RF (rf_run RF b0 str) (nn + 16) /\ pj_cbytes segs mem2 a s /\
        pj_in_ok segs mem2 q text len (sx + nn + 1) (Z.of_nat d + 1) tb)).
  { pose proof (lsz_counts sD str HP NL) as HELD.
    pose proof (pi_lsum_perm _ _ PERM) as LP. rewrite pi_lsum_app, HELD in LP.
    pose proof (pi_hpeak_held str) as HH.
    destruct (scan (rest_at tb text (sx + 1))) as [Qn|] eqn:HQ.
    - destruct ARM as (En & Ec & [(Hcf & Er & Ea & EL & Ep & Ef & Eb & PJ2) |
        [(Hcf & Hdc & Er & Ha & EL & Ep & Ef & HFr & HLo & Eb & PJ2) |
         (Hcf & Er & Ha & s & r & Hdc & EL & NBa & Ep & Ef & Eb & CB & PJ2)]]).
      + left. split; [exact Er|]. split; [exact EL|]. split; [exact PJ2|].
        split; [intros x _ Ha'; contradiction|].
        exists [EFail (S Qn)], (skipn (S (calls str)) pi_ok).
        split.
        { rewrite (pi_nm_val _ _ _ sSK), HQ, pi_take, pi_ok_nth. cbn [fst snd].
          rewrite (proj2 (Z.eqb_eq _ _) Hcf). reflexivity. }
        split; [rewrite Ep, hpeak_app; cbn [hpeak held_ev]; lia|].
        split; [rewrite Ec, calls_app; cbn [calls is_call]; lia|].
        split; [rewrite Ef, calls_app; cbn [calls is_call]; split; [intros _; reflexivity | intros H; exfalso; lia]|].
        split; [rewrite Eb, rf_run_app; reflexivity|].
        split; [rewrite pi_lsz_app; reflexivity | reflexivity].
      + left. split; [exact Er|]. split; [exact EL|]. split; [exact PJ2|].
        split.
        { intros x Hx0 _ Hx. destruct (HFr x Hx) as (F1 & F2). split; [|exact F2].
          split; [lia|]. split; [exact F1|]. intros p n Hp Hpx.
          exact (F2 (ptr_addr L0 p) n (pi_blk_keep _ _ _ _ _ _ RP (rk_blk_of_user L0 A0 p n Hp)) Hpx). }
        exists [EAlloc (S Qn); EFree (S Qn)], (skipn (S (calls str)) pi_ok).
        split.
        { rewrite (pi_nm_val _ _ _ sSK), HQ, pi_take, pi_ok_nth. cbn [fst snd].
          rewrite (proj2 (Z.eqb_neq _ _) Hcf). cbn [negb]. rewrite Hdc. reflexivity. }
        split; [rewrite Ep, hpeak_app, LP; cbn [hpeak held_ev]; lia|].
        split; [rewrite Ec, calls_app; cbn [calls is_call]; lia|].
        split; [rewrite Ef, calls_app; cbn [calls is_call]; split; [intros H; exfalso; lia | intros _; reflexivity]|].
        split; [rewrite Eb, rf_run_app; replace (nn + 16) with (Z.of_nat (S Qn) + 16) by lia; reflexivity|].
        split; [rewrite pi_lsz_app; cbn [fold_left lsz_ev rm1n]; rewrite Nat.eqb_refl; reflexivity | reflexivity].
      + right. split; [exact Er|]. exists Qn, s, r.
        split; [reflexivity|]. split; [exact En|]. split; [exact Ec|]. split; [exact Hcf|]. split; [exact Hdc|].
        split; [exact EL|]. split; [exact NBa|]. split; [exact Ep|]. split; [exact Ef|]. split; [exact Eb|].
        split; [exact CB | exact PJ2].
    - destruct ARM as (Er & Ea & En & EL' & EA' & EL & Ep & Ec & Ef & Eb & PJ2).
      left. split; [exact Er|]. split; [exact EL|]. split; [exact PJ2|].
      split; [intros x _ Ha'; contradiction|].
      exists [], (skipn (calls str) pi_ok).
      split; [rewrite (pi_nm_val _ _ _ sSK), HQ; reflexivity|].
      rewrite !app_nil_r.
      split; [exact Ep|]. split; [exact Ec|].
      split; [rewrite Ef; split; [intros H; exfalso; exact (sNF H) | intros _; reflexivity]|].
      split; [exact Eb|]. split; reflexivity. }
  destruct CASES as [(Er & EL & PJ2 & HWc & tn & okr & JN & PK & CN & FA & EB & LZ & NL0) |
    (Er & Qn & s & r & HQ & En & Ec & Hcf & Hdc & EL & NBa & Ep & Ef & Eb & CB & PJ2)].
  - subst Lam2.
    destruct (s_post L2 A2 regs2 mem2 md2 sLam _ _ _ a nn RPS LG2 (fun b Hb => Hb) HWc)
      as (RPc & FR2 & AUX2 & CS2 & PO2 & OLD).
    apply (s_ps (pi_next w) L2 A2 regs2 mem2 md2 sLam _ _ _ sx RPc LG2 (fun b Hb => Hb) FR2 CS2 PO2 PJ2).
    + intros Hk0 m3 R' CH3 BK3 PX3 RPF R10F. left.
      apply (s_arm0 L2 A2 mem2 md2 peak2 cnt2 fail2 tn okr m3 R' RPc RD2 LG2 FR2 AUX2 PO2 JN PK CN FA);
        [rewrite <- EB; exact RF2 | exact LZ | exact NL0 | exact CH3 | exact PX3 | exact RPF | exact R10F].
    + intros Hk0. exfalso. apply Hk0. rewrite G10', Er. reflexivity.
    + intros Hk0. exfalso. apply Hk0. rewrite G10', Er. reflexivity.
  - assert (Hin : In (a, nn) Lam2) by (rewrite EL; left; reflexivity).
    assert (INC : incl sLam Lam2) by (intros bb Hb; rewrite EL; right; exact Hb).
    pose proof (s_hw_succ L2 A2 regs2 mem2 md2 Lam2 _ _ _ a nn RPS LG2 Hin NBa) as HWs.
    destruct (s_post L2 A2 regs2 mem2 md2 Lam2 _ _ _ a nn RPS LG2 INC HWs) as (RPc & FR2 & AUX2 & CS2 & PO2 & OLD).
    destruct (ledger_block_range B API L2 A2 mem2 md2 Lam2 _ _ _ a nn M2 LG2 Hin) as (A1 & A2' & _).
    apply (s_ps (pi_next w) L2 A2 regs2 mem2 md2 Lam2 _ _ _ (sx + nn + 1) RPc LG2 INC FR2 CS2 PO2 PJ2).
    + intros Hk0. exfalso. rewrite G10', Er in Hk0. rewrite MState.unsigned_lit in Hk0 by lia. lia.
    + intros _ x' m3 R3 HX1 RX NC CH3 BK3 PX3 CS3 G13 G103.
      apply (s_ff w L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Qn s r m3 x' R3 HW RPS RD2 LG2 RF2 HQ En Ec Hcf
        Hdc EL NBa Ep Ef Eb CB CH3 RX NC PX3 CS3 G13).
      rewrite G103, G10', Er. reflexivity.
    + intros _ x' m3 R'' HX1 SK CH3 BK3 PX3 CS'' G1'' G10'' G11'' G12''.
      apply (pi_mc_val w).
      rewrite G10', Er in BK3.
      exact (s_colon w L2 A2 regs2 mem2 md2 Lam2 peak2 cnt2 fail2 b2 a nn Qn s r m3 x' R'' HW RPS RD2 LG2 RF2 HQ En Ec
        Hcf Hdc EL NBa Ep Ef Eb CB CH3 BK3 SK PX3 CS'' G1'' G10'' G11'' G12'').
Qed.

End Str.

Lemma pi_str : forall w c, pi_sc w c -> SR segs c (pi_next w).
Proof.
  intros w c (fxc & R & m & mdc & Lc & Ac & Lamc & tr & D & n & cap & acc & P & x & num & kids & keys & Di & -> & HD & HO &
    CS & G1 & G10 & GL & LG & NF & PIN & TP' & PX & SK & HW & CB & EXT & RMh & LA & INV & ED & PO & DEP).
  exact (pi_str_core fxc R m mdc Lc Ac Lamc tr D n cap acc P x num kids keys Di HD HO CS G1 G10 GL LG NF PIN TP' PX SK CB
    EXT RMh LA INV ED PO DEP w HW).
Qed.

Lemma pi_step : forall w c, pi_inv w c -> SR segs c (pi_next w).
Proof.
  intros w c (fxc & R & m & mdc & Lc & Ac & Lamc & tr & D & n & cap & acc & P & num & kids & keys & Di & -> & HD & CS &
    GL & LG & NF & PIN & HW & CB & EXT & RMh & LA & INV & ED & PO & DEP).
  pose proof GL as (FZ & FK & RP & RD & FR & PERM & HP & NL & NB & RS & AUX).
  pose proof RP as (M & _).
  destruct (mr_model B _ (aa_laws API) Lc Ac m mdc M) as (Hh & Hl & _).
  pose proof PO as (HN & HA & Hh0 & (_ & HNC & _) & _).
  pose proof Hh0 as ((HRW & _) & _ & _ & _ & (_ & HK24) & _ & (_ & HN40) & _).
  assert (LT : (n < cap)%nat) by (destruct INV as (H & _); lia).
  assert (KS : In (kids, 56 * Z.of_nat cap) (pis_slots o kids keys (Z.of_nat cap))).
  { unfold pis_slots, kids_blk. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia.
    apply in_or_app. left. left. reflexivity. }
  assert (KL : In (kids, 56 * Z.of_nat cap) Lamc)
    by (apply (pis_open_incl segs m Lamc v o num kids keys _ _ _ _ Di PO); apply in_or_app; left; exact KS).
  destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ _ _ M LG KL) as (KR1 & KR2 & _).
  pose proof pi_pre0 as (_ & _ & _ & _ & _ & HAC & H63 & _). pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV. pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof QSP as QS. pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  assert (KA : forall m', chg [(q, q + 8)] m m' ->
            pi_glob fxc Lc Ac m' mdc Lamc tr D /\
            ledger B Lc Ac m' Lamc (Z.max peak0 (lsum Lam0 + hpeak tr)) (cnt0 + Z.of_nat (calls tr)) fail0 /\
            pis_open segs m' (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) (map snd (rev acc))
              (map fst (rev acc)) Di).
  { intros m' CH.
    assert (CH' : chg [(v + 40, v + 48); (q, q + 8); (q + 16, q + 20)] m m')
      by (eapply chg_weaken; [|exact CH]; intros z Hz; cbn [outside] in Hz |- *; tauto).
    destruct (pi_kA3 Lc Ac m mdc Lamc _ _ _ m' D RP RD LG PERM NB FR AUX CH') as (RP' & RD' & LG' & FR' & AUX' & _).
    pose proof CH as (MU & WM & _).
    assert (MBq : forall y, 0 <= y < 2 ^ 64 -> ~ (q <= y < q + 8) -> pis_same segs m m' y).
    { intros y Hy Hq. assert (Ho : outside [(q, q + 8)] y) by (cbn [outside]; split; [lia | exact I]).
      split; [exact (MemNorm.mbyte_munch _ _ _ _ y MU Hy Ho) |
        intros Hw; exact (proj1 (rk_writable_munch _ _ m m' y MU Hy Ho) Hw)]. }
    split.
    { split; [exact FZ|]. split; [exact FK|]. split; [exact RP'|]. split; [exact RD'|]. split; [exact FR'|].
      split; [exact PERM|]. split; [exact HP|]. split; [exact NL|]. split; [exact NB|]. split; [exact RS | exact AUX']. }
    split; [exact LG'|].
    apply (pis_frame segs m (lin Lamc) m' (lin Lamc) v o num kids keys (Z.of_nat cap) (Z.of_nat n) _ _ Di num
      (Z.of_nat n) PO).
    - apply (pis_hdr_frame segs m m' v _ _ _ _ _ _ _ Hh0). intros y Hy. apply MBq; lia.
    - lia.
    - intros a k Hak. exact (pis_open_lblk segs m (lin Lamc) v o num kids keys _ _ _ _ Di PO a k Hak).
    - intros y [Hy|[(Eo & Hy)|((a & k) & Hb & Hy)]].
      + rewrite length_map, length_rev, LA in Hy. apply MBq; lia.
      + rewrite length_map, length_rev, LA in Hy.
        assert (YS : In (keys, 8 * Z.of_nat cap) Lamc).
        { apply (pis_open_incl segs m Lamc v o num kids keys _ _ _ _ Di PO). apply in_or_app. left.
          unfold pis_slots, kids_blk, keys_blk. rewrite Eo, (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia.
          cbn. right. left. reflexivity. }
        destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ _ _ M LG YS) as (Y1 & Y2 & _).
        apply MBq; lia.
      + unfold pj_holds in Hy; cbn [fst snd] in Hy.
        assert (HbL : In (a, k) Lamc)
          by (apply (pis_open_incl segs m Lamc v o num kids keys _ _ _ _ Di PO); apply in_or_app; right; exact Hb).
        destruct (ledger_block_range B API Lc Ac m mdc Lamc _ _ _ a k M LG HbL) as (Y1 & Y2 & _).
        apply MBq; lia. }
  unfold pi_frm in FR.
  rewrite pi_seg.
  eapply rk_kA; [exact Hh | exact Hl | |].
  { rewrite (pi_canon R CS).
    eapply pip_head with (p := P) (d := Z.of_nat d + 1) (vals := kids) (n := Z.of_nat n) (tb := tb).
    - rewrite <- pi_seg. exact PIN.
    - exact FR.
    - left. unfold pi_f. lia.
    - rewrite <- pi_seg. exact HK24.
    - rewrite <- pi_seg. exact HN40.
    - lia.
    - lia.
    - lia. }
  intros ms' (can & HQ & EQV).
  destruct HQ as [(Eo & ->) | [(Eo & x & a2' & m' & -> & HX & SK & CH & PX) | (Eo & x & a2' & m' & -> & HX & RX & NC & CH & PX)]].
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems, <- pi_seg.
    apply (pi_mc_val w).
    assert (JA : forall ok, jafter d o n cap acc (rest_at tb text P) ok = jval d o n cap acc [] (rest_at tb text P) ok)
      by (intros ok; rewrite Eo; apply pi_jafter_f).
    exists fxc, (ms_regs ms'), m, mdc, Lc, Ac, Lamc, tr, D, n, cap, acc, P, num, kids, keys, Di, [], [].
    split; [reflexivity|]. split; [exact HD|].
    split; [unfold pi_cs; repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]); rewrite (rk_getr_eqv _ _ XR);
      reflexivity|].
    split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
    split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
    split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
    split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
    split; [exact GL|]. split; [exact LG|]. split; [exact NF|]. split; [exact PIN|].
    split; [lia|]. split; [rewrite HW; exact CB|].
    split; [rewrite <- JA; exact EXT|].
    split; [rewrite <- JA; exact RMh|].
    split; [exact LA|]. split; [exact INV|].
    split; [rewrite app_nil_r; exact ED|].
    split; [exact PO|].
    split; [rewrite Eo; exact eq_refl | exact DEP].
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems, <- pi_seg.
    destruct (KA m' CH) as (GL' & LG' & PO').
    apply (pi_str w).
    exists fxc, (ms_regs ms'), m', mdc, Lc, Ac, Lamc, tr, D, n, cap, acc, P, x, num, kids, keys, Di.
    split; [reflexivity|]. split; [exact HD|]. split; [exact Eo|].
    split; [unfold pi_cs; repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]); rewrite (rk_getr_eqv _ _ XR);
      reflexivity|].
    split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
    split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|].
    split; [exact GL'|]. split; [exact LG'|]. split; [exact NF|].
    split; [rewrite pi_seg; exact PX|].
    split; [lia|]. split; [exact HX|]. split; [exact SK|].
    split; [lia|]. split; [rewrite HW; exact CB|].
    split; [exact EXT|]. split; [exact RMh|]. split; [exact LA|]. split; [exact INV|]. split; [exact ED|].
    split; [exact PO' | exact DEP].
  - destruct (KA m' CH) as (GL' & LG' & PO').
    rewrite <- pi_seg. eapply pi_ret; [exact EQV|]. intros R' RPF R10F. left.
    pose proof GL' as (_ & _ & RP' & RD' & _).
    assert (JN : jr_name o (rest_at tb text P) (skipn (calls tr) pi_ok) = (None, [], skipn (calls tr) pi_ok)).
    { rewrite Eo. apply pi_nm_nq. intros c r Hc. rewrite <- RX in Hc. exact (NC c r Hc). }
    assert (JI : jr_items jr_strtod d o pi_x pi_ok = (None, tr ++ [], skipn (calls tr) pi_ok)).
    { pose proof EXT as E. unfold jafter in E. exact (ext_bind_none _ _ _ _ _ _ _ _ _ JN E). }
    rewrite app_nil_r in JI.
    apply (pi_exit fxc Lc Ac m' mdc Lamc _ _ _ tr D R' None (skipn (calls tr) pi_ok) FZ FK RP' RD' LG' PERM HP NL NB
      eq_refl RS eq_refl).
    + split; [intros H; exfalso; exact (NF H) | intros _; reflexivity].
    + exact RPF.
    + exact JI.
    + split; [exact R10F|]. split; [apply (pi_after_of m' x); rewrite pi_seg; exact PX|].
      rewrite ED. apply (pis_exit_open segs m' (lin Lamc) v o num kids keys (Z.of_nat cap) (map snd (rev acc))
        (map fst (rev acc)) Di d); [rewrite length_map, length_rev, LA; exact PO' | exact HD | exact DEP].
Qed.

Lemma pi_canon0 :
  mkR_of regs0 = mkR (getr regs0 1) (reg_get regs0 2) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 5)
    (reg_get regs0 6) (reg_get regs0 7) (reg_get regs0 8) (reg_get regs0 9) (Z_to_bv 64 q) (Z_to_bv 64 v)
    (Z_to_bv 64 (if o then 1 else 0)) (reg_get regs0 13) (reg_get regs0 14) (reg_get regs0 15) (reg_get regs0 16)
    (reg_get regs0 17) (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22)
    (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (reg_get regs0 28)
    (reg_get regs0 29) (reg_get regs0 30) (reg_get regs0 31).
Proof.
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 q) by exact R10.
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 v) by exact R11.
  assert (E12 : reg_get regs0 12 = Z_to_bv 64 (if o then 1 else 0)) by exact R12.
  unfold mkR_of. rewrite E10, E11, E12. reflexivity.
Qed.

Lemma pi_final0 : forall x5 x6 x7 a0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 R',
  xregs_eqv (mkR (getr regs0 1) (reg_get regs0 2) (reg_get regs0 3) (reg_get regs0 4) x5 x6 x7
    (reg_get regs0 8) (reg_get regs0 9) a0 x11 x12 x13 x14 x15 x16 x17 (reg_get regs0 18) (reg_get regs0 19)
    (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25)
    (reg_get regs0 26) (reg_get regs0 27) x28 x29 x30 x31) R' ->
  regs_preserved regs0 R' /\ getr R' 10 = a0.
Proof.
  intros x5 x6 x7 a0 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 R' XR.
  split; [|rewrite (rk_getr_eqv _ _ XR); reflexivity].
  intros r Hr. rewrite (rk_getr_eqv _ _ XR). unfold callee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    reflexivity.
Qed.

Lemma pi_ret0 : forall fxc m mdc (ms' : machine_state) (P : config -> Prop)
    (a0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  ms_eqv (MS (mkR (getr regs0 1) (reg_get regs0 2) (reg_get regs0 3) (reg_get regs0 4) x5 x6 x7
    (reg_get regs0 8) (reg_get regs0 9) a0 x11 x12 x13 x14 x15 x16 x17 (reg_get regs0 18) (reg_get regs0 19)
    (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25)
    (reg_get regs0 26) (reg_get regs0 27) x28 x29 x30 x31) (@fp_regs fxc) (ret_pc (getr regs0 1)) (@fp_csr fxc) None m
    (seg_rom rsegs)) ms' ->
  (forall R', regs_preserved regs0 R' -> getr R' 10 = a0 ->
     P (mkCfg (@mkst fxc R' (getr regs0 1) m (seg_rom segs)) mdc)) ->
  SR segs (mkCfg ms' mdc) P.
Proof.
  intros fxc m mdc ms' P a0 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 EQV K.
  destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR).
  destruct (pi_final0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (RPF & R10F).
  pose proof pi_pre0 as (_ & _ & _ & HRA & _).
  rewrite Ems, (rk_ret_pc _ HRA).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite pi_seg; reflexivity).
  apply SR_ret. apply K; assumption.
Qed.

Lemma pi_rp0 : rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L0 A0 regs0 mem0 md0.
Proof.
  pose proof pi_pre0 as (HM & HWF & HBD & _ & _ & _ & _ & HWS & _ & HER & _).
  assert (So : forall i, 0 <= i < 8 -> 0 <= ms_libc B + 8 + i < alloc_ceiling).
  { intros i Hi. apply (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM). right. unfold static_owned. right. right. left. lia. }
  pose proof rk_ceil as HC.
  apply (rk_of_A pi_seg (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 mem0 [] regs0 HM HWF HBD (fun r _ => eq_refl));
    [apply munch_refl | apply wmono_refl | | | | | | ].
  - intros a [Ha|Ha]; [exact (HWS a Ha) | exact (HER a Ha)].
  - intros x _ _ _. exact I.
  - intros i _. exact I.
  - pose proof (So 0 ltac:(lia)). lia.
  - pose proof (So 7 ltac:(lia)). lia.
  - intros p n i Hp Hi _. destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 p n i HM Hp Hi) as (_ & B1 & B2 & _).
    split; [lia | exact I].
Qed.

Lemma pi_kA0 : forall m', chg [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q, q + 8); (q + 16, q + 20)] mem0 m' ->
  rpost B API (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 (fun _ _ => False) L0 A0 regs0 m' md0 /\
  rd_cells B m' /\ ledger B L0 A0 m' Lam0 peak0 cnt0 fail0 /\
  (st_init_done A0 = false -> auxv_pre B (ly_sec L0) pi_lo m') /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs0 - 80 <= x < spZ regs0) -> ~ (v <= x < v + 4) -> ~ (q <= x < q + 24) ->
     pis_same segs mem0 m' x).
Proof.
  intros m' (MU & WM & PR).
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RDC).
  pose proof pi_pre0 as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  pose proof rk_ceil as HC. pose proof pi_K80 as KP. pose proof QSP as QS.
  pose proof RPL as (PL & PA & PNO). pose proof DJV as DV. cbn [Frame.disjoint_from] in DV.
  pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof VZ as ((_ & (V0 & V1 & _)) & _).
  set (W := [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q, q + 8); (q + 16, q + 20)]).
  assert (WM' : wmono segs mem0 m') by (rewrite pi_seg; exact WM).
  assert (INW : forall x, ~ outside W x ->
             spZ regs0 - 80 <= x < spZ regs0 \/ v <= x < v + 4 \/ q <= x < q + 8 \/ q + 16 <= x < q + 20).
  { intros x Ho.
    destruct (Z_le_gt_dec (spZ regs0 - 80) x); [destruct (Z_lt_ge_dec x (spZ regs0)); [left; lia|]|];
    (destruct (Z_le_gt_dec v x); [destruct (Z_lt_ge_dec x (v + 4)); [right; left; lia|]|]);
    (destruct (Z_le_gt_dec q x); [destruct (Z_lt_ge_dec x (q + 8)); [right; right; left; lia|]|]);
    (destruct (Z_le_gt_dec (q + 16) x); [destruct (Z_lt_ge_dec x (q + 20)); [right; right; right; lia|]|]);
    exfalso; apply Ho; unfold W; cbn [outside]; repeat split; lia. }
  assert (MB : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs0 - 80 <= x < spZ regs0) -> ~ (v <= x < v + 4) ->
                 ~ (q <= x < q + 24) -> pis_same segs mem0 m' x).
  { intros x Hx H1 H2 H3. assert (Ho : outside W x) by (unfold W; cbn [outside]; repeat split; lia).
    split; [exact (MemNorm.mbyte_munch _ _ _ _ x MU Hx Ho) |
      intros Hw; exact (proj1 (rk_writable_munch _ _ mem0 m' x MU Hx Ho) Hw)]. }
  assert (NIW : forall x, 0 <= x < 2 ^ 64 -> ~ outside W x -> ~ in_img B x).
  { intros x Hx Ho Hi. pose proof (rk_img_bound pi_seg x Hi) as Hb. destruct (INW x Ho) as [H1|[H1|[H1|H1]]].
    - lia.
    - destruct (PNO (x - v) ltac:(lia)) as (_ & _ & _ & N4). apply N4. replace (v + (x - v)) with x by lia. exact Hi.
    - lia.
    - lia. }
  assert (NOW : forall x, owned B L0 A0 x -> outside W x).
  { intros x Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM Ho) as Lo.
    destruct (rk_outside_dec W x) as [O|O]; [exact O|]. exfalso. destruct (INW x O) as [H1|[H1|[H1|H1]]].
    - lia.
    - destruct (PNO (x - v) ltac:(lia)) as (N1 & _). apply N1. replace (v + (x - v)) with x by lia. exact Ho.
    - lia.
    - lia. }
  assert (M' : aa_MR API L0 A0 m' md0) by exact (rk_MR_A pi_seg L0 A0 mem0 m' md0 W HM MU WM' NOW NIW).
  split.
  { apply (rk_of_A pi_seg (PARSE_ITEMS_K d) L0 A0 regs0 mem0 md0 pi_E0 m' W regs0 M' HWF HBD (fun r _ => eq_refl) MU WM').
    - intros a [Ha|Ha]; [exact (HWS a Ha) | exact (HER a Ha)].
    - intros x Hx Hs He. destruct (rk_outside_dec W x) as [O|O]; [exact O|]. exfalso.
      destruct (INW x O) as [H1|[H1|[H1|H1]]].
      + apply Hs. left. lia.
      + apply He. left. lia.
      + apply He. right. left. unfold pj_in_set. lia.
      + apply He. right. left. unfold pj_in_set. lia.
    - intros i Hi. apply NOW. right. unfold static_owned. right. right. left. lia.
    - assert (So : owned B L0 A0 (ms_libc B + 8)) by (right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM So). lia.
    - assert (So : owned B L0 A0 (ms_libc B + 15)) by (right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM So). lia.
    - intros p n i Hp Hi He. destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 p n i HM Hp Hi) as (_ & B1 & B2 & _).
      split; [lia|]. destruct (rk_outside_dec W (ptr_addr L0 p + i)) as [O|O]; [exact O|]. exfalso.
      destruct (INW _ O) as [H1|[H1|[H1|H1]]]; [lia | apply He; left; lia | lia | lia]. }
  split; [exact (pi_rd_munch mem0 m' W RDC MU NIW)|].
  split.
  { apply (rk_ledger_keep L0 A0 mem0 m' Lam0 peak0 cnt0 fail0 LG0).
    - intros a Ha. pose proof (pi_statics_img a Ha) as Hi. pose proof (rk_img_bound pi_seg a Hi) as Ra.
      refine (proj1 (MB a ltac:(lia) ltac:(lia) _ ltac:(lia))).
      intros Hv. destruct (PNO (a - v) ltac:(lia)) as (_ & _ & _ & N4). apply N4.
      replace (v + (a - v)) with a by lia. exact Hi.
    - intros a k i HIn Hi.
      destruct (ledger_block_range B API L0 A0 mem0 md0 Lam0 _ _ _ a k HM LG0 HIn) as (R1 & R2 & _).
      pose proof LG0 as (_ & _ & _ & _ & _ & LF0). rewrite Forall_forall in LF0.
      destruct (LF0 _ HIn) as (Lk & _). cbn [fst snd] in Lk.
      pose proof (pi_v_heads L0 A0 mem0 md0 Lam0 [] _ _ _ pi_rp0 LG0 (Permutation_refl _)
        (fun a0 k0 (H : In (a0, k0) []) => match H with end) a k (a - 16 + i) HIn ltac:(lia)) as NV.
      refine (proj1 (MB (a - 16 + i) ltac:(lia) ltac:(lia) _ ltac:(lia))). lia. }
  split.
  { intros HD.
    assert (AX0 : auxv_pre B (ly_sec L0) pi_lo mem0).
    { unfold pi_lo. destruct (Z.leb_spec (spZ regs0) v) as [Hsv|Hsv].
      - exact (PvGlue.auxv_join B _ _ _ _ (QAUX HD) (PA Hsv HD)).
      - replace (Z.max (q + 24) (spZ regs0)) with (q + 24) by lia. exact (QAUX HD). }
    apply (rk_auxv_keep (ly_sec L0) pi_lo mem0 m' AX0).
    - intros i Hi.
      assert (So : owned B L0 A0 (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM So) as Lo.
      refine (proj1 (MB (ms_libc B + 8 + i) ltac:(lia) ltac:(lia) _ ltac:(lia))).
      intros Hv. destruct (PNO (ms_libc B + 8 + i - v) ltac:(lia)) as (N1 & _).
      apply N1. replace (v + (ms_libc B + 8 + i - v)) with (ms_libc B + 8 + i) by lia. exact So.
    - intros a Ha. unfold pi_lo in Ha. refine (proj1 (MB a ltac:(lia) ltac:(lia) _ ltac:(lia))).
      destruct (Z.leb_spec (spZ regs0) v); lia. }
  exact MB.
Qed.

Lemma pi_hdr0 : forall m',
  chg [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q, q + 8); (q + 16, q + 20)] mem0 m' ->
  bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) ->
  pj_hdr segs m' v (5 + pis_oz o) 0 0 0 0 0 0.
Proof.
  intros m' CH TY.
  destruct (pi_kA0 m' CH) as (_ & _ & _ & _ & MB).
  pose proof CH as (_ & WM & _).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV. pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof VZ as ((_ & (V0 & V1 & _)) & _). pose proof pi_K80 as KP.
  apply (pis_hdr_ty segs mem0 m' v (5 + pis_oz o) VZ).
  - destruct o; cbn [pis_oz]; lia.
  - replace (5 + pis_oz o) with (if o then 6 else 5) by (destruct o; reflexivity). rewrite pi_seg. exact TY.
  - intros x Hx. exact (proj1 (MB x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
  - intros x _ Hw. unfold writable_at in Hw |- *. rewrite pi_seg in Hw |- *. exact (WM _ Hw).
Qed.

Lemma pi_e_deep : forall m' R', 31 < Z.of_nat d ->
  chg [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q + 16, q + 20)] mem0 m' ->
  bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) -> pi_q m' q text len p0 (Z.of_nat d + 1) tb ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 (-1) ->
  pi_post (mkCfg (@mkst fx R' (getr regs0 1) m' (seg_rom segs)) md0).
Proof.
  intros m' R' Hd CH TY PQ RPF R10F.
  assert (CH' : chg [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q, q + 8); (q + 16, q + 20)] mem0 m')
    by (eapply chg_weaken; [|exact CH]; intros z Hz; cbn [outside] in Hz |- *; tauto).
  destruct (pi_kA0 m' CH') as (RP' & RD' & LG' & _ & _).
  pose proof (pi_hdr0 m' CH' TY) as Hh.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  pose proof LG0 as (_ & (PK0 & _) & _).
  exists fx, L0, A0, R', m', md0, Lam0, peak0, cnt0, fail0, pi_ok, None, [], pi_ok, [].
  split; [reflexivity|]. split; [exact FRM|]. split; [intros r _; reflexivity|].
  split; [exact (pi_rp_exit L0 A0 m' md0 [] R' RP' RPF)|].
  split; [exact RD'|]. split; [exact LG'|].
  split; [apply jr_items_deep; unfold MAXD; lia|].
  split; [exact (pi_oks 0)|]. split; [cbn [calls]; lia|]. split; [apply fail_after_none; cbn [calls]; lia|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  split; [intros a k []|].
  split; [cbn [hpeak]; lia|]. split; [cbn [hpeak]; lia|].
  split; [exact RES0|].
  split; [exact R10F|].
  split.
  { destruct PQ as (P1 & P2 & P3 & P4 & _). exists p0, (Z.of_nat d + 1).
    split; [lia|]. split; [lia|]. rewrite pi_seg. split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact P4]. }
  exact (pis_fd_hdr0 segs m' (lin Lam0) (MAXD - d) v (5 + pis_oz o) 0 0 Hh).
Qed.

Lemma pi_e_close : forall m' x R', Z.of_nat d <= 31 -> p0 + 1 <= x < text + len ->
  skip (rest_at tb text (p0 + 1)) = closer o :: rest_at tb text (x + 1) ->
  chg [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q, q + 8); (q + 16, q + 20)] mem0 m' ->
  bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) -> pj_in_ok rsegs m' q text len (x + 1) (Z.of_nat d) tb ->
  regs_preserved regs0 R' -> getr R' 10 = Z_to_bv 64 0 ->
  pi_post (mkCfg (@mkst fx R' (getr regs0 1) m' (seg_rom segs)) md0).
Proof.
  intros m' x R' Hd HX SK CH TY PX RPF R10F.
  destruct (pi_kA0 m' CH) as (RP' & RD' & LG' & _ & _).
  pose proof (pi_hdr0 m' CH TY) as Hh.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  pose proof LG0 as (_ & (PK0 & _) & _).
  assert (HS : (S d <= MAXD)%nat) by (unfold MAXD; lia).
  assert (JI : jr_items jr_strtod d o (rest_at tb text p0) pi_ok =
               (Some (mk o [], rest_at tb text (x + 1)), [], pi_ok)).
  { change (rest_at tb text p0) with pi_x. rewrite pi_x_cons, (jr_items_eq d o (opener o) _ pi_ok HS), SK.
    cbv beta iota. rewrite Z.eqb_refl. reflexivity. }
  pose proof (skip_len (rest_at tb text (p0 + 1))) as SL. rewrite SK in SL. cbn [length] in SL.
  pose proof pi_x_cons as XC. unfold pi_x in XC.
  assert (LX : length (rest_at tb text p0) = S (length (rest_at tb text (p0 + 1)))) by (rewrite XC; reflexivity).
  exists fx, L0, A0, R', m', md0, Lam0, peak0, cnt0, fail0, pi_ok, (Some (mk o [], rest_at tb text (x + 1))), [], pi_ok,
    [].
  split; [reflexivity|]. split; [exact FRM|]. split; [intros r _; reflexivity|].
  split; [exact (pi_rp_exit L0 A0 m' md0 [] R' RP' RPF)|].
  split; [exact RD'|]. split; [exact LG'|].
  split; [exact JI|].
  split; [exact (pi_oks 0)|]. split; [cbn [calls]; lia|]. split; [apply fail_after_none; cbn [calls]; lia|].
  split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
  split; [intros a k []|].
  split; [cbn [hpeak]; lia|]. split; [cbn [hpeak]; lia|].
  split; [exact RES0|].
  split; [exact R10F|].
  split.
  { replace (text + len - Z.of_nat (length (rest_at tb text (x + 1)))) with (x + 1)
      by (rewrite (pi_rest_len tb text len (x + 1) TL ltac:(lia)); lia).
    rewrite pi_seg. exact PX. }
  split.
  { assert (ES : pis_slots o 0 0 0 ++ [] = []) by (destruct o; reflexivity).
    pose proof (pis_close segs m' (lin Lam0) v o 0 0 0 0 [] [] (pis_init segs m' (lin Lam0) v o Hh)) as PN.
    rewrite ES in PN. exact PN. }
  cbn [lsum]. lia.
Qed.

Lemma pi_loop : forall w c, pi_inv w c -> SR segs c pi_post.
Proof. exact (SR_loop segs nat (fun w0 => w0) pi_inv pi_post pi_step). Qed.

Lemma pi_e_grow : forall R m' x, Z.of_nat d <= 31 -> p0 + 1 <= x <= text + len ->
  rest_at tb text x = skip (rest_at tb text (p0 + 1)) ->
  (forall c r, rest_at tb text x = c :: r -> c <> closer o) ->
  chg [(spZ regs0 - 80, spZ regs0); (v, v + 4); (q, q + 8); (q + 16, q + 20)] mem0 m' ->
  bytes_at rsegs m' v (le4 (Z_to_bv 64 (if o then 6 else 5))) -> pj_in_ok rsegs m' q text len x (Z.of_nat d + 1) tb ->
  pi_frm m' -> pi_cs0 R -> getr R 1 = Z_to_bv 64 0x150b8 -> getr R 10 = Z_to_bv 64 v ->
  SR segs (mkCfg (@mkst fx R (Z_to_bv 64 0x147e8) m' (seg_rom segs)) md0) pi_post.
Proof.
  intros R m' x Hd HX RX NC CH TY PX FR CS G1 G10.
  destruct (pi_kA0 m' CH) as (RP' & RD' & LG' & AUX' & _).
  pose proof (pi_hdr0 m' CH TY) as Hh.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & FRM & _).
  pose proof LG0 as (_ & (PK0 & _) & _).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (Q0 & Q1 & T0 & TP & TE & QT & TL & Q8 & D32).
  assert (HS : (S d <= MAXD)%nat) by (unfold MAXD; lia).
  assert (HD : (d < MAXD)%nat) by (unfold MAXD; lia).
  assert (JT : forall ok, jr_items jr_strtod d o pi_x ok = jturn d o 0 0 [] (rest_at tb text x) ok).
  { intros ok. rewrite pi_x_cons, (jr_items_eq d o (opener o) _ ok HS), <- RX.
    destruct (rest_at tb text x) as [|c r] eqn:E; [reflexivity|].
    rewrite (proj2 (Z.eqb_neq c (closer o)) (NC c r eq_refl)). reflexivity. }
  pose proof (skip_len (rest_at tb text (p0 + 1))) as SL. rewrite <- RX in SL.
  pose proof pi_x_cons as XC.
  assert (LX : length pi_x = S (length (rest_at tb text (p0 + 1)))) by (rewrite XC; reflexivity).
  assert (GL : pi_glob fx L0 A0 m' md0 Lam0 [] []).
  { split; [exact FRM|]. split; [intros r _; reflexivity|]. split; [exact RP'|]. split; [exact RD'|]. split; [exact FR|].
    split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [reflexivity|].
    split; [intros a k []|]. split; [exact RES0 | exact AUX']. }
  assert (gLG : ledger B L0 A0 m' Lam0 (Z.max peak0 (lsum Lam0 + hpeak [])) (cnt0 + Z.of_nat (calls [])) fail0).
  { replace (Z.max peak0 (lsum Lam0 + hpeak [])) with peak0 by (cbn [hpeak]; lia).
    replace (cnt0 + Z.of_nat (calls [])) with cnt0 by (cbn [calls]; lia). exact LG'. }
  assert (gNF : ~ (cnt0 <= fail0 < cnt0 + Z.of_nat (calls []))) by (cbn [calls]; lia).
  assert (gPIN : pj_in_ok segs m' q text len x (Z.of_nat d + 1) tb) by (rewrite pi_seg; exact PX).
  assert (gCB : Z.of_nat (calls []) + 2 * Z.of_nat (length (rest_at tb text x)) + 2 <= 2 * Z.of_nat (length pi_x))
    by (cbn [calls]; lia).
  assert (gEXT : ext (jr_items jr_strtod d o pi_x pi_ok) []
                   (jturn d o 0 0 [] (rest_at tb text x) (skipn (calls []) pi_ok))).
  { change (skipn (calls []) pi_ok) with pi_ok. rewrite <- (JT pi_ok). apply pi_ext_refl. }
  assert (gROOM : room_run RF (rf_run RF b0 []) (snd (fst (jturn d o 0 0 [] (rest_at tb text x) [])))).
  { change (rf_run RF b0 []) with b0. rewrite <- (JT []). exact ROOM. }
  assert (gINV : inv 0 0) by (unfold inv; lia).
  assert (gED : ([] : list (Z * Z)) = pis_slots o 0 0 (Z.of_nat 0) ++ []) by (destruct o; reflexivity).
  assert (gPO : pis_open segs m' (lin Lam0) v o 0 0 0 (Z.of_nat 0) (Z.of_nat 0)
                  (map snd (rev ([] : list (list Z * jv)))) (map fst (rev ([] : list (list Z * jv)))) [])
    by exact (pis_init segs m' (lin Lam0) v o Hh).
  assert (gDEP : Forall (fun u => (depth u <= MAXD - S d)%nat) (map snd (rev ([] : list (list Z * jv)))))
    by constructor.
  eapply SR_bind.
  { exact (pi_sep_core fx R m' md0 L0 A0 Lam0 [] [] 0 0 [] x 0 0 0 [] HD CS (or_intror G1) G10 GL gLG gNF gPIN gCB
      gEXT gROOM eq_refl gINV gED gPO gDEP (S (length (rest_at tb text x))) ltac:(lia)). }
  intros c' [HP|(w' & _ & HI)]; [apply SR_ret; exact HP | exact (pi_loop w' c' HI)].
Qed.

Lemma pi_main : SR segs (mkCfg (mkst regs0 (Z_to_bv 64 PARSE_ITEMS) mem0 (seg_rom segs)) md0) pi_post.
Proof using All.
  pose proof ENV as (SEG & TP & ERR & GG & GD & PRE & SP47 & GTOP & FRM & RDC).
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & HAUX).
  destruct (mr_model B _ (aa_laws API) L0 A0 mem0 md0 HM) as (Hh & Hl & _).
  pose proof (pj_in_ok_bounds _ _ _ _ _ _ _ _ PIN0) as (Q0 & Q1 & T0 & TP' & TE & QT & TL & Q8 & D32).
  pose proof DJV as DV. cbn [Frame.disjoint_from] in DV. pose proof DJS as DJ. cbn [Frame.disjoint_from] in DJ.
  pose proof VZ as ((_ & VS) & _). pose proof VS as (V0 & V1 & _).
  pose proof rk_ceil as HC. pose proof pi_K80 as KP.
  rewrite pi_seg.
  eapply rk_kA; [exact Hh | exact Hl | |].
  { rewrite pi_canon0. unfold PARSE_ITEMS.
    eapply pip_entry with (p := p0) (d := Z.of_nat d) (tb := tb).
    - rewrite <- pi_seg. exact PIN0.
    - exact PLT.
    - rewrite <- pi_seg. apply (pi_wr_stk _ _ _ _ _ _ VS); lia.
    - change (bv_unsigned (reg_get regs0 2)) with (spZ regs0).
      split; [lia|]. split; [lia|]. intros i Hi. rewrite <- pi_seg. exact (HWS (spZ regs0 - 80 + i) ltac:(lia)).
    - cbn [disjoint_from]. repeat split; lia.
    - change (bv_unsigned (reg_get regs0 2)) with (spZ regs0). cbn [disjoint_from]. repeat split; lia. }
  intros ms' (can & (a1' & a2' & a3' & a4' & a5' & m' & ARMS) & EQV).
  destruct ARMS as [(Hd & -> & CH & TY & PQ) | [(Hd & x & -> & HX & SK & CH & TY & PX) |
    (Hd & x & -> & HX & RX & NC & CH & TY & PX & FRx)]].
  - rewrite <- pi_seg. eapply pi_ret0; [exact EQV|]. intros R' RPF R10F.
    exact (pi_e_deep m' R' Hd CH TY PQ RPF R10F).
  - rewrite <- pi_seg. eapply pi_ret0; [exact EQV|]. intros R' RPF R10F.
    exact (pi_e_close m' x R' Hd HX SK CH TY PX RPF R10F).
  - destruct (rk_eqv_shape _ _ _ _ _ _ EQV) as (Ems & XR). rewrite Ems, <- pi_seg.
    apply (pi_e_grow (ms_regs ms') m' x Hd HX RX NC CH TY PX FRx).
    + unfold pi_cs0. repeat (split; [rewrite (rk_getr_eqv _ _ XR); reflexivity|]). rewrite (rk_getr_eqv _ _ XR).
      reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
    + rewrite (rk_getr_eqv _ _ XR). reflexivity.
Qed.

End PI.

Theorem parse_items_step : forall {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (F : ResForm),
  YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  forall d, ((d < MAXD)%nat -> forall fx, @parse_value_contract fx rc B API F (S d)) ->
    (forall fx, @grow_contract fx rc B API F) -> (forall fx, @parse_string_contract fx rc B API F) ->
    memset_contract -> (forall fx, @fuzz_free_contract fx rc B API F) ->
    forall fx, @parse_items_contract fx rc B API F d.
Proof.
  intros rc B API F AXh COh d PV GR PS MS FF fx.
  intros L A regs mem md Lam peak cnt fail b q text len p tb v o H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16
    H17 H18 H19 H20.
  exact (@pi_main fx rc B API F L A regs mem md Lam peak cnt fail b q text len p tb v o d H1 H2 H3 H4 H5 H6 H7 H8 H9 H10
    H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 AXh COh PV GR PS MS FF).
Qed.
