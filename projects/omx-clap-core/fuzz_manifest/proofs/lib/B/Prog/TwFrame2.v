(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/TwFrame2.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/TwFrame2.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Prog/TwFrame2.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrStr StrBytes TwoWay TwSearch TwMaxSuf TwCrit TwSearchPf.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import TwFrame1.
Import ListNotations.
Open Scope Z_scope.

Lemma tw_gt_props :
  (forall a b, Z.gtb a b = true -> Z.gtb b a = false) /\
  (forall a b, a <> b -> Z.gtb a b = true \/ Z.gtb b a = true) /\
  (forall a b d, Z.gtb a b = true -> Z.gtb b d = true -> Z.gtb a d = true).
Proof.
  split; [|split].
  - intros a b H. rewrite Z.gtb_ltb in *. apply Z.ltb_lt in H. apply Z.ltb_ge. lia.
  - intros a b H. rewrite !Z.gtb_ltb. destruct (Z.lt_trichotomy a b) as [L|[L|L]]; [|contradiction|].
    + right. apply Z.ltb_lt. exact L.
    + left. apply Z.ltb_lt. lia.
  - intros a b d H1 H2. rewrite Z.gtb_ltb in *. apply Z.ltb_lt in H1, H2. apply Z.ltb_lt. lia.
Qed.

Lemma tw_lt_props :
  (forall a b, Z.ltb a b = true -> Z.ltb b a = false) /\
  (forall a b, a <> b -> Z.ltb a b = true \/ Z.ltb b a = true) /\
  (forall a b d, Z.ltb a b = true -> Z.ltb b d = true -> Z.ltb a d = true).
Proof.
  split; [|split].
  - intros a b H. apply Z.ltb_lt in H. apply Z.ltb_ge. lia.
  - intros a b H. destruct (Z.lt_trichotomy a b) as [L|[L|L]]; [|contradiction|].
    + left. apply Z.ltb_lt. exact L.
    + right. apply Z.ltb_lt. lia.
  - intros a b d H1 H2. apply Z.ltb_lt in H1, H2. apply Z.ltb_lt. lia.
Qed.

Lemma tw_crit_of_runs : forall (x : list Z) c1 p1 c2 p2, (1 <= length x)%nat ->
  msuf_run Z.gtb x 0 0 1 1 c1 p1 -> msuf_run Z.ltb x 0 0 1 1 c2 p2 ->
  TW_CRIT x (fst (tw_cut c1 p1 c2 p2)) (snd (tw_cut c1 p1 c2 p2)).
Proof.
  intros x c1 p1 c2 p2 Hl R1 R2.
  destruct tw_gt_props as (G1 & G2 & G3). destruct tw_lt_props as (L1 & L2 & L3).
  destruct (maxsuf_ok Z.gtb x c1 p1 G1 G2 G3 Hl R1) as [M1 S1].
  destruct (maxsuf_ok Z.ltb x c2 p2 L1 L2 L3 Hl R2) as [M2 S2].
  exact (crit_ok x c1 p1 c2 p2 Hl M1 S1 M2 S2).
Qed.

Lemma tw_sv_none : forall A (hb nb : list byte), find_first (map bv_unsigned hb) (map bv_unsigned nb) = None ->
  strstr_val A hb nb = 0.
Proof. intros A hb nb H. unfold strstr_val. rewrite H. reflexivity. Qed.

Lemma tw_sv_some : forall A (hb nb : list byte) pos,
  find_first (map bv_unsigned hb) (map bv_unsigned nb) = Some pos -> strstr_val A hb nb = A + Z.of_nat pos.
Proof. intros A hb nb pos H. unfold strstr_val. rewrite H. reflexivity. Qed.

Lemma tw_at_u : forall (l : list byte) i b, nth_error l i = Some b -> at_ (map bv_unsigned l) i = bv_unsigned b.
Proof.
  induction l as [|y l IH]; intros [|i] b E; cbn in *; try discriminate.
  - inversion E; reflexivity.
  - apply IH. exact E.
Qed.

Lemma tw_nth_ex : forall (l : list byte) i, (i < length l)%nat -> exists b, nth_error l i = Some b.
Proof. intros l i H. destruct (nth_error l i) as [b|] eqn:E; [eauto|]. apply nth_error_None in E. lia. Qed.

Lemma tw_nz_of_nth : forall (l : list byte) i b, ~ In (Z_to_bv 8 0) l -> nth_error l i = Some b -> bv_unsigned b <> 0.
Proof.
  intros l i b NZ E Hb. apply NZ. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|].
  apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma tw_bytes_skip : forall segs m A (bs : list byte) k, bytes_at segs m A bs -> (k <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros segs m A bs k (Ha & Hl & H) Hk. split; [lia|]. rewrite length_skipn. split; [lia|].
  intros i Hi. replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma tw_memchr_ok : forall A (hb hs : list byte) j n, ~ In (Z_to_bv 8 0) hb -> (j <= length hb)%nat ->
  (- (A + Z.of_nat (length hb) + 1)) mod 8 <= Z.of_nat (length hs) ->
  memchr_ok (A + Z.of_nat j) 0 n (skipn j hb ++ Z_to_bv 8 0 :: hs).
Proof.
  intros A hb hs j n NZ Hj PAD. apply memchr_ok_cstr.
  all: first [ intros Hin; apply NZ; rewrite <- (firstn_skipn j hb); apply in_or_app; right; exact Hin
             | rewrite length_skipn; replace (A + Z.of_nat j + Z.of_nat (length hb - j)) with (A + Z.of_nat (length hb)) by lia;
               exact PAD ].
Qed.

Lemma tw_memchr_res_hit : forall A (hb hs : list byte) j n, ~ In (Z_to_bv 8 0) hb -> (j <= length hb)%nat ->
  Z.of_nat (length hb - j) < n ->
  memchr_res (A + Z.of_nat j) 0 n (skipn j hb ++ Z_to_bv 8 0 :: hs) = A + Z.of_nat (length hb).
Proof.
  intros A hb hs j n NZ Hj Hn. unfold memchr_res. rewrite (find_byte_cstr 0); cbv beta iota.
  all: first [ rewrite length_skipn; lia
             | intros Hin; apply NZ; rewrite <- (firstn_skipn j hb); apply in_or_app; right; exact Hin ].
Qed.

Lemma tw_memchr_res_miss : forall A (hb hs : list byte) j n, ~ In (Z_to_bv 8 0) hb -> (j <= length hb)%nat ->
  n <= Z.of_nat (length hb - j) ->
  memchr_res (A + Z.of_nat j) 0 n (skipn j hb ++ Z_to_bv 8 0 :: hs) = 0.
Proof.
  intros A hb hs j n NZ Hj Hn. unfold memchr_res. rewrite (find_byte_cstr_short 0); cbv beta iota.
  all: first [ reflexivity | rewrite length_skipn; lia
             | intros Hin; apply NZ; rewrite <- (firstn_skipn j hb); apply in_or_app; right; exact Hin ].
Qed.

Lemma tw_skipn_str : forall (hb hs : list byte) j, (j <= length hb)%nat ->
  skipn j (hb ++ Z_to_bv 8 0 :: hs) = skipn j hb ++ Z_to_bv 8 0 :: hs.
Proof. intros hb hs j Hj. rewrite skipn_app. replace (j - length hb)%nat with 0%nat by lia. reflexivity. Qed.

Lemma tw_memcmp_total : forall (nb : list byte) c p, (1 <= p)%nat -> (c + p <= length nb)%nat ->
  exists v, memcmp_model (nb ++ [Z_to_bv 8 0]) (skipn p (nb ++ [Z_to_bv 8 0])) c = Some v.
Proof.
  intros nb c p Hp Hcp. apply memcmp_model_total.
  - rewrite length_app. cbn [length]. lia.
  - rewrite length_skipn, length_app. cbn [length]. lia.
Qed.

Lemma tw_memcmp_periodic : forall (nb : list byte) c p v, (1 <= p)%nat -> (c + p <= length nb)%nat ->
  memcmp_model (nb ++ [Z_to_bv 8 0]) (skipn p (nb ++ [Z_to_bv 8 0])) c = Some v ->
  (v = 0 <-> tw_periodic (map bv_unsigned nb) c p = true).
Proof.
  intros nb c p v Hp Hcp H. rewrite (tw_memcmp_zero c _ _ v H). unfold tw_periodic.
  rewrite forallb_forall. split.
  - intros G j Hj. apply in_seq in Hj. apply Z.eqb_eq. specialize (G j ltac:(lia)).
    rewrite tw_nth_map_skipn in G. rewrite map_app in G. unfold at_ in G |- *.
    rewrite !app_nth1 in G by (rewrite length_map; lia). exact G.
  - intros G j Hj. specialize (G j ltac:(apply in_seq; lia)). apply Z.eqb_eq in G.
    rewrite tw_nth_map_skipn. rewrite map_app. unfold at_ in G |- *.
    rewrite !app_nth1 by (rewrite length_map; lia). exact G.
Qed.

Lemma tw_inv0 : forall (x y : list Z), (1 <= length x)%nat -> TW_INV x y 0 0.
Proof. intros x y Hl. split; [intros i Hi; lia|]. split; [lia|]. intros j Hj; lia. Qed.

Lemma tw_none_short : forall (x y : list Z), (1 <= length x)%nat -> (length y < length x)%nat -> find_first y x = None.
Proof. intros x y Hl Hy. apply (search_end_ok x y 0%nat 0%nat Hl (tw_inv0 x y Hl)). lia. Qed.

Lemma tw_rscan_eq : forall x y pos k f, (k < length x)%nat -> at_ x k = at_ y (pos + k) ->
  rscan x y pos k (S f) = rscan x y pos (S k) f.
Proof.
  intros x y pos k f Hk E. cbn [rscan]. rewrite (proj2 (Nat.ltb_lt _ _) Hk), E, Z.eqb_refl. reflexivity.
Qed.

Lemma tw_rscan_neq : forall x y pos k f, at_ x k <> at_ y (pos + k) -> rscan x y pos k (S f) = k.
Proof.
  intros x y pos k f E. cbn [rscan]. rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r. reflexivity.
Qed.

Lemma tw_rscan_end : forall x y pos f, rscan x y pos (length x) f = length x.
Proof. intros x y pos [|f]; cbn [rscan]; [reflexivity|]. rewrite Nat.ltb_irrefl. reflexivity. Qed.

Lemma tw_lscan_eq : forall x y pos mem k, (mem < S k)%nat -> at_ x k = at_ y (pos + k) ->
  lscan x y pos mem (S k) = lscan x y pos mem k.
Proof.
  intros x y pos mem k Hk E. cbn [lscan]. rewrite (proj2 (Nat.ltb_lt _ _) Hk), E, Z.eqb_refl. reflexivity.
Qed.

Lemma tw_lscan_neq : forall x y pos mem k, at_ x k <> at_ y (pos + k) -> lscan x y pos mem (S k) = S k.
Proof.
  intros x y pos mem k E. cbn [lscan]. rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r. reflexivity.
Qed.

Lemma tw_lscan_stop : forall x y pos mem k, (k <= mem)%nat -> lscan x y pos mem k = k.
Proof.
  intros x y pos mem [|k] Hk; cbn [lscan]; [reflexivity|].
  replace (mem <? S k)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.

Lemma tw_lscan_le : forall x y pos mem k, (lscan x y pos mem k <= k)%nat.
Proof.
  intros x y pos mem k. induction k as [|k IH]; cbn [lscan]; [lia|].
  destruct ((mem <? S k)%nat && Z.eqb (at_ x k) (at_ y (pos + k)))%bool; lia.
Qed.

Lemma tw_body_notin : forall x y c p mem0 pos mem, inset x (at_ y (pos + length x - 1)) = false ->
  tw_body x y c p mem0 pos mem = TwNext (pos + length x) 0.
Proof. intros x y c p mem0 pos mem H. unfold tw_body. cbv zeta. rewrite H. reflexivity. Qed.

Lemma tw_body_skip : forall x y c p mem0 pos mem, inset x (at_ y (pos + length x - 1)) = true ->
  (length x - shift_of x (at_ y (pos + length x - 1)) <> 0)%nat ->
  tw_body x y c p mem0 pos mem = TwNext (pos + Nat.max (length x - shift_of x (at_ y (pos + length x - 1))) mem) 0.
Proof.
  intros x y c p mem0 pos mem H K. unfold tw_body. cbv zeta. rewrite H. cbn [negb].
  rewrite (proj2 (Nat.eqb_neq _ _) K). reflexivity.
Qed.

Lemma tw_body_scan : forall x y c p mem0 pos mem, inset x (at_ y (pos + length x - 1)) = true ->
  (length x - shift_of x (at_ y (pos + length x - 1)) = 0)%nat ->
  tw_body x y c p mem0 pos mem =
    if (rscan x y pos (Nat.max c mem) (length x - Nat.max c mem) <? length x)%nat
    then TwNext (pos + (rscan x y pos (Nat.max c mem) (length x - Nat.max c mem) + 1 - c)) 0
    else if (lscan x y pos mem c <=? mem)%nat then TwFound pos else TwNext (pos + p) mem0.
Proof.
  intros x y c p mem0 pos mem H K. unfold tw_body. cbv zeta. rewrite H, K. reflexivity.
Qed.

Lemma tw_p_le : forall x c p0, TW_CRIT x c p0 -> (tw_p x c p0 <= length x)%nat.
Proof.
  intros x c p0 (Hc & Hp & Hcp & _). unfold tw_p. destruct c as [|c'].
  - cbn [tw_periodic seq forallb]. lia.
  - destruct (tw_periodic x (S c') p0); lia.
Qed.

Lemma tw_mem0_le : forall x c p0, (tw_mem0 x c p0 <= length x)%nat.
Proof. intros x c p0. unfold tw_mem0. destruct (tw_periodic x c p0); lia. Qed.
