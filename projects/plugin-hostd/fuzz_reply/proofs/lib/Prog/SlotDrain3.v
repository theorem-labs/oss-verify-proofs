From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT SlotKept SlotPack
  AllocPack AllocPackRoom AllocBound AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotInv SlotParse SlotCaps3 SlotRI3
  RelayRunT RelayRunF RelayRep HarnessRep RelayModel RelayKeys ListTr send_line_b_c drain_b_c SlotRun3 SlotP5R3G
  SlotDrain3Aux.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Lemma NMAX_v : NMAX = 536879104.
Proof. reflexivity. Qed.

Lemma P29 : 2 ^ 29 = 536870912.
Proof. reflexivity. Qed.

Lemma P26 : 2 ^ 26 = 67108864.
Proof. reflexivity. Qed.

Lemma P25 : 2 ^ 25 = 33554432.
Proof. reflexivity. Qed.

Definition d3pow (c : Z) : Prop := c = 0 \/ exists k, 0 <= k /\ c = 8 * 2 ^ k.

Lemma pow8_grow k : 0 <= k -> 8 * 2 ^ k < 2 ^ 25 -> 32 * (8 * 2 ^ k) <= 2 ^ 29 /\ k < 22.
Proof.
  intros Hk H. rewrite P25 in H. rewrite P29. destruct (Z_lt_le_dec k 22) as [L|L].
  - assert (2 ^ k <= 2 ^ 21) by (apply Z.pow_le_mono_r; lia). assert (E : 2 ^ 21 = 2097152) by reflexivity. lia.
  - assert (2 ^ 22 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). assert (E : 2 ^ 22 = 4194304) by reflexivity. lia.
Qed.

Lemma pow_succ8 k : 0 <= k -> 8 * 2 ^ k * 2 = 8 * 2 ^ (k + 1).
Proof. intros Hk. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia. Qed.

Lemma sl_cap_ind f : forall mx no cap rem j o j' o',
  fst (snd (sl_run f mx no cap rem j o)) = fst (snd (sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; [reflexivity|]. cbn [sl_run]. cbv zeta.
  destruct (rem <=? 0); [reflexivity|].
  match goal with |- context [if cap <? ?x then _ else _] => destruct (cap <? x) end; cbn [fst snd]; apply IH.
Qed.

Lemma sl_mono f : forall mx no cap rem j o, 0 <= cap -> cap <= fst (snd (sl_run f mx no cap rem j o)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Hc; [cbn; lia|]. cbn [sl_run]. cbv zeta.
  destruct (rem <=? 0); [cbn [fst snd]; lia|]. set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (Z.ltb_spec cap (no + n)) as [E|E]; cbn [fst snd].
  - specialize (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j) ltac:(lia)). lia.
  - apply IH. exact Hc.
Qed.

Lemma sl_steps mxs g f : forall mx no cap rem j o, 0 <= cap ->
  fst (snd (sl_run f mx no cap rem j o)) <= nth 0 mxs 0 -> nth 0 mxs 0 <= NMAX ->
  steps mxs j ((cap, o) :: g) (fst (sl_run f mx no cap rem j o))
    ((fst (snd (sl_run f mx no cap rem j o)), snd (snd (sl_run f mx no cap rem j o))) :: g) [].
Proof.
  pose proof NMAX_v as EN.
  induction f as [|f IH]; intros mx no cap rem j o Hc HF HN; [cbn [sl_run fst snd]; apply sp_nil|]. revert HF.
  cbn [sl_run]. cbv zeta.
  destruct (rem <=? 0); [intros _; cbn [fst snd]; apply sp_nil|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (Z.ltb_spec cap (no + n)) as [E|E]; cbn [fst snd]; intros HF.
  - pose proof (sl_mono f mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j) ltac:(lia)) as M.
    apply sp_grow0; [lia|lia|]. apply IH; [lia|exact HF|exact HN].
  - apply IH; [exact Hc|exact HF|exact HN].
Qed.

Lemma send_steps mxs g live mx no cap len j o : 0 <= cap ->
  send_line_cap live mx no cap len <= nth 0 mxs 0 -> nth 0 mxs 0 <= NMAX ->
  steps mxs j ((cap, o) :: g) (send_line_tr live mx no cap len j o)
    ((send_line_cap live mx no cap len, send_line_out live mx no cap len j o) :: g) [].
Proof.
  intros Hc HF HN. unfold send_line_tr, send_line_cap, send_line_out in *. destruct live; [|apply sp_nil].
  assert (E : fst (snd (sl_run (Z.to_nat len) mx no cap len j o)) = fst (snd (sl_run (Z.to_nat len) mx no cap len 0 adr0)))
    by apply sl_cap_ind.
  rewrite <- E. apply sl_steps; [exact Hc|rewrite E; exact HF|exact HN].
Qed.

Lemma send_mono live mx no cap len : 0 <= cap -> cap <= send_line_cap live mx no cap len.
Proof. intros Hc. unfold send_line_cap. destruct live; [apply sl_mono; exact Hc|lia]. Qed.

Definition ska (H : list (list Z)) (ka : Z) (l : list Z) : Z := snd (fst (seen_tr H ka l 0 adr0 [])).

Lemma seen_ka_c H ka l j ha ks : snd (fst (seen_tr H ka l j ha ks)) = ska H ka l.
Proof.
  unfold ska, seen_tr. destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H)|destruct (index_of x H)|];
    reflexivity.
Qed.

Lemma lines_st_ind live mx ls : forall no cap H ka j o ha ks j' o' ha' ks',
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = snd (fst (lines_run live mx no cap H ka ls j' o' ha' ks')).
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks j' o' ha' ks'; [reflexivity|].
  cbn [lines_run fst snd]. cbv zeta. rewrite !seen_ka_c. apply IH.
Qed.

Definition lrst (live : bool) (mx no cap : Z) (H : list (list Z)) (ka : Z) (ls : list (list Z)) : Z * list (list Z) * Z :=
  snd (fst (lines_run live mx no cap H ka ls 0 adr0 adr0 [])).

Lemma lines_st_c live mx ls no cap H ka j o ha ks :
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = lrst live mx no cap H ka ls.
Proof. unfold lrst. apply lines_st_ind. Qed.

Lemma lines_mono live mx ls : forall no cap H ka j o ha ks, 0 <= cap ->
  cap <= fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))).
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks Hc; [cbn; lia|]. cbn [lines_run fst snd]. cbv zeta.
  pose proof (send_mono live mx no cap (Z.of_nat (length l) + 1) Hc) as M.
  eapply Z.le_trans; [exact M|]. apply IH. lia.
Qed.

Lemma seen_steps mxs x0 x1 x3 H ka l j ha ks : 0 <= ka -> zlen l <= 6000 ->
  (Z.of_nat (length H) + 1) * 8 <= 2 ^ 29 -> 2 ^ 29 <= nth 2 mxs 0 ->
  exists u, steps mxs j [x0; x1; (ka, ha); x3] (fst (fst (seen_tr H ka l j ha ks)))
      [x0; x1; (snd (fst (seen_tr H ka l j ha ks)), fst (snd (seen_tr H ka l j ha ks))); x3] u /\
    (forall c, bcnt c u <= bcnt c (ek1 l)) /\ zsum (fun n => n) u <= zsum (fun n => n) (ek1 l) /\
    0 <= snd (fst (seen_tr H ka l j ha ks)) /\ (length (seen_arr H l) <= length H + 1)%nat.
Proof.
  intros Hk Hl HH HM. pose proof P29 as E29. pose proof NMAX_v as EN. unfold seen_tr, seen_arr, ek1.
  destruct (gesture l) as [[[|] x]|] eqn:Eg.
  - destruct (index_of x H) as [i|] eqn:Ei; cbn [fst snd]; cbv zeta.
    + exists []. split; [apply sp_nil|]. split; [intros c; change (bcnt c []) with 0; apply bcnt_nonneg|].
      split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|lia].
    + destruct (gesture_begin l x Eg) as [Ex _]. exists [Z.of_nat (length x) + 1]. split.
      * apply sp_grow2; [lia|lia|]. apply sp_copy; [lia|]. apply sp_nil.
      * split; [intros c; lia|]. split; [lia|]. split; [lia|]. rewrite length_app. cbn [length]. lia.
  - destruct (index_of x H) as [i|] eqn:Ei; cbn [fst snd].
    + exists []. split; [apply sp_free; [lia|apply sp_nil]|]. split; [intros c; unfold bcnt, zsum; cbn [fold_right]; lia|].
      split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|]. unfold swap_remove.
      pose proof (firstn_len_le (length H - 1) (set_nth i (last H []) H)). lia.
    + exists []. split; [apply sp_nil|]. split; [intros c; unfold bcnt, zsum; cbn [fold_right]; lia|].
      split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|lia].
  - exists []. cbn [fst snd]. split; [apply sp_nil|]. split; [intros c; unfold bcnt, zsum; cbn [fold_right]; lia|].
    split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|lia].
Qed.

Lemma lines_steps lv mx mxs x1 x3 : forall ls no cap H ka j o ha ks,
  0 <= cap -> 0 <= ka -> zlen H + zlen ls < 2 ^ 26 -> Forall (fun l => zlen l <= 6000) ls ->
  2 ^ 29 <= nth 2 mxs 0 -> nth 0 mxs 0 <= NMAX ->
  fst (fst (snd (fst (lines_run lv mx no cap H ka ls j o ha ks)))) <= nth 0 mxs 0 ->
  exists u, steps mxs j [(cap, o); x1; (ka, ha); x3] (fst (fst (lines_run lv mx no cap H ka ls j o ha ks)))
      [(fst (fst (snd (fst (lines_run lv mx no cap H ka ls j o ha ks)))),
        fst (fst (snd (lines_run lv mx no cap H ka ls j o ha ks)))); x1;
       (snd (snd (fst (lines_run lv mx no cap H ka ls j o ha ks))),
        snd (fst (snd (lines_run lv mx no cap H ka ls j o ha ks)))); x3] u /\
    (forall c, bcnt c u <= bcnt c (ekl ls)) /\ zsum (fun n => n) u <= zsum (fun n => n) (ekl ls) /\
    0 <= snd (snd (fst (lines_run lv mx no cap H ka ls j o ha ks))) /\
    zlen (snd (fst (snd (fst (lines_run lv mx no cap H ka ls j o ha ks))))) <= zlen H + zlen ls.
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks Hc Hk HH HF M2 MN HO.
  - exists []. cbn [lines_run fst snd]. split; [apply sp_nil|].
    split; [intros c; unfold bcnt, ekl, zsum; cbn [map concat fold_right]; lia|].
    split; [unfold ekl, zsum; cbn [map concat fold_right]; lia|]. split; [exact Hk|]. unfold zlen. cbn [length]. lia.
  - apply Forall_cons_iff in HF as [Hl HF]. revert HO. cbn [lines_run fst snd]. cbv zeta. intros HO.
    set (len := Z.of_nat (length l) + 1) in *.
    set (t1 := send_line_tr lv mx no cap len j o) in *.
    set (sn := seen_tr H ka l (j + nretF t1) ha ks) in *.
    set (p := lines_run lv mx (no + len) (send_line_cap lv mx no cap len) (seen_arr H l) (snd (fst sn)) r
                (j + nretF t1 + nretF (fst (fst sn))) (send_line_out lv mx no cap len j o) (fst (snd sn))
                (snd (snd sn))) in *.
    pose proof (send_mono lv mx no cap len Hc) as MS.
    assert (MO : send_line_cap lv mx no cap len <= fst (fst (snd (fst p)))) by (unfold p; apply lines_mono; lia).
    pose proof (send_steps mxs [x1; (ka, ha); x3] lv mx no cap len j o Hc ltac:(lia) MN) as S1.
    assert (HHs : (Z.of_nat (length H) + 1) * 8 <= 2 ^ 29)
      by (pose proof P26; pose proof P29; unfold zlen in *; cbn [length] in HH; lia).
    destruct (seen_steps mxs (send_line_cap lv mx no cap len, send_line_out lv mx no cap len j o) x1 x3 H ka l
      (j + nretF t1) ha ks Hk Hl HHs M2) as (u1 & S2 & B1 & Z1 & K1 & L1).
    fold sn in S2, B1, Z1, K1.
    assert (HH' : zlen (seen_arr H l) + zlen r < 2 ^ 26) by (unfold zlen in *; cbn [length] in HH; lia).
    destruct (IH (no + len) (send_line_cap lv mx no cap len) (seen_arr H l) (snd (fst sn))
      (j + nretF t1 + nretF (fst (fst sn)))%nat (send_line_out lv mx no cap len j o) (fst (snd sn)) (snd (snd sn))
      ltac:(lia) K1 HH' HF M2 MN HO) as (u2 & S3 & B2 & Z2 & K2 & L2).
    exists (u1 ++ u2). split.
    + change (u1 ++ u2) with ([] ++ u1 ++ u2). eapply steps_app; [exact S1|]. eapply steps_app; [exact S2|]. exact S3.
    + change (ekl (l :: r)) with (ek1 l ++ ekl r).
      split; [intros c; rewrite !bcnt_app; specialize (B1 c); specialize (B2 c); lia|].
      split; [rewrite !zsum_app; lia|]. split; [exact K2|]. fold p in L2. unfold zlen in *. cbn [length]. lia.
Qed.

Lemma push_tra_steps mxs x0 x1 x2 v n cap len j : d3pow cap -> n < 2 ^ 25 -> 0 <= len <= 6000 -> 2 ^ 29 <= nth 3 mxs 0 ->
  steps mxs j [x0; x1; x2; (16 * cap, v)] (list_push_tra v n cap len)
    [x0; x1; x2; (16 * push_cap n cap, if n =? cap then Ret j else v)] [len + 1].
Proof.
  intros Hp Hn Hl HM. pose proof P29 as E29. pose proof NMAX_v as EN. unfold list_push_tra, push_cap.
  destruct (Z.eqb_spec n cap) as [Ec|Ec].
  - destruct (Z.eqb_spec cap 0) as [Ez|Ez].
    + subst n. subst cap. cbn [app].
      refine (sp_grow3 mxs j x0 x1 x2 [] (16 * 0) v 128 [RMalloc (len + 1)] _ [len + 1] _ _ _); [lia|lia|].
      change (16 * 8) with 128. apply sp_copy; [lia|apply sp_nil].
    + subst n. destruct Hp as [Hp|(k & Hk & Ek)]; [contradiction|].
      pose proof (Z.pow_nonneg 2 k ltac:(lia)) as P0.
      destruct (pow8_grow k Hk ltac:(lia)) as [G _]. cbn [app].
      replace (RRealloc (16 * cap) (32 * cap) v) with
        (if 16 * cap =? 0 then RMalloc (32 * cap) else RRealloc (16 * cap) (32 * cap) v)
        by (rewrite (proj2 (Z.eqb_neq (16 * cap) 0)) by lia; reflexivity).
      replace (16 * (cap * 2)) with (32 * cap) by lia.
      apply sp_grow3; [lia|lia|]. apply sp_copy; [lia|apply sp_nil].
  - cbn [app]. apply sp_copy; [lia|apply sp_nil].
Qed.

Lemma push_cap_pow n cap len : d3pow cap -> n + len < 2 ^ 25 -> 1 <= len -> d3pow (push_cap n cap).
Proof.
  intros Hp Hn Hl. unfold push_cap. destruct (Z.eqb_spec n cap) as [Ec|Ec]; [|exact Hp].
  destruct (Z.eqb_spec cap 0) as [Ez|Ez].
  - right. exists 0. split; [lia|reflexivity].
  - destruct Hp as [Hp|(k & Hk & ->)]; [contradiction|]. right. exists (k + 1). split; [lia|]. apply pow_succ8. exact Hk.
Qed.

Lemma pushes_steps mxs x0 x1 x2 ls : forall n cap j v rs,
  d3pow cap -> n + zlen ls < 2 ^ 25 -> Forall (fun l => zlen l <= 6000) ls -> 2 ^ 29 <= nth 3 mxs 0 ->
  steps mxs j [x0; x1; x2; (16 * cap, v)] (fst (fst (pushes_run n cap ls j v rs)))
    [x0; x1; x2; (16 * snd (fst (pushes_run n cap ls j v rs)), fst (snd (pushes_run n cap ls j v rs)))] (rcl ls) /\
  d3pow (snd (fst (pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs Hp Hn HF HM.
  - cbn [pushes_run fst snd]. split; [apply sp_nil|exact Hp].
  - apply Forall_cons_iff in HF as [Hl HF]. cbn [pushes_run fst snd]. cbv zeta.
    assert (Hr : n + 1 + zlen r < 2 ^ 25) by (unfold zlen in *; cbn [length] in Hn; lia).
    assert (Hn1 : n < 2 ^ 25) by (unfold zlen in *; cbn [length] in Hn; lia).
    pose proof (push_tra_steps mxs x0 x1 x2 v n cap (Z.of_nat (length l)) j Hp Hn1 ltac:(unfold zlen in Hl; lia) HM) as T.
    assert (Hp' : d3pow (push_cap n cap))
      by (apply (push_cap_pow n cap (zlen (l :: r))); [exact Hp|exact Hn|unfold zlen; cbn [length]; lia]).
    destruct (IH (n + 1) (push_cap n cap) (j + nretF (list_push_tra v n cap (Z.of_nat (length l))))%nat
      (if n =? cap then Ret j else v)
      (rs ++ [Ret (Nat.pred (j + nretF (list_push_tra v n cap (Z.of_nat (length l)))))]) Hp' Hr HF HM) as [S2 P2].
    split; [|exact P2].
    change (rcl (l :: r)) with ([Z.of_nat (length l) + 1] ++ rcl r).
    eapply steps_app; [exact T|exact S2].
Qed.

Lemma grow_steps mxs x0 x2 x3 cap used j b : 0 <= cap -> 0 <= used <= 6000 -> 32768 <= nth 1 mxs 0 ->
  steps mxs j [x0; (cap, b); x2; x3] (fst (grow_tr cap used j b))
    [x0; (fst (snd (grow_tr cap used j b)), snd (snd (grow_tr cap used j b))); x2; x3] [] /\
  0 <= fst (snd (grow_tr cap used j b)).
Proof.
  intros Hc Hu HM. pose proof NMAX_v as EN. unfold grow_tr. cbv zeta.
  destruct (Z.ltb_spec (cap - used) 4096) as [E|E]; cbn [fst snd].
  - split; [|destruct (Z.eqb_spec cap 0); lia].
    apply sp_grow1; [destruct (Z.eqb_spec cap 0); lia|destruct (Z.eqb_spec cap 0); lia|apply sp_nil].
  - split; [apply sp_nil|exact Hc].
Qed.

Lemma td_steps mxs j g (w : bool) x m : 0 <= m -> steps mxs j g (if w then list_drop_tra x m else []) g [].
Proof. intros Hm. destruct w; [apply sp_free; [lia|apply sp_nil]|apply sp_nil]. Qed.

Definition d3sig (s : dstate) (a : dadr) : list (Z * adrF) :=
  [(ds_ocap s, da_out a); (ds_cap s, da_buf a); (ds_ka s, da_hp a); (16 * ds_ecap s, da_ev a)].

Definition d3str (s : dstate) : list Z :=
  match ds_pend s with [] => [] | r :: rs => skipn (Z.to_nat (ds_off s)) r ++ concat rs end.

Definition d3I (s : dstate) : Prop :=
  J1 (ds_u s) (ds_skip s) (ds_ref s) /\ 0 <= ds_cap s /\ 0 <= ds_ka s /\ 0 <= ds_ocap s /\ 0 <= ds_off s /\
  d3pow (ds_ecap s) /\ ds_en s + zlen (d3str s) < 2 ^ 25 /\ zlen (ds_H s) + zlen (d3str s) < 2 ^ 26.

Lemma skipn_skipn2 {A : Type} (m n : nat) (l : list A) : skipn n (skipn m l) = skipn (m + n) l.
Proof.
  revert l. induction m as [|m IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [destruct n; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma firstn_all3 {A : Type} (n : nat) (l : list A) : (length l <= n)%nat -> firstn n l = l.
Proof.
  revert l. induction n as [|n IH]; intros [|x l] H; cbn [length] in H; try reflexivity; [lia|].
  cbn [firstn]. rewrite IH by lia. reflexivity.
Qed.

Lemma round_str (s s2 : dstate) r0 rs n : ds_pend s = r0 :: rs -> 0 <= ds_off s -> 0 < n ->
  n <= Z.of_nat (length r0) - ds_off s ->
  ds_pend s2 = (if ds_off s + n =? Z.of_nat (length r0) then rs else r0 :: rs) ->
  ds_off s2 = (if ds_off s + n =? Z.of_nat (length r0) then 0 else ds_off s + n) ->
  d3str s = firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0) ++ d3str s2.
Proof.
  intros Ep Ho Hn Hl E1 E2. unfold d3str. rewrite Ep, E1, E2.
  destruct (Z.eqb_spec (ds_off s + n) (Z.of_nat (length r0))) as [W|W].
  - rewrite (firstn_all3 (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) by (rewrite length_skipn; lia).
    f_equal. destruct rs as [|r1 rs']; reflexivity.
  - cbv beta iota. rewrite app_assoc. f_equal.
    rewrite <- (firstn_skipn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) at 1. f_equal.
    rewrite skipn_skipn2. f_equal. rewrite Z2Nat.inj_add by lia. reflexivity.
Qed.

Lemma lines_J1 u skip st d : J1 u skip st -> Forall (fun l => zlen l <= 6000) (lines st d).
Proof.
  intros (Hk & Hw & Hl & _). apply lines_len6. intros E. rewrite <- Hw by (rewrite Hk; exact E).
  unfold zlen. apply LL_le. exact Hl.
Qed.

Lemma drain_ocap_mono lv mx : forall f s j a, 0 <= ds_ocap s -> ds_ocap s <= ds_ocap (fst (snd (drain_run f lv mx s j a))).
Proof.
  induction f as [|f IH]; intros s j a Ho; [cbn; lia|]. cbn [drain_run]. cbv zeta.
  destruct (ds_eintr s).
  - cbn [fst snd].
    match goal with |- _ <= ds_ocap (fst (snd (drain_run f lv mx ?s1 ?j1 ?a1))) => exact (IH s1 j1 a1 Ho) end.
  - destruct (ds_pend s) as [|r0 rs]; [cbn [fst snd ds_ocap]; lia|].
    match goal with |- context [if Z.min ?x ?y <=? 0 then _ else _] => destruct (Z.min x y <=? 0) end;
      [cbn [fst snd ds_ocap]; lia|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end. cbv beta iota.
    match goal with |- context [snd (fst (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11))] =>
      pose proof (lines_mono a1 a2 a7 a3 a4 a5 a6 a8 a9 a10 a11 Ho) as M;
      destruct (snd (fst (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11))) as [[oc' H'] ka'] eqn:E1 end.
    cbv beta iota. try rewrite E1 in M. cbn [fst] in M.
    match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11)] =>
      destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o' ha'] ks'] end.
    cbv beta iota. cbn [fst snd]. eapply Z.le_trans; [exact M|].
    match goal with |- _ <= ds_ocap (fst (snd (drain_run f lv mx ?s2 ?j2 ?a2))) =>
      exact (IH s2 j2 a2 ltac:(cbn [ds_ocap]; lia)) end.
Qed.

Definition gcap (cap used : Z) : Z := fst (snd (grow_tr cap used 0 adr0)).

Lemma grow_cap_c cap used j b : fst (snd (grow_tr cap used j b)) = gcap cap used.
Proof. unfold gcap, grow_tr. destruct (cap - used <? 4096); reflexivity. Qed.

Lemma pushes_cap_ind ls : forall n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs j' v' rs'; [reflexivity|]. cbn [pushes_run fst snd]. cbv zeta.
  apply IH.
Qed.

Definition pcap (n cap : Z) (ls : list (list Z)) : Z := snd (fst (pushes_run n cap ls 0 adr0 [])).

Lemma pushes_cap_c ls n cap j v rs : snd (fst (pushes_run n cap ls j v rs)) = pcap n cap ls.
Proof. unfold pcap. apply pushes_cap_ind. Qed.

Lemma drain_st lv mx : forall f s j a j' a', fst (snd (drain_run f lv mx s j a)) = fst (snd (drain_run f lv mx s j' a')).
Proof.
  induction f as [|f IH]; intros s j a j' a'; [reflexivity|]. cbn [drain_run]. cbv zeta. rewrite !grow_cap_c.
  destruct (ds_eintr s); [cbn [fst snd]; apply IH|].
  destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
  match goal with |- context [if Z.min ?x ?y <=? 0 then _ else _] => destruct (Z.min x y <=? 0) end; [reflexivity|].
  match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end. cbv beta iota.
  rewrite !pushes_cap_c, !lines_st_c.
  match goal with |- context [lrst ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] => destruct (lrst a1 a2 a3 a4 a5 a6 a7) as [[oc' H'] ka'] end.
  cbv beta iota.
  match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11)] =>
    destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o1 h1] k1] end.
  cbv beta iota.
  match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11)] =>
    destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o2 h2] k2] end.
  cbv beta iota. cbn [fst snd]. apply IH.
Qed.

Lemma drain_steps lv mx mxs : forall f s j a,
  d3I s -> 32768 <= nth 1 mxs 0 -> 2 ^ 29 <= nth 2 mxs 0 -> 2 ^ 29 <= nth 3 mxs 0 -> nth 0 mxs 0 <= NMAX ->
  ds_ocap (fst (snd (drain_run f lv mx s j a))) <= nth 0 mxs 0 ->
  exists u cs, steps mxs j (d3sig s a) (fst (drain_run f lv mx s j a))
      (d3sig (fst (snd (drain_run f lv mx s j a))) (snd (snd (drain_run f lv mx s j a)))) u /\
    d3str s = cs ++ d3str (fst (snd (drain_run f lv mx s j a))) /\ chg u (lines (ds_ref s) cs).
Proof.
  induction f as [|f IH]; intros s j a HD M1 M2 M3 MN.
  - intros _. exists [], []. cbn [drain_run fst snd]. split; [apply sp_nil|]. split; [reflexivity|].
    rewrite lines_nil. exact chg_nil.
  - pose proof HD as (HJ & Hc & Hka & Hoc & Hoff & Hp & Hen & HH).
    assert (Hu : 0 <= Z.of_nat (length (ds_u s)) <= 6000)
      by (destruct HJ as (_ & _ & L & _); pose proof (LL_le _ L); lia).
    destruct (grow_steps mxs (ds_ocap s, da_out a) (ds_ka s, da_hp a) (16 * ds_ecap s, da_ev a) (ds_cap s)
      (Z.of_nat (length (ds_u s))) j (da_buf a) Hc Hu M1) as [G1 G2].
    cbn [drain_run]. cbv zeta.
    set (g := grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)) in *.
    destruct (ds_eintr s) eqn:Ee.
    + cbn [fst snd]. intros HF.
      match type of HF with ds_ocap (fst (snd (drain_run f lv mx ?s1 ?j1 ?a1))) <= _ =>
        assert (HD1 : d3I s1) by (unfold d3I, d3str in *; cbn [ds_u ds_skip ds_ref ds_cap ds_ka ds_ocap ds_off ds_ecap
          ds_en ds_H ds_pend]; tauto);
        destruct (IH s1 j1 a1 HD1 M1 M2 M3 MN HF) as (u & cs & S1 & S2 & S3) end.
      exists u, cs. split; [|split; [exact S2|exact S3]].
      change u with ([] ++ u). eapply steps_app; [exact G1|exact S1].
    + destruct (ds_pend s) as [|r0 rs] eqn:Ep.
      * cbn [fst snd]. intros HF. exists [], []. split; [exact G1|]. split; [unfold d3str; rewrite Ep; reflexivity|].
        rewrite lines_nil. exact chg_nil.
      * set (n := Z.min (Z.of_nat (length r0) - ds_off s) (fst (snd g) - Z.of_nat (length (ds_u s)))) in *.
        destruct (Z.leb_spec n 0) as [En|En].
        -- cbn [fst snd]. intros HF. exists [], []. split; [exact G1|]. split; [unfold d3str; rewrite Ep; reflexivity|].
           rewrite lines_nil. exact chg_nil.
        -- assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
           set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) in *.
           destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:Ech. cbv beta iota.
           pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJ) as CK. rewrite Ech in CK. cbv beta iota in CK.
           destruct CK as [Erl HJ2]. subst rl.
           set (ls := lines (ds_ref s) d) in *.
           set (pu := pushes_run (ds_en s) (ds_ecap s) ls (j + nretF (fst g)) (da_ev a) (da_erecs a)) in *.
           match goal with |- context [lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls ?j3 (da_out a) (da_hp a) (da_keys a)] =>
             set (j3' := j3) in * end.
           set (sl := lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a)) in *.
           destruct (snd (fst sl)) as [[oc' H'] ka'] eqn:E1. cbv beta iota.
           destruct (snd sl) as [[o' ha'] ks'] eqn:E2. cbv beta iota.
           cbn [fst snd]. intros HF.
           match type of HF with ds_ocap (fst (snd (drain_run f lv mx ?s2 ?j4 ?a2))) <= _ =>
             set (s2' := s2) in *; set (a2' := a2) in *; set (j4' := j4) in * end.
           assert (SE : d3str s = d ++ d3str s2') by (unfold d; apply (round_str s s2' r0 rs n Ep Hoff En Hn1); reflexivity).
           assert (Ld : zlen (d3str s) = zlen d + zlen (d3str s2')) by (rewrite SE; unfold zlen; rewrite length_app; lia).
           pose proof (lines_count d (ds_ref s)) as LC. fold ls in LC.
           assert (LF : Forall (fun l => zlen l <= 6000) ls) by exact (lines_J1 _ _ _ d HJ).
           destruct (pushes_steps mxs (ds_ocap s, da_out a) (fst (snd g), snd (snd g)) (ds_ka s, da_hp a) ls
             (ds_en s) (ds_ecap s) (j + nretF (fst g)) (da_ev a) (da_erecs a) Hp ltac:(unfold zlen in *; lia) LF M3)
             as [P1 P2].
           fold pu in P1, P2.
           pose proof (lines_mono lv mx ls (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3' (da_out a) (da_hp a) (da_keys a)
             Hoc) as M.
           change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a))
             with sl in M.
           rewrite E1 in M. cbn [fst] in M.
           assert (Hfin : oc' <= nth 0 mxs 0).
           { eapply Z.le_trans; [|exact HF].
             exact (drain_ocap_mono lv mx f s2' j4' a2' ltac:(unfold s2'; cbn [ds_ocap]; lia)). }
           destruct (lines_steps lv mx mxs (fst (snd g), snd (snd g)) (16 * snd (fst pu), fst (snd pu)) ls
             (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3' (da_out a) (da_hp a) (da_keys a) Hoc Hka
             ltac:(unfold zlen in *; lia) LF M2 MN
             ltac:(change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a)
                     (da_keys a)) with sl; rewrite E1; exact Hfin))
             as (uk & L1 & B1 & Z1 & K1 & HL1).
           change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a))
             with sl in L1, B1, Z1, K1, HL1.
           rewrite E1, E2 in L1. rewrite E1 in K1, HL1. cbn [fst snd] in L1, K1, HL1.
           assert (HD2 : d3I s2').
           { unfold d3I.
             split; [exact HJ2|]. split; [exact G2|]. split; [exact K1|]. split; [change (0 <= oc'); lia|].
             split; [change (0 <= if ds_off s + n =? Z.of_nat (length r0) then 0 else ds_off s + n);
                     destruct (ds_off s + n =? Z.of_nat (length r0)); lia|].
             split; [exact P2|].
             split; [change (ds_en s + Z.of_nat (length ls) + zlen (d3str s2') < 2 ^ 25); unfold zlen in *; lia|].
             change (zlen H' + zlen (d3str s2') < 2 ^ 26). unfold zlen in *. lia. }
           destruct (IH s2' j4' a2' HD2 M1 M2 M3 MN HF) as (u2 & cs & S1 & S2 & S3).
           exists (rcl ls ++ uk ++ u2), (d ++ cs). split; [|split].
           ++ change (rcl ls ++ uk ++ u2) with ([] ++ rcl ls ++ [] ++ uk ++ u2).
              eapply steps_app; [exact G1|]. eapply steps_app; [exact P1|].
              eapply steps_app; [apply td_steps; lia|]. eapply steps_app; [exact L1|]. exact S1.
           ++ rewrite SE, S2, app_assoc. reflexivity.
           ++ rewrite lines_app. fold ls. rewrite app_assoc. apply chg_app; [|exact S3].
              split; [intros c; rewrite bcnt_app; specialize (B1 c); lia|]. rewrite zsum_app. lia.
Qed.

Lemma d3str_init NO CAP e h : d3str (drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
  unfold d3str, drain_init, pending_stream. cbn [ds_pend ds_off].
  destruct (hl_recs (hs_pending h)) as [|r0 rs]; [reflexivity|]. cbn [map].
  unfold bzs. rewrite map_app, concat_map, map_map, skipn_map'. reflexivity.
Qed.

Lemma slot3_16 c x : slot3 (16 * c) x = slot3 c x.
Proof.
  unfold slot3. destruct (Z.eqb_spec c 0) as [->|E]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq (16 * c) 0)) by lia. reflexivity.
Qed.

Lemma slot3_res n x : (length (slot3 n x) + res3 n = 1)%nat.
Proof. unfold slot3, res3. destruct (n =? 0); reflexivity. Qed.

Lemma bnd_cons p g m ms : bnd (p :: g) (m :: ms) -> 0 <= fst p <= m /\ bnd g ms.
Proof. unfold bnd. intros H. inversion H; subst. split; assumption. Qed.

Theorem drain3_holds (e : rentry) (h : hsrc) :
  0 <= re_cap e ->
  0 <= ent_ka e ->
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) ->
  0 <= hs_off h ->
  re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
  (hl_cap (hs_expected h) = 0 \/ exists k, 0 <= k /\ hl_cap (hs_expected h) = 8 * 2 ^ k) ->
  hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25 ->
  drain3 e h.
Proof.
  intros Hcap Hka HJ Hoff Hnh Hpow Hen. unfold drain3. intros lv mx NO CAP Hmx HCAP. cbv zeta.
  unfold drain_fin, drain_tr, drain_adr, drain_go.
  set (f := S (S (length (pending_stream h)))).
  set (s0 := drain_init NO CAP e h).
  assert (HL0 : zlen (d3str s0) = Z.of_nat (length (pending_stream h)))
    by (unfold s0; rewrite d3str_init; unfold zlen, bzs; rewrite length_map; reflexivity).
  assert (HD0 : d3I s0).
  { unfold d3I. rewrite HL0. unfold s0, drain_init.
    cbn [ds_u ds_skip ds_ref ds_cap ds_ka ds_ocap ds_off ds_ecap ds_en ds_H].
    split; [exact HJ|]. split; [exact Hcap|]. split; [exact Hka|]. split; [exact HCAP|]. split; [exact Hoff|].
    split; [exact Hpow|]. split; [exact Hen|].
    unfold zlen, keys_texts, re_nheld in *. rewrite length_map. exact Hnh. }
  assert (Hmono : forall j a, CAP <= ds_ocap (fst (snd (drain_run f lv mx s0 j a))))
    by (intros j a; exact (drain_ocap_mono lv mx f s0 j a HCAP)).
  split; [exact (Hmono 0%nat dadr0)|].
  intros qs b j a Ss r Hpk HN HL HB HM.
  rewrite (drain_st lv mx f s0 0 dadr0 j a) in *.
  set (sF := fst (snd (drain_run f lv mx s0 j a))) in *.
  set (aF := snd (snd (drain_run f lv mx s0 j a))) in *.
  set (td := fst (drain_run f lv mx s0 j a)) in *.
  set (mxs := [ds_ocap sF; Z.max (re_cap e) 32768; Z.max (ent_ka e) (2 ^ 29); Z.max (16 * hl_cap (hs_expected h)) (2 ^ 29)]).
  pose proof P29 as E29. pose proof P26 as E26. pose proof P25 as E25. pose proof NMAX_v as EN.
  assert (EB : BMAX = 17592186044416) by reflexivity. assert (ED : DRAIN_B = 1099511627776) by reflexivity.
  assert (Hc0 : 0 <= hl_cap (hs_expected h)).
  { destruct Hpow as [->|(k & Hk & ->)]; [lia|]. pose proof (Z.pow_nonneg 2 k ltac:(lia)). lia. }
  assert (HmF : CAP <= ds_ocap sF) by exact (Hmono j a).
  destruct (drain_steps lv mx mxs f s0 j a HD0 ltac:(unfold mxs; cbn [nth]; lia) ltac:(unfold mxs; cbn [nth]; lia)
    ltac:(unfold mxs; cbn [nth]; lia) ltac:(unfold mxs; cbn [nth]; exact HN)
    ltac:(unfold mxs, sF; cbn [nth]; apply Z.le_refl)) as (u & cs & ST & SE & SC).
  change (fst (snd (drain_run f lv mx s0 j a))) with sF in ST, SE.
  change (snd (snd (drain_run f lv mx s0 j a))) with aF in ST.
  change (fst (drain_run f lv mx s0 j a)) with td in ST.
  set (g0 := [(CAP, da_out a); (re_cap e, da_buf a); (ent_ka e, da_hp a); (16 * hl_cap (hs_expected h), da_ev a)]).
  change (d3sig s0 a) with g0 in ST.
  assert (HB0 : bnd g0 mxs).
  { unfold bnd, g0, mxs. constructor; [cbv beta; cbn [fst]; lia|]. constructor; [cbv beta; cbn [fst]; lia|].
    constructor; [cbv beta; cbn [fst]; lia|]. constructor; [cbv beta; cbn [fst]; lia|]. constructor. }
  pose proof (steps_bnd _ _ _ _ _ _ ST HB0) as HBF. unfold d3sig, mxs in HBF.
  destruct (bnd_cons _ _ _ _ HBF) as [F0 HBF1]. destruct (bnd_cons _ _ _ _ HBF1) as [F1 HBF2].
  destruct (bnd_cons _ _ _ _ HBF2) as [F2 HBF3]. destruct (bnd_cons _ _ _ _ HBF3) as [F3 _].
  cbn [fst] in F0, F1, F2, F3.
  assert (HJw : ls_k (hs_state h) = false -> zlen (ls_w (hs_state h)) <= 6000 /\ nozero (ls_w (hs_state h))).
  { destruct HJ as (Hk & Hw & Hl & Hz). intros E. rewrite <- Hw by (rewrite Hk; exact E).
    split; [unfold zlen; apply LL_le; exact Hl|exact Hz]. }
  assert (ENEW : lines (hs_state h) (bzs (pending_stream h)) =
                 lines (hs_state h) cs ++ lines (feed (hs_state h) cs) (d3str sF)).
  { rewrite <- lines_app, <- SE. unfold s0. rewrite d3str_init. reflexivity. }
  assert (LFN : Forall (fun l => zlen l <= 6000) (lines (hs_state h) (bzs (pending_stream h))))
    by (apply lines_len6; intros E; exact (proj1 (HJw E))).
  destruct (new_cred h HJw) as [CR1 CR2].
  rewrite ENEW in LFN, CR1, CR2.
  destruct (chg_new (lines (hs_state h) cs) (lines (feed (hs_state h) cs) (d3str sF)) LFN) as [CN1 CN2].
  destruct SC as [SC1 SC2].
  assert (Er : ds_ref s0 = hs_state h) by reflexivity. rewrite Er in SC1, SC2.
  assert (KB : forall c, bcnt c u + bcnt c (ekl (lines (hs_state h) (bzs (pending_stream h)))) <= cred h c).
  { intros c. rewrite ENEW. specialize (SC1 c). specialize (CN1 c). specialize (CR1 c). lia. }
  assert (KZ : zsum (fun n => n) u + zsum (fun n => n) (ekl (lines (hs_state h) (bzs (pending_stream h)))) <= credb h)
    by (rewrite ENEW; lia).
  assert (UB : zsum (fun n => n) u <= 268435456).
  { apply Forall_app in LFN as [LFc _].
    destruct (ekl_line (lines (hs_state h) cs) LFc) as (_ & _ & Q3 & _).
    pose proof (lines_mass cs (hs_state h)) as LM. unfold rcl in SC2, Q3. rewrite zsum_map in SC2, Q3.
    cbv beta in SC2, Q3.
    assert (Lcs : zlen cs <= Z.of_nat (length (pending_stream h))).
    { rewrite <- HL0, SE. unfold zlen. rewrite length_app. lia. }
    assert (Lw : (if ls_k (hs_state h) then 0 else zlen (ls_w (hs_state h))) <= 6000).
    { destruct (ls_k (hs_state h)) eqn:Ek; cbv beta iota; [lia|]. exact (proj1 (HJw eq_refl)). }
    unfold re_nheld in Hnh. lia. }
  pose proof (steps_u _ _ _ _ _ _ ST) as UN. pose proof (zsum_id_nonneg u UN) as UZ.
  destruct HM as (HN0 & HI0 & HLen).
  unfold dslots, dres in HLen. rewrite !length_app in HLen.
  pose proof (slot3_res CAP (resolveF qs (da_out a))) as R0.
  pose proof (slot3_res (re_cap e) (resolveF qs (da_buf a))) as R1.
  pose proof (slot3_res (ent_ka e) (resolveF qs (da_hp a))) as R2.
  pose proof (slot3_res (hl_cap (hs_expected h)) (resolveF qs (da_ev a))) as R3.
  destruct Hpk as (Hpl & Hcapok & Hmc).
  assert (EQ0 : bks qs g0 ++ Ss = slot3 CAP (resolveF qs (da_out a)) ++ dslots qs e h a ++ Ss).
  { unfold bks, g0, dslots. cbn [flat_map fst snd]. rewrite slot3_16, app_nil_r, <- !app_assoc. reflexivity. }
  assert (HMI : mi qs Ss g0 (p3_mis b)) by (split; [exact HN0|rewrite EQ0; exact HI0]).
  assert (HLg : (length g0 + length Ss <= NC_MAX)%nat) by (unfold g0; cbn [length]; unfold NC_MAX in *; lia).
  assert (Ebkc : forall c, bkc g0 c = ncb CAP c + ncb (re_cap e) c + ncb (ent_ka e) c + ncb (16 * hl_cap (hs_expected h)) c)
    by (intros c; unfold bkc, g0, zsum; cbn [fold_right fst]; lia).
  assert (Ebkb : bkb g0 = CAP + re_cap e + ent_ka e + 16 * hl_cap (hs_expected h))
    by (unfold bkb, g0, zsum; cbn [fold_right fst]; lia).
  assert (Ebkc' : forall c, bkc (d3sig sF aF) c = ncb (ds_ocap sF) c + ncb (ds_cap sF) c + ncb (ds_ka sF) c +
                                                  ncb (16 * ds_ecap sF) c)
    by (intros c; unfold bkc, d3sig, zsum; cbn [fold_right fst]; lia).
  assert (Ebkb' : bkb (d3sig sF aF) = ds_ocap sF + ds_cap sF + ds_ka sF + 16 * ds_ecap sF)
    by (unfold bkb, d3sig, zsum; cbn [fold_right fst]; lia).
  assert (Emx : zsum (fun m => m) mxs = ds_ocap sF + Z.max (re_cap e) 32768 + Z.max (ent_ka e) (2 ^ 29) +
                                       Z.max (16 * hl_cap (hs_expected h)) (2 ^ 29))
    by (unfold mxs, zsum; cbn [fold_right]; lia).
  assert (HLV : forall c, 0 <= c < 49 ->
            znth c (p3_live b) - bkc g0 c + Z.of_nat (length g0) + 1 + bcnt c u <= znth c (p3_cap b)).
  { intros c Hc. specialize (HL c Hc). specialize (KB c). pose proof (bcnt_nonneg c (ekl (lines (hs_state h) (bzs (pending_stream h))))).
    pose proof (bkc_b g0 c). change (Z.of_nat (length g0)) with 4. unfold DRAIN_HR in HL. lia. }
  assert (HBY : p3_bytes b - bkb g0 + zsum (fun m => m) mxs + NMAX + zsum (fun n => n) u <= BMAX)
    by (rewrite Ebkb, Emx; lia).
  destruct (steps_room mxs qs Ss j g0 td (d3sig sF aF) u ST b HB0 Hpl HLg Hcapok Hmc HMI HLV HBY) as [RM MI].
  pose proof (bnd_nonneg _ _ HB0) as HG0.
  destruct (steps_eff _ _ _ _ _ _ ST HG0) as (OK & DL & DB).
  rewrite Ebkb, Ebkb' in DB.
  split; [exact RM|].
  split; [split; [rewrite run3_len; exact Hpl|]; split; [rewrite run3_cap, run3_mcap; exact Hcapok|];
    intros c Hc; rewrite run3_mcap; exact (Hmc c Hc)|].
  split; [apply run3_cap|]. split; [apply run3_mcap|].
  split.
  - exists u. split; [exact UN|]. split; [|split; [|split]].
    + intros c Hc. rewrite (run3_live qs b j td c Hpl OK Hc). specialize (DL c). rewrite Ebkc, Ebkc' in DL.
      unfold dchain. lia.
    + rewrite run3_bytes. unfold dchainb. lia.
    + intros c _. exact (KB c).
    + exact KZ.
  - split.
    + rewrite run3_bytes. lia.
    + exists (slot3 (ds_cap sF) (resolveF qs (da_buf aF)) ++ slot3 (ds_ka sF) (resolveF qs (da_hp aF)) ++
              slot3 (16 * ds_ecap sF) (resolveF qs (da_ev aF))).
      destruct MI as [MN0 MI0]. split; [exact MN0|]. split.
      * assert (EQF : bks qs (d3sig sF aF) ++ Ss =
                      slot3 (ds_ocap sF) (resolveF qs (da_out aF)) ++
                      (slot3 (ds_cap sF) (resolveF qs (da_buf aF)) ++ slot3 (ds_ka sF) (resolveF qs (da_hp aF)) ++
                       slot3 (16 * ds_ecap sF) (resolveF qs (da_ev aF))) ++ Ss).
        { unfold bks, d3sig. cbn [flat_map fst snd]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
        rewrite <- EQF. exact MI0.
      * rewrite !length_app.
        pose proof (slot3_res (ds_ocap sF) (resolveF qs (da_out aF))).
        pose proof (slot3_res (ds_cap sF) (resolveF qs (da_buf aF))).
        pose proof (slot3_res (ds_ka sF) (resolveF qs (da_hp aF))).
        pose proof (slot3_res (16 * ds_ecap sF) (resolveF qs (da_ev aF))). unfold NC_MAX in *. lia.
Qed.

Lemma pushes_ecap ls : forall n cap, ecap_ok cap -> n + zlen ls < 2 ^ 25 -> ecap_ok (pcap n cap ls).
Proof.
  induction ls as [|l r IH]; intros n cap Hc Hn; [exact Hc|]. unfold pcap. cbn [pushes_run fst snd]. cbv zeta.
  rewrite pushes_cap_c. apply IH; [|unfold zlen in *; cbn [length] in Hn; lia].
  unfold push_cap. destruct (Z.eqb_spec n cap) as [E|E]; [|exact Hc].
  destruct (Z.eqb_spec cap 0) as [E0|E0].
  - right. exists 0. split; [lia|reflexivity].
  - destruct Hc as [Hc|(k & Hk & Ek)]; [contradiction|]. subst cap.
    destruct (pow8_grow k ltac:(lia) ltac:(unfold zlen in *; cbn [length] in Hn; lia)) as [_ K].
    right. exists (k + 1). split; [lia|]. apply pow_succ8. lia.
Qed.

Definition d3E (s : dstate) : Prop := ecap_ok (ds_ecap s) /\ ds_en s + zlen (d3str s) < 2 ^ 25 /\ 0 <= ds_off s.

Lemma d3E_same s s' : ds_ecap s' = ds_ecap s -> ds_en s' = ds_en s -> d3str s' = d3str s -> ds_off s' = ds_off s ->
  d3E s -> d3E s'.
Proof. intros E1 E2 E3 E4 (H1 & H2 & H3). unfold d3E. rewrite E1, E2, E3, E4. tauto. Qed.

Lemma drain_ecap_run lv mx : forall f s j a, d3E s -> d3E (fst (snd (drain_run f lv mx s j a))).
Proof.
  induction f as [|f IH]; intros s j a HE; [exact HE|]. pose proof HE as (He & Hn & Ho). cbn [drain_run]. cbv zeta.
  set (g := grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)).
  destruct (ds_eintr s).
  - cbn [fst snd]. apply IH. apply (d3E_same s); [reflexivity|reflexivity|reflexivity|reflexivity|exact HE].
  - destruct (ds_pend s) as [|r0 rs] eqn:Ep.
    + cbn [fst snd]. apply (d3E_same s); [reflexivity|reflexivity| |reflexivity|exact HE].
      unfold d3str. rewrite Ep. reflexivity.
    + set (n := Z.min (Z.of_nat (length r0) - ds_off s) (fst (snd g) - Z.of_nat (length (ds_u s)))).
      destruct (Z.leb_spec n 0) as [En|En].
      * cbn [fst snd]. apply (d3E_same s); [reflexivity|reflexivity| |reflexivity|exact HE].
        unfold d3str. rewrite Ep. reflexivity.
      * assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
        set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)).
        destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl]. cbv beta iota.
        match goal with |- context [snd (fst (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11))] =>
          destruct (snd (fst (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11))) as [[oc' H'] ka'] end.
        cbv beta iota.
        match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11)] =>
          destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o' ha'] ks'] end.
        cbv beta iota. cbn [fst snd]. apply IH.
        match goal with |- d3E ?s2 => set (s2' := s2) end.
        assert (SE : d3str s = d ++ d3str s2') by (unfold d; apply (round_str s s2' r0 rs n Ep Ho En Hn1); reflexivity).
        pose proof (lines_count d (ds_ref s)) as LC.
        assert (Ld : zlen (d3str s) = zlen d + zlen (d3str s2')) by (rewrite SE; unfold zlen; rewrite length_app; lia).
        unfold d3E. split; [|split].
        -- unfold s2'. cbn [ds_ecap]. rewrite pushes_cap_c. apply pushes_ecap; [exact He|]. unfold zlen in *. lia.
        -- assert (E : ds_en s2' = ds_en s + Z.of_nat (length (lines (ds_ref s) d))) by reflexivity.
           rewrite E. unfold zlen in *. lia.
        -- assert (E : ds_off s2' = if ds_off s + n =? Z.of_nat (length r0) then 0 else ds_off s + n) by reflexivity.
           rewrite E. destruct (ds_off s + n =? Z.of_nat (length r0)); lia.
Qed.

Theorem drain3_ecap (e : rentry) (h : hsrc) :
  0 <= hs_off h ->
  ecap_ok (hl_cap (hs_expected h)) ->
  hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25 ->
  forall (lv : bool) (mx NO CAP : Z), ecap_ok (ds_ecap (drain_fin lv mx NO CAP e h)).
Proof.
  intros Hoff He Hn lv mx NO CAP. unfold drain_fin, drain_go.
  assert (H0 : d3E (drain_init NO CAP e h)).
  { unfold d3E. rewrite d3str_init. unfold drain_init. cbn [ds_ecap ds_en ds_off]. split; [exact He|].
    split; [|exact Hoff]. unfold zlen, bzs, hl_n in *. rewrite length_map. exact Hn. }
  exact (proj1 (drain_ecap_run lv mx _ _ 0%nat dadr0 H0)).
Qed.
