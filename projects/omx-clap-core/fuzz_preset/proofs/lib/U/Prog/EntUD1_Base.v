From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import pj_get_c.
Import ListNotations.
Open Scope Z_scope.

Lemma ud1_cb : forall m k s, mem_inv rsegs m -> 0 <= k -> k + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  ro_bytes_b rsegs k (map (Z_to_bv 8) (s ++ [0])) = true -> pj_cbytes rsegs m k s.
Proof.
  intros m k s MI H0 H1 HF HB. split.
  - apply Forall_forall. intros c Hc. rewrite forallb_forall in HF. specialize (HF c Hc).
    apply andb_prop in HF as [A B]. apply Z.ltb_lt in A. apply Z.ltb_lt in B. lia.
  - apply ro_bytes_at; [exact MI | exact H0 | rewrite length_map, length_app; cbn [length]; lia |].
    apply ro_bytes_b_sound. exact HB.
Qed.

Lemma ud1_apart : forall a n lo hi, 0 < n -> lo < hi -> (forall x, a <= x < a + n -> ~ (lo <= x < hi)) ->
  a + n <= lo \/ hi <= a.
Proof.
  intros a n lo hi Hn Hl H. destruct (Z_le_dec (a + n) lo) as [E|E]; [left; exact E|].
  destruct (Z_le_dec hi a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max a lo)); lia.
Qed.

Lemma ud1_hit_foot : forall m L o members D i kname v kids x,
  pj_node rsegs m L o (JObj members) D -> nth_error members i = Some (kname, v) -> pj_u64 rsegs m (o + 24) kids ->
  kids + 56 * Z.of_nat i <= x < kids + 56 * Z.of_nat i + 56 -> pj_foot o D x.
Proof.
  intros m L o members D i kname v kids x HN Ei Hk Hx.
  assert (Es : nth_error (slots (JObj members)) i = Some (Some kname, v))
    by (cbn [slots]; rewrite nth_error_map, Ei; reflexivity).
  destruct (pj_slot rsegs m L o (JObj members) D i (Some kname) v HN Es)
    as (num & str & kids' & keys & n & cap & D1 & Hh & _ & _ & _ & HF1 & _).
  pose proof Hh as (_ & _ & _ & _ & Hk' & _).
  rewrite (pj_u64_uniq rsegs m (o + 24) kids' kids Hk' Hk) in HF1.
  apply HF1. left. exact Hx.
Qed.

Lemma ud1_get_sub : forall m L o t D kname z, pj_node rsegs m L o t D -> pj_get_res m L o t D kname z ->
  z = 0 \/ exists v Dz, pj_node rsegs m L z v Dz /\ (forall x, pj_foot z Dz x -> pj_foot o D x).
Proof.
  intros m L o t D kname z HN HR.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_get_res] in HR; try (left; exact HR).
  destruct HR as [(_ & Hz)|(i & v & kids & Di & Ei & _ & Hk & Ez & Hv & Hinc)]; [left; exact Hz|]. right.
  exists v, Di. split; [subst z; exact Hv|].
  intros x [Hx|(b & Hb & Hx)].
  - subst z. exact (ud1_hit_foot m L o members D i kname v kids x HN Ei Hk Hx).
  - right. exists b. split; [apply Hinc; exact Hb | exact Hx].
Qed.

Lemma ud1_node_tr : forall W m m' L p u Du, pj_node rsegs m L p u Du -> munch W m m' ->
  (forall x, pj_foot p Du x -> outside W x) -> pj_node rsegs m' L p u Du.
Proof.
  intros W m m' L p u Du H MU HO.
  exact (pj_node_munch rsegs W m L m' L p u Du H (pj_node_blocks rsegs u m L p Du H) MU HO).
Qed.

Lemma ud1_res_tr : forall W m m' L o t D kname z, pj_node rsegs m L o t D -> pj_get_res m L o t D kname z ->
  munch W m m' -> (forall x, pj_foot o D x -> outside W x) -> pj_get_res m' L o t D kname z.
Proof.
  intros W m m' L o t D kname z HN HR MU HO.
  destruct t as [| | | txt bits | s | items | members]; cbn [pj_get_res] in HR |- *; try exact HR.
  destruct HR as [HR|(i & v & kids & Di & Ei & Hf & Hk & Ez & Hv & Hinc)]; [left; exact HR|right].
  exists i, v, kids, Di. split; [exact Ei|]. split; [exact Hf|].
  split; [apply (pj_u64_eq rsegs m m'); [exact Hk | intros x Hx; apply MU; apply HO; left; lia]|].
  split; [exact Ez|]. split; [|exact Hinc].
  apply (ud1_node_tr W m m' L z v Di Hv MU).
  intros x [Hx|(b & Hb & Hx)]; apply HO.
  - subst z. exact (ud1_hit_foot m L o members D i kname v kids x HN Ei Hk Hx).
  - right. exists b. split; [apply Hinc; exact Hb | exact Hx].
Qed.

Definition ud1_inv (m0 m : word -> option byte) (S lo : Z) : Prop :=
  munch [(S - 96, S); (S + 64, S + 72)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\
  stk rsegs m lo S /\ lo <= S - 96 /\ stk rsegs m (S + 64) (S + 72).

Definition ud1_blk (lblk : Z -> Z -> Prop) (S : Z) : Prop :=
  forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 96) 168.

Definition ud1_key (k : Z) (K : list Z) : Prop :=
  0 <= k /\ k + Z.of_nat (length K) + 1 <= 2 ^ 64 /\
  forallb (fun c => (0 <? c) && (c <? 256)) K = true /\
  ro_bytes_b rsegs k (map (Z_to_bv 8) (K ++ [0])) = true.

Ltac ud1_keyok :=
  unfold ud1_key; refine (conj _ (conj _ (conj _ _)));
  first [apply Z.leb_le; vm_compute; reflexivity | vm_compute; reflexivity].

Ltac ud1_lit := first [reflexivity | apply bv_eq; vm_compute; reflexivity].

Lemma ud1_inv_mk : forall m0 m S lo,
  munch [(S - 96, S); (S + 64, S + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo S -> lo <= S - 96 -> stk rsegs m (S + 64) (S + 72) -> ud1_inv m0 m S lo.
Proof. intros m0 m S lo H1 H2 H3 H4 H5 H6. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))). Qed.

Lemma ud1_inv_refl : forall m S lo, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 96 ->
  stk rsegs m (S + 64) (S + 72) -> ud1_inv m m S lo.
Proof. intros m S lo H3 H4 H5 H6. exact (ud1_inv_mk m m S lo (munch_refl _ m) (wmono_refl rsegs m) H3 H4 H5 H6). Qed.

Lemma ud1_munch_sym : forall W m m', munch W m m' -> munch W m' m.
Proof. intros W m m' H x Hx. symmetry. exact (H x Hx). Qed.

Lemma ud1_munch_call : forall S w m0 m m', 0 <= w <= 96 ->
  munch [(S - 96, S); (S + 64, S + 72)] m0 m -> munch [(S - w, S)] m m' ->
  munch [(S - 96, S); (S + 64, S + 72)] m0 m'.
Proof.
  intros S w m0 m m' Hw H1 H2. apply (munch_trans _ m0 m m' H1).
  apply (munch_weaken [(S - w, S)]); [|exact H2].
  intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (A & _ & _).
  split; [intros [C1 C2]; apply A; split; lia | exact I].
Qed.

Lemma ud1_slot : forall m S, stk rsegs m (S + 64) (S + 72) -> exists j, rw_cells rsegs m (S + 64) [CB 8 j].
Proof.
  intros m S H. destruct (stk_carve rsegs m (S + 64) (S + 72) 8 H ltac:(lia)) as (_ & j & HJ).
  change (Z.of_nat 8) with 8 in HJ. exists j. replace (S + 64) with (S + 72 - 8) by lia. exact HJ.
Qed.

Lemma ud1_slot_back : forall m S v, rw_cells rsegs m (S + 64) [C8 v] -> stk rsegs m (S + 64) (S + 72).
Proof.
  intros m S v H. pose proof (stk_of_rw_cells rsegs m (S + 64) [C8 v] H) as H'.
  change (Z.of_nat (cells_size [C8 v])) with 8 in H'. replace (S + 72) with (S + 64 + 8) by lia. exact H'.
Qed.

Lemma ud1_root_out : forall m lblk S t D, ud1_blk lblk S -> pj_node rsegs m lblk (S + 8) t D ->
  forall x, pj_foot (S + 8) D x -> outside [(S - 96, S); (S + 64, S + 72)] x.
Proof.
  intros m lblk S t D HB HN x [Hx|((a & n) & Hin & Hx)]; cbn [outside].
  - split; [intros [C1 C2]; lia|]. split; [intros [C1 C2]; lia | exact I].
  - pose proof (pj_node_blocks rsegs t m lblk (S + 8) D HN a n Hin) as HL.
    destruct (HB a n HL) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd.
    unfold pj_holds in Hx. cbn [fst snd] in Hx.
    split; [intros [C1 C2]; lia|]. split; [intros [C1 C2]; lia | exact I].
Qed.

Lemma ud1_sub : forall m0 lblk S t D K z, ud1_blk lblk S -> pj_node rsegs m0 lblk (S + 8) t D ->
  pj_get_res m0 lblk (S + 8) t D K z ->
  z = 0 \/ exists v Dv, pj_node rsegs m0 lblk z v Dv /\
    (forall x, pj_foot z Dv x -> outside [(S - 96, S); (S + 64, S + 72)] x).
Proof.
  intros m0 lblk S t D K z HB HN HR.
  destruct (ud1_get_sub m0 lblk (S + 8) t D K z HN HR) as [Hz|(v & Dz & Hv & Hf)]; [left; exact Hz|right].
  exists v, Dz. split; [exact Hv|]. intros x Hx. exact (ud1_root_out m0 lblk S t D HB HN x (Hf x Hx)).
Qed.

Lemma ud1_ro_out : forall m lo hi k bs, mem_inv rsegs m -> stk rsegs m lo hi -> ro_bytes rsegs k bs ->
  forall x, k <= x < k + Z.of_nat (length bs) -> ~ (lo <= x < hi).
Proof.
  intros m lo hi k bs MI (_ & _ & HS) HR x Hx Hin.
  destruct (nth_error bs (Z.to_nat (x - k))) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  pose proof (ro_bytes_nth rsegs bs k _ b HR E) as (_ & Hro).
  replace (k + Z.of_nat (Z.to_nat (x - k))) with x in Hro by lia.
  destruct (HS x Hin) as (Hw & _).
  destruct (m (wa x)) as [b'|] eqn:Em.
  - pose proof (MI _ _ Em). congruence.
  - pose proof (wview_not_ro rsegs m (wa x) Hw Em). congruence.
Qed.

Lemma ud1_key_apart : forall m lo S w k K, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - w -> 0 < w -> ud1_key k K ->
  k + Z.of_nat (length K) + 1 <= S - w \/ S <= k.
Proof.
  intros m lo S w k K MI ST HL Hw (H0 & H1 & HF & HB).
  pose proof (ro_bytes_b_sound rsegs _ _ HB) as HR.
  assert (HA : forall x, k <= x < k + (Z.of_nat (length K) + 1) -> ~ (S - w <= x < S)).
  { intros x Hx Hin. apply (ud1_ro_out m lo S k (map (Z_to_bv 8) (K ++ [0])) MI ST HR x);
      [rewrite length_map, length_app; cbn [length]; lia | lia]. }
  destruct (ud1_apart k (Z.of_nat (length K) + 1) (S - w) S ltac:(lia) ltac:(lia) HA) as [E|E]; [left|right]; lia.
Qed.

Lemma ud1_key_cb : forall m k K, mem_inv rsegs m -> ud1_key k K -> pj_cbytes rsegs m k K.
Proof. intros m k K MI (H0 & H1 & HF & HB). exact (ud1_cb m k K MI H0 H1 HF HB). Qed.
