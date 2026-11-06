(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the representation lemma the fd >= 0 arm of plugin-hostd's relay_add ends
   with - the new entry is appended to the relay's table (lane W5). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_journal W_sites.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section ra.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable RG : rep_globals.

(* ---------------------------------------------------------------------------------------------------------------
   small list facts
   --------------------------------------------------------------------------------------------------------------- *)

Lemma rar_bzs_app : forall l1 l2 : list byte, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. apply map_app. Qed.

Lemma rar_length_bzs : forall l : list byte, length (bzs l) = length l.
Proof. intros l. apply length_map. Qed.

Lemma rar_NoDup_snoc : forall (A : Type) (l : list A) (x : A), NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros A l x. rewrite !NoDup_ListNoDup. induction l as [|a l IH]; intros H Hn; cbn [app].
  - apply List.NoDup_cons; [exact Hn | exact H].
  - apply List.NoDup_cons_iff in H. destruct H as (Ha & Hl). apply List.NoDup_cons.
    + intros Hi. apply in_app_iff in Hi. destruct Hi as [Hi | [He | []]].
      * exact (Ha Hi).
      * apply Hn. left. exact (eq_sym He).
    + apply IH; [exact Hl | intros Hi; apply Hn; right; exact Hi].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   a byte the ASan reader sees is a byte of a val_mem, and a region it sees everywhere is a byte list
   --------------------------------------------------------------------------------------------------------------- *)

Lemma rar_vm1_of_aview : forall (Wx : world SEGS) (mx : word -> option byte) a v,
  aview SEGS (w_H Wx) mx a = Some v -> val_mem SEGS (arm Wx mx) a 1 v /\ 0 <= v < 256.
Proof.
  intros Wx mx a v E. destruct (aview_byte SEGS (w_H Wx) mx a v E) as (b & Hb & Hv & Hr).
  split; [|exact Hr]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold arm. rewrite Hb. f_equal. unfold YO0f.le_byte.
  replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 256) by lia. rewrite Z.mod_small by lia.
  rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rar_bytes_of_view : forall (Wx : world SEGS) (mx : word -> option byte) base n,
  (forall x, base <= x < base + Z.of_nat n -> aview SEGS (w_H Wx) mx x <> None) ->
  exists l : list byte, length l = n /\ garr8 SEGS (arm Wx mx) base (bzs l).
Proof.
  intros Wx mx base n. revert base. induction n as [|n IH]; intros base Hp.
  - exists []. split; [reflexivity | apply garr8_nil].
  - destruct (aview SEGS (w_H Wx) mx base) as [v|] eqn:E;
      [|exfalso; exact (Hp base ltac:(lia) E)].
    destruct (rar_vm1_of_aview Wx mx base v E) as (HV & HR).
    destruct (aview_byte SEGS (w_H Wx) mx base v E) as (b & _ & Hbv & _).
    destruct (IH (base + 1)) as (l & Hl & Hg); [intros x Hx; apply Hp; lia|].
    exists (b :: l). split; [cbn [length]; lia|].
    change (bzs (b :: l)) with (bz b :: bzs l).
    intros [|j] Hj.
    + cbn [nth Z.of_nat]. rewrite Z.add_0_r. unfold bz. rewrite <- Hbv.
      split; [exact HV | exact HR].
    + cbn [nth length] in Hj |- *.
      replace (base + Z.of_nat (S j)) with (base + 1 + Z.of_nat j) by lia.
      exact (Hg j ltac:(lia)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   the blocks an entry names are live
   --------------------------------------------------------------------------------------------------------------- *)

Lemma rar_in_if_nil : forall (X : Type) (c : bool) (p b : X), In b (if c then [] else [p]) -> c = false /\ b = p.
Proof. intros X c p b H. destruct c; cbn [In] in H; [destruct H | destruct H as [<- | []]; split; reflexivity]. Qed.

Lemma rar_aentry_blks_live : forall ly S (Wx : world SEGS) (mx : word -> option byte) e,
  aentry_ok B ly S Wx mx e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S Wx mx e He b Hb.
  destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15).
  unfold aentry_blks in Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply rar_in_if_nil in Hb. destruct Hb as (Ec & ->). apply Z.eqb_neq in Ec.
    destruct H10 as [(Hc & _) | (_ & Hin & _)]; [lia | exact Hin].
  - apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
    + apply rar_in_if_nil in Hb. destruct Hb as (Ez & ->). apply Z.eqb_neq in Ez.
      destruct H12 as [(Hz & _) | (_ & Hin & _)]; [lia | exact Hin].
    + apply in_map_iff in Hb. destruct Hb as (k & <- & Hk).
      rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   the entry relay_add appends is well formed on its own: cap 0, buf 0, no held keys
   --------------------------------------------------------------------------------------------------------------- *)

Lemma rar_aentry_ok_new : forall fd, 0 <= fd < 2 ^ 31 ->
  forall ly S (Wx : world SEGS) (mx : word -> option byte), aentry_ok B ly S Wx mx (ra_new fd).
Proof.
  intros fd Hfd ly S Wx mx. unfold aentry_ok, ra_new.
  cbn [re_eof re_skip re_pad1 re_pad2 re_fd re_cap re_used re_U re_buf re_junk re_hp re_kh re_keys].
  unfold re_nheld. cbn [re_keys length].
  split; [left; reflexivity|].
  split; [left; reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hfd|].
  split; [left; reflexivity|].
  split; [reflexivity|].
  split; [unfold APARTIAL; lia|].
  split; [intros []|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [cbn [Z.of_nat]; lia|].
  split; [left; split; reflexivity|].
  split; [cbn [map]; constructor|].
  split; [cbn [map]; constructor|].
  constructor.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   the byte image of that entry: the 4 little-endian bytes of fd, then 52 zero bytes
   --------------------------------------------------------------------------------------------------------------- *)

Lemma ra_new_entry_garr8 : forall (Wx : world SEGS) (mx : word -> option byte) d fd,
  0 <= fd < 2 ^ 31 ->
  val_mem SEGS (arm Wx mx) d 4 fd ->
  (forall i, 0 <= i < 52 -> aview SEGS (w_H Wx) mx (d + 4 + i) = Some 0) ->
  garr8 SEGS (arm Wx mx) d (bzs (entry_bytes (ra_new fd))).
Proof.
  intros Wx mx d fd Hfd Hvm Hz.
  (* the n-th byte of a little-endian image is the n-th byte of the value *)
  assert (Hnth : forall n z j, (j < n)%nat -> nth j (bzs (Z_to_le_bytes n z)) 0 = Z.shiftr z (8 * Z.of_nat j) mod 256).
  { induction n as [|n IH]; intros z j Hj; [lia|].
    destruct j as [|j]; cbn [Z_to_le_bytes bzs map nth].
    - unfold bz. rewrite Z_to_bv_unsigned. change (bv_wrap 8 z) with (z mod 256).
      change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
    - change (nth j (map bz (Z_to_le_bytes n (Z.shiftr z 8))) 0) with (nth j (bzs (Z_to_le_bytes n (Z.shiftr z 8))) 0).
      rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia. }
  unfold entry_bytes, ra_new, Mem.le4.
  cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2].
  rewrite rar_bzs_app. apply garr8_app. split.
  - (* the 4 bytes of fd *)
    intros j Hj. change (length (bzs (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 fd))))) with 4%nat in Hj.
    rewrite (Hnth 4%nat _ j Hj). rewrite Z_to_bv_unsigned.
    rewrite (bv_wrap_small 64 fd) by (unfold bv_modulus; lia).
    assert (Hr : 0 <= Z.shiftr fd (8 * Z.of_nat j) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    split; [|exact Hr].
    intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite (Hvm j Hj). f_equal. f_equal. unfold YO0f.le_byte.
    change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
    rewrite Z.shiftr_0_r. rewrite (Z.mod_small fd (2 ^ 32)) by lia.
    rewrite (Z.mod_small (Z.shiftr fd (8 * Z.of_nat j) mod 256) 256) by exact Hr.
    symmetry. apply Z.mod_mod. lia.
  - (* the 52 zero bytes after it *)
    change (length (bzs (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 fd))))) with 4%nat.
    match goal with |- garr8 _ _ _ ?l => replace l with (repeat 0 52) by (vm_compute; reflexivity) end.
    intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat.
    apply rar_vm1_of_aview. replace (d + Z.of_nat 4 + Z.of_nat j) with (d + 4 + Z.of_nat j) by lia.
    apply Hz. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   the walk's last representation step: the table at T' holds es ++ [ra_new fd]
   --------------------------------------------------------------------------------------------------------------- *)

Lemma arelay_append : forall ly S (W : world SEGS) mem ly' S' (W' : world SEGS) mem' T T' es fd,
  ra_rel B RG ly S W mem T es ->
  (length es < 4)%nat -> ~ In fd (map re_fd es) -> 0 <= fd < 2 ^ 31 ->
  In (T', ATABLE) (ablocks B ly' S') -> (es <> [] -> T' = T) ->
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly' S')) ->
  val_mem SEGS (arm W' mem') (rg_src RG) 8 T' -> awr W' mem' (rg_src RG) 8 ->
  val_mem SEGS (arm W' mem') (rg_nsrc RG) 4 (Z.of_nat (length es) + 1) -> awr W' mem' (rg_nsrc RG) 4 ->
  val_mem SEGS (arm W' mem') (rg_capsrc RG) 4 16 -> awr W' mem' (rg_capsrc RG) 4 ->
  garr8 SEGS (arm W' mem') (T' + AENT * Z.of_nat (length es)) (bzs (entry_bytes (ra_new fd))) ->
  (forall x, T <= x < T + AENT * Z.of_nat (length es) -> abyte_kept W mem W' mem' x) ->
  (forall x, T' + AENT * (Z.of_nat (length es) + 1) <= x < T' + ATABLE -> aview SEGS (w_H W') mem' x <> None) ->
  akept W mem W' mem' (concat (map aentry_fp es)) ->
  arelay_at B RG ly' S' W' mem' T' (es ++ [ra_new fd]).
Proof.
  intros ly S W mem ly' S' W' mem' T T' es fd Hrel Hlt4 Hfd Hfdr Hin HT' Hmono
    Hsrc Hwsrc Hnsrc Hwn Hcap Hwc Hnew Hold Hview Hkept.
  assert (Hlen : Z.of_nat (length (es ++ [ra_new fd])) = Z.of_nat (length es) + 1)
    by (rewrite length_app; cbn [length]; lia).
  assert (HNB : length (entry_bytes (ra_new fd)) = 56%nat) by reflexivity.
  (* what survives of the old table: its bytes, its entries, its file descriptors, and that no entry's block is the
     table (arelay_at's last conjunct, W8's) *)
  assert (HOLD : Z.of_nat (length (concat (map entry_bytes es))) = AENT * Z.of_nat (length es)
              /\ garr8 SEGS (arm W' mem') T' (bzs (concat (map entry_bytes es)))
              /\ Forall (aentry_ok B ly' S' W' mem') es
              /\ NoDup (map re_fd es)
              /\ Forall (fun e => forall b, In b (aentry_blks e) -> b <> (T', ATABLE)) es).
  { destruct es as [|e0 es1].
    - cbn [concat map length]. split; [unfold AENT; lia|].
      split; [apply garr8_nil|]. split; [constructor|]. split; constructor.
    - assert (HTT : T' = T) by (apply HT'; discriminate).
      destruct Hrel as [(_ & Hnil & _) | HAT]; [discriminate|].
      destruct HAT as (_ & _ & _ & _ & _ & _ & _ & _ & (tail0 & Ht1 & Ht2 & Ht3) & HFa & HND & HFR).
      rewrite length_app in Ht2. rewrite Nat2Z.inj_add in Ht2.
      assert (HLc : Z.of_nat (length (concat (map entry_bytes (e0 :: es1))))
                  = AENT * Z.of_nat (length (e0 :: es1))) by lia.
      split; [exact HLc|].
      split.
      { rewrite HTT. rewrite rar_bzs_app in Ht3.
        apply (akept_garr8 W mem); [|exact (proj1 (proj1 (garr8_app _ _ _ _ _) Ht3))].
        intros x Hx. rewrite rar_length_bzs in Hx. apply Hold. lia. }
      split; [|split; [exact HND | rewrite HTT; exact HFR]].
      rewrite Forall_forall in HFa |- *. intros e He.
      apply (aentry_ok_kept B ly S W mem); [exact (HFa e He) | |].
      + eapply akept_sub; [exact Hkept|]. intros r Hr. apply in_concat.
        exists (aentry_fp e). split; [apply (in_map aentry_fp); exact He | exact Hr].
      + intros b Hb. apply Hmono. exact (rar_aentry_blks_live ly S W mem e (HFa e He) b Hb). }
  destruct HOLD as (HLc & HGc & HFo & HNDo & HFRo).
  (* the bytes of the table after the new entry: whatever the reader sees there *)
  destruct (rar_bytes_of_view W' mem' (T' + AENT * (Z.of_nat (length es) + 1))
              (Z.to_nat (ATABLE - AENT * (Z.of_nat (length es) + 1)))) as (tl & Htl & Hgtl).
  { intros x Hx. rewrite Z2Nat.id in Hx by (unfold AENT, ATABLE; lia). apply Hview. lia. }
  assert (HLt : Z.of_nat (length tl) = ATABLE - AENT * (Z.of_nat (length es) + 1)).
  { rewrite Htl. apply Z2Nat.id. unfold AENT, ATABLE. lia. }
  assert (Hcat : concat (map entry_bytes (es ++ [ra_new fd]))
               = concat (map entry_bytes es) ++ entry_bytes (ra_new fd)).
  { rewrite map_app, concat_app. cbn [concat map]. rewrite app_nil_r. reflexivity. }
  unfold arelay_at.
  split; [exact Hsrc|].
  split; [exact Hwsrc|].
  split; [rewrite Hlen; exact Hnsrc|].
  split; [exact Hwn|].
  split; [exact Hcap|].
  split; [exact Hwc|].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [exact Hin|].
  split.
  { exists tl. unfold atable_at. rewrite Hcat, Hlen.
    split; [exact HLt|].
    split.
    { rewrite !length_app, !Nat2Z.inj_add, HLc, HNB, HLt. unfold AENT, ATABLE. lia. }
    rewrite !rar_bzs_app.
    apply (proj2 (garr8_app _ _ _ _ _)). split.
    - apply (proj2 (garr8_app _ _ _ _ _)). split; [exact HGc|].
      rewrite rar_length_bzs, HLc. exact Hnew.
    - rewrite length_app, !rar_length_bzs, Nat2Z.inj_add, HLc, HNB.
      replace (T' + (AENT * Z.of_nat (length es) + Z.of_nat 56))
        with (T' + AENT * (Z.of_nat (length es) + 1)) by (unfold AENT; lia).
      exact Hgtl. }
  split.
  { apply Forall_forall. intros e He. apply in_app_iff in He. destruct He as [He | [<- | []]].
    - rewrite Forall_forall in HFo. exact (HFo e He).
    - apply rar_aentry_ok_new. exact Hfdr. }
  split.
  { rewrite map_app. cbn [map re_fd ra_new].
    apply rar_NoDup_snoc; [exact HNDo | exact Hfd]. }
  (* the new entry has no blocks *)
  apply Forall_app. split; [exact HFRo|].
  apply Forall_cons; [|apply Forall_nil]. intros b Hb. simpl in Hb. destruct Hb.
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   an old entry's footprint lies in a live block that is not the table, so off the table (relay_add's akept premise)
   --------------------------------------------------------------------------------------------------------------- *)

Hypothesis LAWS : AR_laws SEGS B.

(* key_ptrs (Prog/gestures_end_b_c.v) is loaded through W_rep but not imported here: its full name *)
Lemma rar_key_ptrs_len : forall ks,
  length (OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.gestures_end_b_c.key_ptrs in *.
  cbn [map concat length].
  rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.

(* two live blocks that are not the same are disjoint (the image-B twin's ra_sep_disj, lib/B/W_relay_add_sep.v) *)
Lemma rar_sep_disj : forall ly S (W : world SEGS) mem md p n q m,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) -> (p, n) <> (q, m) ->
  p + req_size n <= q \/ q + req_size m <= p.
Proof.
  intros ly S W mem md p n q m HAR H1 H2 Hne.
  apply in_split in H1 as (a1 & a2 & E1).
  assert (H2' : In (q, m) (a1 ++ a2)).
  { rewrite E1 in H2. apply in_app_or in H2 as [H2 | [H2 | H2]];
    [apply in_or_app; left; exact H2 | exfalso; exact (Hne H2) | apply in_or_app; right; exact H2]. }
  apply in_split in H2' as (b1 & b2 & E2).
  assert (T1 : Permutation ((p, n) :: (q, m) :: b1 ++ b2) ((p, n) :: (a1 ++ a2)))
    by (apply perm_skip; rewrite E2; apply Permutation_middle).
  assert (T2 : Permutation ((p, n) :: (a1 ++ a2)) (a1 ++ (p, n) :: a2)) by apply Permutation_middle.
  assert (HP : Permutation (ablocks B ly S) ((p, n) :: (q, m) :: b1 ++ b2))
    by (rewrite E1; apply Permutation_sym; exact (perm_trans T1 T2)).
  pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (p, n) (q, m) (b1 ++ b2) HAR HP) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* every byte an old entry reads is in one of its blocks (a buffer, a held array, a key text); arelay_at's last
   conjunct makes that block a live block other than the table, so AR's pairwise separation puts it off the table *)
Lemma rar_efp_off_table : forall ly S (W : world SEGS) mem md T es,
  AR SEGS B ly S W mem md -> arelay_at B RG ly S W mem T es ->
  forall e r a, In e es -> In r (aentry_fp e) -> fst r <= a < snd r ->
  exists p n, In (p, n) (ablocks B ly S) /\ 0 <= a - p < req_size n /\ ~ (T <= a < T + req_size ATABLE).
Proof.
  intros ly S W mem md T es HAR HR e r a He Hr Ha.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HinT & _ & HF & _ & HFR).
  rewrite Forall_forall in HF, HFR.
  pose proof (HF e He) as HE. pose proof (HFR e He) as HB.
  (* a block of e holding a: live, not the table, so disjoint from it *)
  assert (Hblk : forall p n, In (p, n) (aentry_blks e) -> 0 < n -> p <= a < p + n ->
    exists p n, In (p, n) (ablocks B ly S) /\ 0 <= a - p < req_size n /\ ~ (T <= a < T + req_size ATABLE)).
  { intros p n Hb Hn Hpa. exists p, n.
    pose proof (rar_aentry_blks_live ly S W mem e HE (p, n) Hb) as Hin.
    assert (Rn : req_size n = n) by (clear - Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
    split; [exact Hin|]. split; [rewrite Rn; clear - Hpa; lia|].
    destruct (rar_sep_disj ly S W mem md p n T ATABLE HAR Hin HinT (HB (p, n) Hb)) as [D|D];
      clear - D Rn Hpa; lia. }
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - (* the buffer *)
    destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
    destruct HE as (_ & _ & _ & _ & _ & _ & H7 & _ & _ & H10 & _).
    destruct H10 as [(Hc0 & _) | (Hcp & _ & Hj & _)]; [exfalso; exact (Hc Hc0)|].
    unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd] in Ha.
    apply (Hblk (re_buf e) (re_cap e)).
    + unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + exact Hcp.
    + clear - Ha H7 Hj. lia.
  - destruct Hr as [<- | Hr].
    + (* the held array *)
      pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H12 & _).
      destruct H12 as [(Hz & Hk) | (Hz & _ & Hk1 & Hk2 & _)].
      * exfalso. unfold gfp, bzs in Ha. rewrite length_map, Hk in Ha. cbn in Ha. clear - Ha. lia.
      * unfold gfp, bzs in Ha. rewrite length_map, rar_key_ptrs_len in Ha. cbn [fst snd] in Ha.
        apply (Hblk (re_hp e) (re_kh e)).
        -- unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
           rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- clear - Hk2. lia.
        -- unfold re_nheld in Hk1. clear - Ha Hk1. lia.
    + (* a key's text *)
      apply in_map_iff in Hr as (k & <- & Hk).
      unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd length] in Ha.
      eapply Hblk.
      * unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
        apply in_map_iff. exists k. split; [reflexivity | exact Hk].
      * clear. lia.
      * clear - Ha. lia.
Qed.

End ra.

Print Assumptions arelay_append.
Print Assumptions ra_new_entry_garr8.
Print Assumptions rar_efp_off_table.
