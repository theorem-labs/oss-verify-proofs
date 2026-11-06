From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts CommandModel rec_code_declared_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import memcpy_c strspn_c strcspn_c SlotSpec CommandTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma sw_strnlen_upto0 : forall M,
  strnlen_res (Z.of_nat (length M)) M = Z.of_nat (length (Verbs.upto0 M)).
Proof.
  intros M. unfold strnlen_res. rewrite Nat2Z.id, firstn_all. unfold Verbs.upto0.
  induction M as [|b M IH]; [reflexivity|].
  cbn [find_byte Verbs.upto length].
  destruct (bv_unsigned b =? 0); [reflexivity|].
  destruct (find_byte 0 M) as [i|]; cbn [length]; lia.
Qed.

Lemma sw_upto_prefix : forall (P : byte -> bool) l, Verbs.upto P l = firstn (length (Verbs.upto P l)) l.
Proof.
  intros P l. induction l as [|b l IH]; [reflexivity|].
  cbn [Verbs.upto]. destruct (P b); cbn [length firstn]; [reflexivity|]. f_equal. exact IH.
Qed.

Lemma sw_upto0_nz : forall M b, In b (Verbs.upto0 M) -> bv_unsigned b <> 0.
Proof.
  intros M b. unfold Verbs.upto0. induction M as [|x M IH]; cbn [Verbs.upto]; [cbn; tauto|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; [cbn; tauto|].
  intros [<-|H]; [exact E| exact (IH H)].
Qed.

Lemma sw_trim_snoc : forall l b,
  Verbs.trim (l ++ [b]) = if Verbs.is_trail b then Verbs.trim l else l ++ [b].
Proof.
  intros l b. unfold Verbs.trim. rewrite rev_app_distr. cbn [rev app Verbs.dropw].
  destruct (Verbs.is_trail b); [reflexivity|]. cbn [rev]. rewrite rev_involutive. reflexivity.
Qed.

Lemma sw_trim_len : forall l, (length (Verbs.trim l) <= length l)%nat.
Proof.
  induction l as [|b l IH] using rev_ind; [cbn; lia|].
  rewrite sw_trim_snoc, length_app. cbn [length].
  destruct (Verbs.is_trail b); [lia|]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma sw_trim_prefix : forall l, Verbs.trim l = firstn (length (Verbs.trim l)) l.
Proof.
  induction l as [|b l IH] using rev_ind; [reflexivity|].
  rewrite sw_trim_snoc. destruct (Verbs.is_trail b).
  - rewrite firstn_app. pose proof (sw_trim_len l).
    replace (length (Verbs.trim l) - length l)%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r. exact IH.
  - rewrite firstn_all. reflexivity.
Qed.

Lemma sw_firstn_snoc : forall (l : list byte) i b, nth_error l i = Some b -> firstn (S i) l = firstn i l ++ [b].
Proof.
  induction l as [|x l IHl]; intros [|i] b H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IHl i b H). reflexivity.
Qed.

Lemma sw_words_seps : forall pre l, (forall x, In x pre -> Verbs.is_sep x = true) ->
  Verbs.words_acc [] (pre ++ l) = Verbs.words_acc [] l.
Proof.
  induction pre as [|x pre IH]; intros l H; [reflexivity|].
  cbn [app Verbs.words_acc]. rewrite (H x (or_introl eq_refl)). cbn iota.
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma sw_words_word : forall w cur l, (forall x, In x w -> Verbs.is_sep x = false) ->
  Verbs.words_acc cur (w ++ l) = Verbs.words_acc (cur ++ w) l.
Proof.
  induction w as [|x w IH]; intros cur l H; cbn [app].
  - rewrite app_nil_r. reflexivity.
  - cbn [Verbs.words_acc]. rewrite (H x (or_introl eq_refl)). cbn iota.
    rewrite IH by (intros y Hy; apply H; right; exact Hy). rewrite <- app_assoc. reflexivity.
Qed.

Lemma sw_words_sep : forall x cur s l, Verbs.is_sep s = true ->
  Verbs.words_acc (x :: cur) (s :: l) = (x :: cur) :: Verbs.words_acc [] l.
Proof. intros x cur s l H. cbn [Verbs.words_acc]. rewrite H. reflexivity. Qed.

Definition SEPS : list byte := [Z_to_bv 8 32; Z_to_bv 8 9].

Lemma sw_in_set_seps : forall x, in_set SEPS x = Verbs.is_sep x.
Proof.
  intros x. unfold in_set, SEPS, Verbs.is_sep. cbn [existsb].
  change (bv_unsigned (Z_to_bv 8 32)) with 32. change (bv_unsigned (Z_to_bv 8 9)) with 9.
  rewrite orb_false_r, (Z.eqb_sym 32), (Z.eqb_sym 9). reflexivity.
Qed.

Lemma sw_spn_split : forall set s,
  (forall x, In x (firstn (spn_len set s) s) -> in_set set x = true) /\
  (match skipn (spn_len set s) s with [] => True | x :: _ => in_set set x = false end).
Proof.
  intros set s. induction s as [|x s IH]; cbn [spn_len firstn skipn]; [split; [cbn; tauto|exact I]|].
  destruct (in_set set x) eqn:E; cbn [firstn skipn].
  - destruct IH as [IH1 IH2]. split; [|exact IH2]. intros y [<-|Hy]; [exact E| exact (IH1 y Hy)].
  - split; [cbn; tauto| exact E].
Qed.

Lemma sw_cspn_split : forall set s,
  (forall x, In x (firstn (cspn_len set s) s) -> in_set set x = false) /\
  (match skipn (cspn_len set s) s with [] => True | x :: _ => in_set set x = true end).
Proof.
  intros set s. induction s as [|x s IH]; cbn [cspn_len firstn skipn]; [split; [cbn; tauto|exact I]|].
  change (existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned x)) set) with (in_set set x).
  destruct (in_set set x) eqn:E; cbn [firstn skipn].
  - split; [cbn; tauto| exact E].
  - destruct IH as [IH1 IH2]. split; [|exact IH2]. intros y [<-|Hy]; [exact E| exact (IH1 y Hy)].
Qed.

Lemma sw_spn_le : forall set s, (spn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn [spn_len length]; [lia|]. destruct (in_set set x); lia. Qed.

Lemma sw_cspn_le : forall set s, (cspn_len set s <= length s)%nat.
Proof. intros set s. induction s as [|x s IH]; cbn [cspn_len length]; [lia|]. destruct (existsb _ set); lia. Qed.

Definition sw_trail_z (z : Z) : bool := (z =? 32) || (z =? 9) || (z =? 10) || (z =? 13).

Lemma sw_is_trail_z : forall b, Verbs.is_trail b = sw_trail_z (bv_unsigned b).
Proof. reflexivity. Qed.

Lemma sw_trail_mask : forall z, 0 <= z <= 32 ->
  Z.land (Z.shiftr 4294977024 (z mod 64)) 1 = if sw_trail_z z then 1 else 0.
Proof.
  intros z Hz.
  assert (H : forallb (fun z => Z.eqb (Z.land (Z.shiftr 4294977024 (z mod 64)) 1) (if sw_trail_z z then 1 else 0))
                (zseq 33) = true) by (vm_compute; reflexivity).
  pose proof (forallb_zseq 33 _ H z ltac:(lia)) as E. cbn beta in E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma sw_trail_big : forall z, 32 < z -> sw_trail_z z = false.
Proof.
  intros z Hz. unfold sw_trail_z.
  rewrite (proj2 (Z.eqb_neq z 32)), (proj2 (Z.eqb_neq z 9)), (proj2 (Z.eqb_neq z 10)), (proj2 (Z.eqb_neq z 13)) by lia.
  reflexivity.
Qed.

Lemma sw_nth_at : forall {X} (A B : list X) x, nth_error (A ++ x :: B) (length A) = Some x.
Proof. intros X A B x. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

Lemma sw_upd_at : forall {X} (A B : list X) x y, upd (A ++ x :: B) (length A) y = A ++ y :: B.
Proof. intros X A. induction A as [|a A IH]; intros B x y; cbn; [reflexivity|]. f_equal. apply IH. Qed.

Lemma sw_upd_bytes_at : forall (A R xs : list byte), (length xs <= length R)%nat ->
  upd_bytes (A ++ R) (length A) xs = A ++ xs ++ skipn (length xs) R.
Proof.
  intros A R xs H. unfold upd_bytes. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  f_equal. f_equal. rewrite skipn_app, skipn_all2 by lia. cbn [app]. f_equal. lia.
Qed.

Lemma sw_firstn_skipn_app : forall (A B : list byte) j n, (j + n <= length A)%nat ->
  firstn n (skipn j (A ++ B)) = firstn n (skipn j A).
Proof.
  intros A B j n H. rewrite skipn_app. replace (j - length A)%nat with 0%nat by lia.
  rewrite firstn_app. rewrite length_skipn. replace (n - (length A - j))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma sw_bytes_mid : forall m A (X Y Z : list byte), bytes_at rsegs m A (X ++ Y ++ Z) ->
  bytes_at rsegs m (A + Z.of_nat (length X)) Y.
Proof.
  intros m A X Y Z H. apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma sw_wr_at_split : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; (split; [lia|]; split; [lia|]).
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hl & H) & (Ha' & Hl' & H')). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i n1) as [L|L]; [apply H; lia|].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

Lemma sw_u8arr_app : forall m A (X Y : list byte),
  u8arr rsegs m A (X ++ Y) <-> u8arr rsegs m A X /\ u8arr rsegs m (A + Z.of_nat (length X)) Y.
Proof.
  intros m A X Y. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add.
  rewrite sw_wr_at_split by lia. tauto.
Qed.

Lemma sw_nth_skipn : forall {X} (l : list X) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  intros X l. induction l as [|x l IH]; intros n i.
  - destruct n, i; reflexivity.
  - destruct n; [reflexivity|]. cbn [skipn Nat.add nth_error]. apply IH.
Qed.

Lemma sw_nth_firstn : forall {X} (l : list X) n i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X l. induction l as [|x l IH]; intros n i H.
  - destruct n, i; reflexivity.
  - destruct n; [lia|]. destruct i; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma sw_nth_firstn_ge : forall {X} (l : list X) n i, (n <= i)%nat -> nth_error (firstn n l) i = None.
Proof.
  intros X l. induction l as [|x l IH]; intros n i H.
  - destruct n, i; reflexivity.
  - destruct n; [destruct i; reflexivity|]. destruct i; [lia|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma sw_ext : forall {X} (l l' : list X), (forall i, nth_error l i = nth_error l' i) -> l = l'.
Proof.
  intros X l. induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros i. exact (H (S i)).
Qed.

Lemma sw_firstn_of_nth : forall (C X : list byte) j, (j + length X <= length C)%nat ->
  (forall t, (t < length X)%nat -> nth_error C (j + t) = nth_error X t) -> firstn (length X) (skipn j C) = X.
Proof.
  intros C X j Hl H. apply sw_ext. intros t. destruct (Nat.lt_ge_cases t (length X)) as [L|L].
  - rewrite sw_nth_firstn by exact L. rewrite sw_nth_skipn. exact (H t L).
  - rewrite sw_nth_firstn_ge by exact L. symmetry. apply nth_error_None. exact L.
Qed.

Lemma sw_bytes_nth : forall m A (C X : list byte) j,
  bytes_at rsegs m A C -> (j + length X <= length C)%nat ->
  (forall t, (t < length X)%nat -> nth_error C (j + t) = nth_error X t) ->
  bytes_at rsegs m (A + Z.of_nat j) X.
Proof.
  intros m A C X j (Ha & Hl & H) Hj HX. split; [lia|]. split; [lia|].
  intros t Ht. rewrite <- (HX t Ht). replace (A + Z.of_nat j + Z.of_nat t) with (A + Z.of_nat (j + t)) by lia.
  apply H. lia.
Qed.

Lemma sw_skipn_app0 : forall (L : list byte) i z, (i <= length L)%nat -> skipn i (L ++ [z]) = skipn i L ++ [z].
Proof. intros L i z H. rewrite skipn_app. replace (i - length L)%nat with 0%nat by lia. reflexivity. Qed.

Lemma sw_in_firstn : forall {X} (l : list X) n x, In x (firstn n l) -> In x l.
Proof. intros X l n x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma sw_in_skipn : forall {X} (l : list X) n x, In x (skipn n l) -> In x l.
Proof. intros X l n x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma sw_line_nz : forall M b, In b (Verbs.line M) -> bv_unsigned b <> 0.
Proof.
  intros M b H. apply (sw_upto0_nz M). unfold Verbs.line in H. rewrite sw_trim_prefix in H.
  exact (sw_in_firstn _ _ _ H).
Qed.

Lemma sw_line_le : forall M, (length (Verbs.line M) <= length (Verbs.upto0 M))%nat.
Proof. intros M. apply sw_trim_len. Qed.

Lemma sw_nth_z : forall (L : list byte) j, (forall b, In b L -> bv_unsigned b <> 0) -> (j <= length L)%nat ->
  exists b, nth_error (L ++ [Z_to_bv 8 0]) j = Some b /\ (bv_unsigned b = 0 <-> j = length L).
Proof.
  intros L j HZ Hj. destruct (Nat.eq_dec j (length L)) as [E|E].
  - exists (Z_to_bv 8 0). split.
    + rewrite E, nth_error_app2, Nat.sub_diag by lia. reflexivity.
    + split; [intros _; exact E | intros _; reflexivity].
  - destruct (nth_error L j) as [b|] eqn:Eb; [| apply nth_error_None in Eb; lia].
    exists b. split; [rewrite nth_error_app1 by lia; exact Eb|].
    split; [intros H; exfalso; exact (HZ b (nth_error_In L j Eb) H) | intros H; lia].
Qed.

Lemma sw_skipn_cons : forall {X} (l : list X) k x r, skipn k l = x :: r -> nth_error l k = Some x /\ skipn (S k) l = r.
Proof.
  intros X l. induction l as [|y l IH]; intros [|k] x r H; cbn in H |- *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - exact (IH k x r H).
Qed.

Lemma sw_firstn_upd_bytes : forall (Aa xs : list byte) n, (n + length xs <= length Aa)%nat ->
  firstn (n + length xs) (upd_bytes Aa n xs) = firstn n Aa ++ xs.
Proof.
  intros Aa xs n H. apply sw_ext. intros t. unfold upd_bytes.
  assert (L : length (firstn n Aa) = n) by (apply firstn_length_le; lia).
  destruct (Nat.lt_ge_cases t (n + length xs)) as [T|T].
  - rewrite sw_nth_firstn by exact T. destruct (Nat.lt_ge_cases t n) as [T2|T2].
    + rewrite !nth_error_app1 by lia. reflexivity.
    + rewrite (nth_error_app2 (firstn n Aa) (xs ++ skipn (n + length xs) Aa)) by lia.
      rewrite (nth_error_app2 (firstn n Aa) xs) by lia. rewrite L. rewrite nth_error_app1 by lia. reflexivity.
  - rewrite sw_nth_firstn_ge by exact T. symmetry. apply nth_error_None. rewrite length_app. lia.
Qed.

Lemma sw_upd_bytes_len : forall (Aa xs : list byte) n, (n + length xs <= length Aa)%nat ->
  length (upd_bytes Aa n xs) = length Aa.
Proof. intros Aa xs n H. apply upd_bytes_length. exact H. Qed.

Lemma sw_concat_snoc : forall (wp : list Z) p,
  concat (map (fun q => le8 (Z_to_bv 64 q)) (wp ++ [p])) = concat (map (fun q => le8 (Z_to_bv 64 q)) wp) ++ le8 (Z_to_bv 64 p).
Proof. intros wp p. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.

(* One round of the splitter on the rest str of the line: skip separators, take the word up to the next
   separator or the end. *)
Lemma sw_round : forall (str str2 : list byte) s c,
  s = spn_len SEPS str -> str2 = skipn s str -> c = cspn_len SEPS str2 -> (s < length str)%nat ->
  (1 <= c)%nat /\
  (c = length str2 -> Verbs.words_acc [] str = [str2]) /\
  ((c < length str2)%nat -> exists x, nth_error str2 c = Some x /\ Verbs.is_sep x = true /\
     Verbs.words_acc [] str = firstn c str2 :: Verbs.words_acc [] (skipn (S c) str2)).
Proof.
  intros str str2 s c Es E2 Ec Hs.
  destruct (sw_spn_split SEPS str) as [SP1 SP2]. rewrite <- Es in SP1, SP2. rewrite <- E2 in SP2.
  assert (Wseps : Verbs.words_acc [] str = Verbs.words_acc [] str2).
  { rewrite <- (firstn_skipn s str), <- E2. apply sw_words_seps. intros x Hx. rewrite <- sw_in_set_seps. exact (SP1 x Hx). }
  destruct str2 as [|b r].
  { exfalso. apply (f_equal (@length byte)) in E2. rewrite length_skipn in E2. cbn [length] in E2. lia. }
  assert (Hb : in_set SEPS b = false) by exact SP2.
  destruct (sw_cspn_split SEPS (b :: r)) as [CP1 CP2]. rewrite <- Ec in CP1, CP2.
  assert (Hc1 : (1 <= c)%nat).
  { rewrite Ec. cbn [cspn_len]. unfold in_set in Hb. rewrite Hb. lia. }
  assert (Wword : Verbs.words_acc [] (b :: r) = Verbs.words_acc (firstn c (b :: r)) (skipn c (b :: r))).
  { rewrite <- (firstn_skipn c (b :: r)) at 1. rewrite sw_words_word; [reflexivity|].
    intros x Hx. rewrite <- sw_in_set_seps. exact (CP1 x Hx). }
  split; [exact Hc1|]. split.
  - intros Hc. rewrite Wseps, Wword, Hc, firstn_all, skipn_all. reflexivity.
  - intros Hc. destruct (skipn c (b :: r)) as [|x r'] eqn:Ek.
    + exfalso. apply (f_equal (@length byte)) in Ek. rewrite length_skipn in Ek. cbn [length] in Ek, Hc. lia.
    + destruct (sw_skipn_cons _ _ _ _ Ek) as [Ex Er]. exists x. split; [exact Ex|].
      assert (Hx : in_set SEPS x = true) by exact CP2. rewrite sw_in_set_seps in Hx. split; [exact Hx|].
      rewrite Wseps, Wword. destruct (firstn c (b :: r)) as [|y w] eqn:Ef.
      * exfalso. apply (f_equal (@length byte)) in Ef. rewrite firstn_length_le in Ef by lia. cbn [length] in Ef. lia.
      * rewrite sw_words_sep by exact Hx. rewrite Er. reflexivity.
Qed.

Section Words.
Variables (ra sp gp tp s2 s3 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
  (lo src len text copy arr : Z) (M : list byte) (can : word).

Notation SP := (bv_unsigned sp).
Notation L0 := (strnlen_res len M).
Notation ws := (Verbs.words (Verbs.line M)).
Notation W0 := [(text, text + strnlen_res len M + 1); (copy, copy + strnlen_res len M + 1);
                (arr, arr + arr_size (strnlen_res len M)); (bv_unsigned sp - 96, bv_unsigned sp + 72)].

Hypothesis H_lo : 0x54cb8 <= lo.
Hypothesis H_LOS : lo + 96 <= SP.
Hypothesis H_SPH : SP + 176 <= 2 ^ 64.
Hypothesis H_len : 0 <= len <= 8192.
Hypothesis H_src : 0 <= src /\ src + len <= lo.
Hypothesis H_L0 : 0 <= L0 <= len.
Hypothesis H_tx : 0 < text /\ text + L0 + 1 <= lo.
Hypothesis H_cp : 0 < copy /\ copy + L0 + 1 <= lo.
Hypothesis H_ar : 0 < arr /\ arr + arr_size L0 <= lo.
Hypothesis H_AS : arr_size L0 = 8 * (L0 / 2) + 16.

Definition sw_post : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' T C Aa wp jsv' jp,
      ms' = MS (mkR (Z_to_bv 64 0x142cc) sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len)
                    (Z_to_bv 64 (bv_unsigned sp + 40)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 (Z_to_bv 64 (bv_unsigned s8 - len)) s8
                    (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32) t3' t4' t5' t6')
             F (Z_to_bv 64 0x14404) fc None m' (seg_rom rsegs) /\
      munch W0 m0 m' /\
      wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
      rw_cells rsegs m' (bv_unsigned sp) (LOC0 jsv') /\
      rw_cells rsegs m' (bv_unsigned sp + 40)
        [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); C4 (Z_to_bv 64 (Z.of_nat (length ws)));
         CB 4 jp] /\
      rw_cells rsegs m' text [CB (Z.to_nat (L0 + 1)) T] /\
      rw_cells rsegs m' copy [CB (Z.to_nat (L0 + 1)) C] /\
      rw_cells rsegs m' arr [CB (Z.to_nat (arr_size L0)) Aa] /\
      length wp = length ws /\
      firstn (8 * length ws) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) /\
      (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
         copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0 + 1 /\
         firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]).

Definition sw_words_ok (C Aa : list byte) (wp : list Z) : Prop :=
  length wp = length ws /\
  firstn (8 * length ws) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) /\
  (forall k p w, nth_error wp k = Some p -> nth_error ws k = Some w ->
     copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + L0 + 1 /\
     firstn (length w + 1) (skipn (Z.to_nat (p - copy)) C) = w ++ [Z_to_bv 8 0]).

Lemma sw_fin0 : forall m1 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' T C Aa wp jsv' jp,
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP (LOC0 jsv') ->
  rw_cells rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr);
                               C4 (Z_to_bv 64 (Z.of_nat (length ws))); CB 4 jp] ->
  u8arr rsegs m1 text T -> length T = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 copy C -> length C = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 arr Aa -> length Aa = Z.to_nat (arr_size L0) ->
  sw_words_ok C Aa wp ->
  evt rsegs sw_post
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
             s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6 s7' s8 (Z_to_bv 64 MASK) (Z_to_bv 64 arr)
             (Z_to_bv 64 32) t3' t4' t5' t6') F (Z_to_bv 64 0x142c0) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' T C Aa wp jsv' jp
    MU WM MI ST FR0 FR1 TX LT CP LC AR LA (WL & WF & WW).
  step. step. step.
  rewrite (unsigned_lit len) by lia.
  apply evt_done. unfold sw_post.
  do 21 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact FR0|]. split; [exact FR1|].
  split; [rewrite <- LT; apply rw_cells_of_u8arr; exact TX|].
  split; [rewrite <- LC; apply rw_cells_of_u8arr; exact CP|].
  split; [rewrite <- LA; apply rw_cells_of_u8arr; exact AR|].
  split; [exact WL|]. split; [exact WF|]. exact WW.
Qed.

Lemma sw_fin1 : forall m1 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' cnt t3' t4' t5' t6' T C Aa wp jp,
  cnt = Z_to_bv 64 (Z.of_nat (length ws)) ->
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP [C8 (Z_to_bv 64 58); C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 G_REC); C8 s8; C8 s6] ->
  rw_cells rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr);
                               C4 (Z_to_bv 64 0); CB 4 jp] ->
  u8arr rsegs m1 text T -> length T = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 copy C -> length C = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 arr Aa -> length Aa = Z.to_nat (arr_size L0) ->
  sw_words_ok C Aa wp ->
  evt rsegs sw_post
    (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0' a1' a2' a3' a4' a5' a6' a7'
             s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6' s7' cnt (Z_to_bv 64 MASK) (Z_to_bv 64 arr)
             (Z_to_bv 64 32) t3' t4' t5' t6') F (Z_to_bv 64 0x142b4) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' s7' cnt t3' t4' t5' t6' T C Aa wp jp
    -> MU WM MI ST FR0 FR1 TX LT CP LC AR LA WOK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  step. step. step.
  pose proof (rw_cells_merge rsegs _ _ [C8 (Z_to_bv 64 58); C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 G_REC)]
                [C8 s8; C8 s6] [] FR0) as FR0'.
  cbn [cells_size csize Nat.add app] in FR0'.
  eapply sw_fin0; [exact MU | exact WM | exact MI | exact ST | exact FR0' | exact FR1 | exact TX | exact LT
    | exact CP | exact LC | exact AR | exact LA | exact WOK].
Qed.


(* ---- the run of the inlined word splitter from the third malloc's return (0x141c8) ---- *)

Notation LN := (Verbs.line M).
Notation U := (Verbs.upto0 M).

Hypothesis SSPN : strspn_contract.
Hypothesis SCSPN : strcspn_contract.
Hypothesis MEMC : memcpy_contract.
Hypothesis H_M : Z.of_nat (length M) = len.
Hypothesis H_txi : text + L0 + 1 <= 0x10000 \/ 0x54cb8 <= text.
Hypothesis H_cpi : copy + L0 + 1 <= 0x10000 \/ 0x54cb8 <= copy.
Hypothesis H_ari : arr + arr_size L0 <= 0x10000 \/ 0x54cb8 <= arr.
Hypothesis H_d1 : text + L0 + 1 <= copy \/ copy + L0 + 1 <= text.
Hypothesis H_d2 : arr + arr_size L0 <= text \/ text + L0 + 1 <= arr.
Hypothesis H_d3 : arr + arr_size L0 <= copy \/ copy + L0 + 1 <= arr.
Hypothesis H_d4 : src + len <= text \/ text + L0 + 1 <= src.

Lemma sw_L0 : L0 = Z.of_nat (length U).
Proof. rewrite <- H_M. apply sw_strnlen_upto0. Qed.

Definition sw_found (C : list byte) (wp : list Z) (i : nat) : Prop :=
  forall k' p w, nth_error wp k' = Some p -> nth_error ws k' = Some w ->
    copy <= p /\ p + Z.of_nat (length w) + 1 <= copy + Z.of_nat i /\
    forall t, (t <= length w)%nat -> nth_error C (Z.to_nat (p - copy) + t) = nth_error (w ++ [Z_to_bv 8 0]) t.

Lemma sw_found_ok : forall C Aa wp i, sw_found C wp i -> Z.of_nat i <= L0 + 1 -> length C = Z.to_nat (L0 + 1) ->
  length wp = length ws -> firstn (8 * length ws) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) ->
  sw_words_ok C Aa wp.
Proof.
  intros C Aa wp i FD Hi LC Lw FA. split; [exact Lw|]. split; [exact FA|].
  intros k' p w Ep Ew. destruct (FD k' p w Ep Ew) as (P1 & P2 & P3).
  split; [exact P1|]. split; [lia|].
  replace (length w + 1)%nat with (length (w ++ [Z_to_bv 8 0])) by (rewrite length_app; reflexivity).
  apply sw_firstn_of_nth.
  - rewrite length_app. cbn [length]. lia.
  - intros t Ht. rewrite length_app in Ht. cbn [length] in Ht. apply P3. lia.
Qed.

Lemma sw_found_upd : forall C wp i j b, sw_found C wp i -> (i <= j)%nat -> sw_found (upd C j b) wp i.
Proof.
  intros C wp i j b FD Hj k' p w Ep Ew. destruct (FD k' p w Ep Ew) as (P1 & P2 & P3).
  split; [exact P1|]. split; [exact P2|]. intros t Ht. rewrite nth_error_upd_other by lia. exact (P3 t Ht).
Qed.

Lemma sw_found_snoc : forall C wp i i' p w,
  sw_found C wp i -> nth_error ws (length wp) = Some w -> copy <= p ->
  p + Z.of_nat (length w) + 1 <= copy + Z.of_nat i' -> (i <= i')%nat ->
  (forall t, (t <= length w)%nat -> nth_error C (Z.to_nat (p - copy) + t) = nth_error (w ++ [Z_to_bv 8 0]) t) ->
  sw_found C (wp ++ [p]) i'.
Proof.
  intros C wp i i' p w FD Ew H1 H2 Hi HW k' p' w' Ep Ew'.
  destruct (Nat.lt_ge_cases k' (length wp)) as [L|L].
  - rewrite nth_error_app1 in Ep by exact L. destruct (FD k' p' w' Ep Ew') as (P1 & P2 & P3).
    split; [exact P1|]. split; [lia | exact P3].
  - rewrite nth_error_app2 in Ep by exact L. destruct (k' - length wp)%nat as [|q] eqn:Eq.
    + cbn in Ep. injection Ep as <-. replace k' with (length wp) in Ew' by lia. rewrite Ew in Ew'. injection Ew' as <-.
      split; [exact H1|]. split; [exact H2 | exact HW].
    + cbn in Ep. destruct q; discriminate.
Qed.

(* The word w = firstn c (skipn i0 LN) sits at C[i0 ..] when C holds LN's bytes there and a 0 after it. *)
Lemma sw_word_nth : forall (C : list byte) i0 c, (i0 + c <= length LN)%nat ->
  (forall j, (i0 <= j < i0 + c)%nat -> nth_error C j = nth_error LN j) ->
  nth_error C (i0 + c) = Some (Z_to_bv 8 0) ->
  forall t, (t <= length (firstn c (skipn i0 LN)))%nat ->
    nth_error C (i0 + t) = nth_error (firstn c (skipn i0 LN) ++ [Z_to_bv 8 0]) t.
Proof.
  intros C i0 c Hc HL H0 t Ht.
  assert (Lw : length (firstn c (skipn i0 LN)) = c) by (apply firstn_length_le; rewrite length_skipn; lia).
  rewrite Lw in Ht. destruct (Nat.lt_ge_cases t c) as [T|T].
  - rewrite nth_error_app1 by lia. rewrite sw_nth_firstn by exact T. rewrite sw_nth_skipn. apply HL. lia.
  - replace t with c by lia. rewrite nth_error_app2 by lia. rewrite Lw, Nat.sub_diag. exact H0.
Qed.

Lemma sw_upd_bytes1 : forall (C : list byte) j b, (j < length C)%nat -> upd_bytes C j [b] = upd C j b.
Proof.
  intros C j b H. unfold upd_bytes. rewrite upd_firstn_skipn by exact H. cbn [length app].
  replace (j + 1)%nat with (S j) by lia. reflexivity.
Qed.

Lemma sw_arr_snoc : forall (Aa : list byte) (wp : list Z) k p,
  length wp = k -> (8 * k + 8 <= length Aa)%nat ->
  firstn (8 * k) Aa = concat (map (fun q => le8 (Z_to_bv 64 q)) wp) ->
  firstn (8 * S k) (upd_bytes Aa (Z.to_nat (8 * Z.of_nat k)) (le8 (Z_to_bv 64 p))) =
    concat (map (fun q => le8 (Z_to_bv 64 q)) (wp ++ [p])).
Proof.
  intros Aa wp k p Hk HA AF. replace (Z.to_nat (8 * Z.of_nat k)) with (8 * k)%nat by lia.
  replace (8 * S k)%nat with (8 * k + length (le8 (Z_to_bv 64 p)))%nat by (rewrite length_le8; lia).
  rewrite sw_firstn_upd_bytes by (rewrite length_le8; lia). rewrite AF, sw_concat_snoc. reflexivity.
Qed.

(* The word w = LN[i0 .. i0 + c) found at copy + i0, followed by a 0 in C. *)
Lemma sw_word_found : forall (C : list byte) wp i k i0 c w,
  sw_found C wp i -> length wp = k -> nth_error ws k = Some w -> w = firstn c (skipn i0 LN) ->
  (i <= i0)%nat -> (i0 + c <= length LN)%nat ->
  (forall j, (i0 <= j < i0 + c)%nat -> nth_error C j = nth_error LN j) ->
  nth_error C (i0 + c) = Some (Z_to_bv 8 0) ->
  sw_found C (wp ++ [copy + Z.of_nat i0]) (i0 + c + 1).
Proof.
  intros C wp i k i0 c w FD Hwp Ew Ew2 Hi0 Hc HL H0.
  assert (Lw : length w = c) by (rewrite Ew2; apply firstn_length_le; rewrite length_skipn; lia).
  apply (sw_found_snoc C wp i (i0 + c + 1) (copy + Z.of_nat i0) w FD); [rewrite Hwp; exact Ew | lia | lia | lia |].
  intros t Ht. replace (Z.to_nat (copy + Z.of_nat i0 - copy)) with i0 by lia. rewrite Ew2.
  apply (sw_word_nth C i0 c Hc HL H0). rewrite <- Ew2. exact Ht.
Qed.

Ltac sw_eqv :=
  unfold wa;
  first [ reflexivity | f_equal; lia | apply bv_eq; repeat rewrite unsigned_lit by lia; lia ].

Ltac sw_prem :=
  first [ eassumption
        | match goal with H : forall A, A = _ -> bytes_at _ _ A _ |- bytes_at _ _ _ _ => apply H; lia end
        | apply lit_at; [eassumption | vm_compute; reflexivity | lia | unfold SEPS; cbn [length app]; lia]
        | unfold SEPS; cbn [length]; lia
        | apply notin_nul_lit; vm_compute; reflexivity
        | intros ?HL; cbn [length SEPS] in HL; lia
        | unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD, strcspn_c.CSPN_SSP_GOT, strcspn_c.CSPN_SSP_GUARD; lia
        | lia ].

Ltac sw_show := match goal with |- ?G => idtac "SWGOAL:" G end.

(* Speed (common.md Proof speed (2)): lia case-splits every disjunction it reads, and sw_loop carries the seven
   placement disjunctions H_txi .. H_d4 into every lia call, store and callee transport. sw_loop hides them at its
   start and shows each store only the three its transports need. Before each store it clears the array fact that
   store_done would drop (AR, CP): dropping it costs a failing lia. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.

Lemma sw_loop : forall (nm i k : nat) m1 T C Aa (wp : list Z) ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8'
    t3' t4' t5' t6' a0v s6v s7v jp,
  nm = (length LN - i)%nat -> (i <= length LN)%nat -> (2 * k <= i)%nat -> length wp = k ->
  a0v = Z_to_bv 64 (Z.of_nat k) -> s6v = Z_to_bv 64 (arr + 8 * Z.of_nat k) -> s7v = Z_to_bv 64 (copy + Z.of_nat i) ->
  munch W0 m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo SP ->
  rw_cells rsegs m1 SP [C8 (Z_to_bv 64 58); C8 (Z_to_bv 64 REC_CODES); C8 (Z_to_bv 64 G_REC); C8 s8; C8 s6] ->
  rw_cells rsegs m1 (SP + 40) [C8 (Z_to_bv 64 text); C8 (Z_to_bv 64 copy); C8 (Z_to_bv 64 arr); C4 (Z_to_bv 64 0);
                               CB 4 jp] ->
  u8arr rsegs m1 text T -> length T = Z.to_nat (L0 + 1) ->
  u8arr rsegs m1 copy C -> length C = Z.to_nat (L0 + 1) ->
  (forall j, (i <= j <= length LN)%nat -> nth_error C j = nth_error (LN ++ [Z_to_bv 8 0]) j) ->
  u8arr rsegs m1 arr Aa -> length Aa = Z.to_nat (arr_size L0) ->
  firstn (8 * k) Aa = concat (map (fun p => le8 (Z_to_bv 64 p)) wp) ->
  (k <= length ws)%nat -> Verbs.words_acc [] (skipn i LN) = skipn k ws ->
  sw_found C wp i ->
  bytes_at rsegs m1 strspn_c.SSP_GOT (le8 (Z_to_bv 64 strspn_c.SSP_GUARD)) ->
  bytes_at rsegs m1 strspn_c.SSP_GUARD (le8 can) ->
  evt rsegs sw_post (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 src) (Z_to_bv 64 len) a0v a1' a2' a3' a4' a5' a6' a7'
       s2 s3 (Z_to_bv 64 text) (Z_to_bv 64 copy) s6v s7v s8' (Z_to_bv 64 MASK) (Z_to_bv 64 arr) (Z_to_bv 64 32)
       t3' t4' t5' t6') F (Z_to_bv 64 0x14258) fc None m1 (seg_rom rsegs)).
(* The section variables of the base proof, so the discharged sw_loop keeps its type: the hidden disjunctions let
   lia find certificates that no longer use H_src, and hiding H_d4 (unused before) would use it, so it is cleared. *)
Proof using sp gp tp s2 s3 s6 s8 F fc m0 lo src len text copy arr M can H_lo H_LOS H_SPH H_len H_src H_L0 H_tx
  H_cp H_ar H_AS SSPN SCSPN H_M H_txi H_cpi H_ari H_d1 H_d2 H_d3.
  intros nm. induction nm as [nm IH] using (well_founded_ind lt_wf).
  intros i k m1 T C Aa wp ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' a0v s6v s7v jp
    Hnm Hi Hk Hwp -> -> -> MU WM MI ST FR0 FR1 TX LT CP LC CF AR LA AF Hkw WA FD G1 G2.
  clear H_d4. rs_hide_all.
  pose proof sw_L0 as EL0. pose proof (sw_line_le M) as HLL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold strspn_c.SSP_GOT, strspn_c.SSP_GUARD in G1, G2.
  assert (NZL : forall b, In b LN -> bv_unsigned b <> 0) by (intros b Hb; exact (sw_line_nz M b Hb)).
  assert (Lsk : length (skipn i LN) = (length LN - i)%nat) by apply length_skipn.
  assert (NZ1 : ~ In (Z_to_bv 8 0) (skipn i LN)).
  { intros Hb. apply (NZL _ (sw_in_skipn _ _ _ Hb)). reflexivity. }
  assert (BS1 : forall A, A = copy + Z.of_nat i -> bytes_at rsegs m1 A (skipn i LN ++ [Z_to_bv 8 0])).
  { intros A ->. rewrite <- sw_skipn_app0 by exact Hi. apply (sw_bytes_nth m1 copy C); [exact (proj1 CP) | |].
    - rewrite length_skipn, length_app. cbn [length]. lia.
    - intros t Ht. rewrite length_skipn, length_app in Ht. cbn [length] in Ht. rewrite sw_nth_skipn. apply CF. lia. }
  do 5 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (SSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn i LN) SEPS lo can);
      rewrite ?unsigned_lit by lia; try sw_prem
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold strspn_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  clear BS1.
  match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
  pose proof (sw_spn_le SEPS (skipn i LN)) as Hs. rewrite Lsk in Hs.
  remember (spn_len SEPS (skipn i LN)) as s eqn:Es.
  destruct (sw_nth_z LN (i + s) NZL ltac:(lia)) as (b & Eb & Hb0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RD : ov_read_bytes rsegs mm (wa (copy + Z.of_nat (i + s))) 1 = Some [b])
      by (apply (u8arr_read rsegs mm copy C (Z.of_nat (i + s)) b);
          [assumption | rewrite Nat2Z.id, CF by lia; exact Eb | lia | reflexivity])
  end.
  step. step. clear RD.
  pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. cbn in RB.
  step. if_cases HZ; zify_cond HZ; rewrite ?unsigned_lit in HZ by lia.
  - (* the rest of the line is separators: w.n = k, the exit at 0x142b4 *)
    assert (Esl : (i + s)%nat = length LN) by (apply Hb0; exact HZ).
    assert (Hall : forall x, In x (skipn i LN) -> Verbs.is_sep x = true).
    { intros y Hy. destruct (sw_spn_split SEPS (skipn i LN)) as [SP1 _]. rewrite <- Es in SP1.
      rewrite firstn_all2 in SP1 by lia. rewrite <- sw_in_set_seps. exact (SP1 y Hy). }
    assert (Hkw2 : length ws = k).
    { pose proof (sw_words_seps (skipn i LN) [] Hall) as E. rewrite app_nil_r, WA in E. cbn [Verbs.words_acc] in E.
      apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn [length] in E. lia. }
    eapply sw_fin1; [rewrite Hkw2; reflexivity | eassumption .. | ].
    eapply sw_found_ok; [eassumption | lia | eassumption | lia | rewrite Hkw2; exact AF].
  - (* a word starts at i + s: store its address, find its end *)
    assert (Hs2 : (i + s < length LN)%nat) by (assert ((i + s)%nat <> length LN) by (intros E; apply HZ, Hb0, E); lia).
    remember (skipn s (skipn i LN)) as str2 eqn:E2.
    assert (E2' : str2 = skipn (i + s) LN) by (rewrite E2, skipn_skipn; f_equal; lia).
    assert (L2 : length str2 = (length LN - (i + s))%nat) by (rewrite E2', length_skipn; reflexivity).
    assert (H8 : (8 * k + 8 <= length Aa)%nat).
    { rewrite LA, H_AS. Z.div_mod_to_equations. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SOK : store_ok rsegs mm (wa (arr + 8 * Z.of_nat k)) 8 = true)
        by (apply (u8arr_store_ok_n rsegs mm arr Aa (8 * Z.of_nat k) 8); [assumption | lia | lia | reflexivity])
    end.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
      replace a with (wa (arr + 8 * Z.of_nat k)) by (unfold wa; f_equal; lia);
      pose proof (u8arr_write_bytes rsegs mm arr Aa (8 * Z.of_nat k) bs ltac:(assumption) ltac:(lia)
                    ltac:(rewrite length_le8; lia)) as AR2
    end.
    clear AR. unfold rs_hold in H_d2, H_d3, H_ari.
    store_done.
    rs_hide_all.
    remember (upd_bytes Aa (Z.to_nat (8 * Z.of_nat k)) (le8 (Z_to_bv 64 (copy + Z.of_nat i + Z.of_nat s)))) as Aa2 eqn:EAa2.
    assert (LA2 : length Aa2 = Z.to_nat (arr_size L0))
      by (rewrite EAa2, upd_bytes_length by (rewrite length_le8; lia); exact LA).
    assert (AF2 : firstn (8 * S k) Aa2 = concat (map (fun q => le8 (Z_to_bv 64 q)) (wp ++ [copy + Z.of_nat (i + s)]))).
    { rewrite EAa2. replace (copy + Z.of_nat (i + s)) with (copy + Z.of_nat i + Z.of_nat s) by lia.
      apply sw_arr_snoc; [exact Hwp | exact H8 | exact AF]. }
    clear EAa2.
    assert (NZ2 : ~ In (Z_to_bv 8 0) (skipn (i + s) LN)).
    { intros Hb'. apply (NZL _ (sw_in_skipn _ _ _ Hb')). reflexivity. }
    assert (L2' : length (skipn (i + s) LN) = (length LN - (i + s))%nat) by apply length_skipn.
    assert (BS2 : forall A, A = copy + Z.of_nat i + Z.of_nat s ->
              bytes_at rsegs m A (skipn (i + s) LN ++ [Z_to_bv 8 0])).
    { intros A ->. rewrite <- sw_skipn_app0 by lia.
      replace (copy + Z.of_nat i + Z.of_nat s) with (copy + Z.of_nat (i + s)) by lia.
      apply (sw_bytes_nth m copy C); [exact (proj1 CP) | |].
      - rewrite length_skipn, length_app. cbn [length]. lia.
      - intros t Ht. rewrite length_skipn, length_app in Ht. cbn [length] in Ht. rewrite sw_nth_skipn. apply CF. lia. }
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply (SCSPN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (skipn (i + s) LN) [] SEPS lo can);
        rewrite ?unsigned_lit by lia; try sw_prem; try (cbn [length]; lia)
      | let ms' := fresh "ms'" in let PO := fresh "PO" in
        intros ms' PO; unfold strcspn_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
        post_call rsegs mm ]
    end.
    clear BS2.
    try (match goal with H : stk _ _ _ _ |- _ => rename H into ST end).
    remember (cspn_len SEPS (skipn (i + s) LN)) as c eqn:Ec.
    assert (Ec' : c = cspn_len SEPS str2) by (rewrite E2'; exact Ec).
    destruct (sw_round (skipn i LN) str2 s c Es E2 Ec' ltac:(lia)) as (Hc1 & Hfull & Hpart).
    pose proof (sw_cspn_le SEPS (skipn (i + s) LN)) as Hcl. rewrite <- Ec, L2' in Hcl.
    destruct (sw_nth_z LN (i + s + c) NZL ltac:(lia)) as (b2 & Eb2 & Hb2).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (RD : ov_read_bytes rsegs mm (wa (copy + Z.of_nat (i + s + c))) 1 = Some [b2])
        by (apply (u8arr_read rsegs mm copy C (Z.of_nat (i + s + c)) b2);
            [assumption | rewrite Nat2Z.id, CF by lia; exact Eb2 | lia | reflexivity])
    end.
    step. step. clear RD.
    pose proof (bv_unsigned_in_range 8 b2) as RB2. unfold bv_modulus in RB2. cbn in RB2.
    step. if_cases HZ2; zify_cond HZ2; rewrite ?unsigned_lit in HZ2 by lia.
    + (* the word runs to the end of the line: the exit at 0x142b0 *)
      assert (Esl2 : (i + s + c)%nat = length LN) by (apply Hb2; exact HZ2).
      assert (Hcf : c = length str2) by lia.
      pose proof (Hfull Hcf) as W1. rewrite WA in W1.
      destruct (sw_skipn_cons _ _ _ _ W1) as [Ew WS1].
      assert (Hkw2 : length ws = S k).
      { apply (f_equal (@length _)) in WS1. rewrite length_skipn in WS1. cbn [length] in WS1.
        pose proof (nth_error_Some ws k) as NS. rewrite Ew in NS.
        assert (KW : (k < length ws)%nat) by (apply NS; discriminate). lia. }
      assert (FD2 : sw_found C (wp ++ [copy + Z.of_nat (i + s)]) (i + s + c + 1)).
      { apply (sw_word_found C wp i k (i + s) c str2 FD Hwp Ew); [ | lia | lia | | ].
        - rewrite E2', firstn_all2; [reflexivity | rewrite length_skipn; lia].
        - intros j Hj. rewrite CF by lia. apply nth_error_app1. lia.
        - rewrite CF by lia. rewrite Esl2, nth_error_app2, Nat.sub_diag by lia. reflexivity. }
      step.
      eapply sw_fin1; [ rewrite Hkw2; sw_eqv | eassumption .. | ].
      eapply sw_found_ok; [exact FD2 | lia | exact LC | rewrite length_app, Hwp, Hkw2; cbn [length]; lia | ].
      rewrite Hkw2. exact AF2.
    + (* a separator ends the word: put a 0 there *)
      assert (Hlt : (i + s + c < length LN)%nat).
      { assert ((i + s + c)%nat <> length LN) by (intros E; apply HZ2, Hb2, E). lia. }
      assert (Hcp : (c < length str2)%nat) by lia.
      destruct (Hpart Hcp) as (xsep & Ex & Hx & W2). rewrite WA in W2.
      destruct (sw_skipn_cons _ _ _ _ W2) as [Ew WS].
      assert (KW : (k < length ws)%nat).
      { pose proof (nth_error_Some ws k) as NS. rewrite Ew in NS. apply NS. discriminate. }
      assert (WA' : Verbs.words_acc [] (skipn (i + s + c + 1) LN) = skipn (S k) ws).
      { rewrite WS, E2', skipn_skipn. replace (S c + (i + s))%nat with (i + s + c + 1)%nat by lia. reflexivity. }
      destruct (sw_nth_z LN (i + s + c + 1) NZL ltac:(lia)) as (b3 & Eb3 & Hb3).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (RD : ov_read_bytes rsegs mm (wa (copy + Z.of_nat (i + s + c + 1))) 1 = Some [b3])
          by (apply (u8arr_read rsegs mm copy C (Z.of_nat (i + s + c + 1)) b3);
              [assumption | rewrite Nat2Z.id, CF by lia; exact Eb3 | lia | reflexivity])
      end.
      step. clear RD.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SOK2 : store_ok rsegs mm (wa (copy + Z.of_nat (i + s + c))) 1 = true)
          by (apply (u8arr_store_ok_n rsegs mm copy C (Z.of_nat (i + s + c)) 1); [assumption | lia | lia | reflexivity])
      end.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?a ?bs) _) =>
        replace a with (wa (copy + Z.of_nat (i + s + c))) by (unfold wa; f_equal; lia);
        assert (EB0 : bs = [Z_to_bv 8 0]) by (apply StrFun.map_unsigned_inj; vm_compute; reflexivity);
        pose proof (u8arr_write_bytes rsegs mm copy C (Z.of_nat (i + s + c)) bs ltac:(assumption) ltac:(lia)
                      ltac:(rewrite EB0; cbn [length]; lia)) as CP2;
        rewrite EB0 in CP2 |- *
      end.
      clear CP. unfold rs_hold in H_d1, H_d3, H_cpi.
      store_done.
      rs_hide_all.
      rewrite Nat2Z.id, sw_upd_bytes1 in CP2 by lia.
      remember (upd C (i + s + c) (Z_to_bv 8 0)) as C2 eqn:EC2.
      assert (LC2 : length C2 = Z.to_nat (L0 + 1)) by (rewrite EC2, upd_length; exact LC).
      assert (CF2 : forall j, (i + s + c + 1 <= j <= length LN)%nat ->
                nth_error C2 j = nth_error (LN ++ [Z_to_bv 8 0]) j).
      { intros j Hj. rewrite EC2, nth_error_upd_other by lia. apply CF. lia. }
      assert (FD2 : sw_found C2 (wp ++ [copy + Z.of_nat (i + s)]) (i + s + c + 1)).
      { apply (sw_word_found C2 wp i k (i + s) c (firstn c str2)); [ | exact Hwp | exact Ew | | lia | lia | | ].
        - rewrite EC2. apply sw_found_upd; [exact FD | lia].
        - rewrite E2'. reflexivity.
        - intros j Hj. rewrite EC2, nth_error_upd_other by lia. rewrite CF by lia. apply nth_error_app1. lia.
        - rewrite EC2. apply nth_error_upd_same. lia. }
      clear EC2.
      step. step.
      pose proof (bv_unsigned_in_range 8 b3) as RB3. unfold bv_modulus in RB3. cbn in RB3.
      step. if_cases HZ3; zify_cond HZ3; rewrite ?unsigned_lit in HZ3 by lia.
      * (* more of the line: the next round *)
        eapply (IH (length LN - (i + s + c + 1))%nat ltac:(lia) (i + s + c + 1)%nat (S k) _ _ C2 Aa2
                  (wp ++ [copy + Z.of_nat (i + s)]));
          [ reflexivity | lia | lia | rewrite length_app, Hwp; cbn [length]; lia | sw_eqv | sw_eqv | sw_eqv
          | try eassumption .. ].
        all: try lia.
      * (* the separator was the line's last byte: the exit at 0x142b0 *)
        assert (Esl3 : (i + s + c + 1)%nat = length LN) by (apply Hb3; exact HZ3).
        assert (Hkw2 : length ws = S k).
        { rewrite Esl3, skipn_all in WA'. cbn [Verbs.words_acc] in WA'.
          apply (f_equal (@length _)) in WA'. rewrite length_skipn in WA'. cbn [length] in WA'. lia. }
        step.
        eapply sw_fin1; [ rewrite Hkw2; sw_eqv | eassumption .. | ].
        eapply sw_found_ok; [exact FD2 | lia | exact LC2 | rewrite length_app, Hwp, Hkw2; cbn [length]; lia | ].
        rewrite Hkw2. exact AF2.
Qed.
End Words.
