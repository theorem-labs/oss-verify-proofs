(* [comment removed for export] *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Startup_glue Zh_kit Z_kit Z_dview.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b0 := (Z_to_bv 8 0).

Definition orc (junk : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) junk b0).

Lemma orc_range : forall junk i, 0 <= orc junk i < 256.
Proof. intros junk i. unfold orc. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) junk b0)) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

Definition sub (junk : list byte) (off n : nat) : list byte := firstn n (skipn off junk).

Lemma sub_length : forall junk off n, (off + n <= length junk)%nat -> length (sub junk off n) = n.
Proof. intros junk off n H. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.

Lemma sub_S : forall junk off n, (off < length junk)%nat -> sub junk off (S n) = nth off junk b0 :: sub junk (S off) n.
Proof.
  intros junk off n H. unfold sub.
  assert (E : skipn off junk = nth off junk b0 :: skipn (S off) junk).
  { revert off H. induction junk as [|x junk IH]; intros off H; cbn [length] in H; [lia|].
    destruct off as [|off]; [reflexivity|]. cbn [skipn nth]. apply IH. lia. }
  rewrite E. reflexivity.
Qed.

Lemma sub_app : forall junk off n k, sub junk off n ++ sub junk (off + n) k = sub junk off (n + k).
Proof.
  intros junk off n k. unfold sub. replace (off + n)%nat with (n + off)%nat by lia. rewrite <- (skipn_skipn n off junk).
  generalize (skipn off junk) as l. intros l. revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn [skipn firstn Nat.add app].
  - rewrite !firstn_nil. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma sub_all : forall junk, sub junk 0 (length junk) = junk.
Proof. intros junk. unfold sub. cbn [skipn]. apply firstn_all. Qed.

Fixpoint concat_subs (junk : list byte) (off : Z) (sizes : list nat) : list byte :=
  match sizes with [] => [] | n :: r => sub junk (Z.to_nat off) n ++ concat_subs junk (off + Z.of_nat n) r end.

Lemma concat_subs_eq : forall junk sizes off, 0 <= off -> concat_subs junk off sizes = sub junk (Z.to_nat off) (sum_nat sizes).
Proof.
  intros junk sizes. induction sizes as [|n r IH]; intros off H0; cbn [concat_subs sum_nat].
  - unfold sub. reflexivity.
  - rewrite IH by lia. replace (Z.to_nat (off + Z.of_nat n)) with (Z.to_nat off + n)%nat by lia. apply sub_app.
Qed.

Fixpoint ole (g : Z -> Z) (b : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => g b + 256 * ole g (b + 1) n' end.

Lemma ole_nonneg : forall g, (forall i, 0 <= g i < 256) -> forall n b, 0 <= ole g b n.
Proof. intros g Hg n. induction n as [|n IH]; intros b; cbn [ole]; [lia|]. specialize (IH (b + 1)). specialize (Hg b). lia. Qed.

Lemma ole_app : forall g n k b, ole g b (n + k) = ole g b n + 256 ^ Z.of_nat n * ole g (b + Z.of_nat n) k.
Proof.
  intros g n. induction n as [|n IH]; intros k b.
  - cbn [Nat.add ole]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. cbn. lia.
  - cbn [Nat.add ole]. rewrite IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (b + 1 + Z.of_nat n) with (b + Z.succ (Z.of_nat n)) by lia. ring.
Qed.

Lemma bytes_orc : forall junk n off, (off + n <= length junk)%nat ->
  bytes_le_to_Z (sub junk off n) = ole (orc junk) (Z.of_nat off) n.
Proof.
  intros junk n. induction n as [|n IH]; intros off H.
  - reflexivity.
  - rewrite sub_S by lia. cbn [bytes_le_to_Z ole]. rewrite IH by lia.
    rewrite lor_shiftl8_add.
    + change (orc junk (Z.of_nat off)) with (bv_unsigned (nth (Z.to_nat (Z.of_nat off)) junk b0)).
      rewrite Nat2Z.id. replace (Z.of_nat off + 1) with (Z.of_nat (S off)) by lia. reflexivity.
    + pose proof (bv_unsigned_in_range 8 (nth off junk b0)) as R. change (bv_modulus 8) with 256 in R. exact R.
    + apply ole_nonneg. apply orc_range.
Qed.

Lemma le_ole : forall junk n off, 0 <= off -> off + Z.of_nat n <= Z.of_nat (length junk) ->
  Z_to_le_bytes n (ole (orc junk) off n) = sub junk (Z.to_nat off) n.
Proof.
  intros junk n off H0 H. rewrite <- (Z2Nat.id off) at 1 by lia. rewrite <- bytes_orc by lia.
  rewrite <- (sub_length junk (Z.to_nat off) n) at 1 by lia. apply Z_to_le_bytes_inv.
Qed.

Section Init.
Variable g : Z -> Z.
Hypothesis Hg : forall i, 0 <= g i < 256.

Lemma wrap8_g : forall i, wrap8 (g i) = g i.
Proof. intros i. rewrite wrap8_mod. change (2^8) with 256. apply Z.mod_small. apply Hg. Qed.

Lemma init_u8_ole : forall b i, init_u8 g b i = ole g (b + i) 1.
Proof. intros b i. unfold init_u8. cbn [ole]. rewrite wrap8_g. lia. Qed.

Lemma init_u16_ole : forall b i, init_u16 g b i = ole g (b + 2 * i) 2.
Proof. intros b i. unfold init_u16. cbn [ole]. rewrite !wrap8_g. lia. Qed.

Lemma init_u32_ole : forall b i, init_u32 g b i = ole g (b + 4 * i) 4.
Proof.
  intros b i. unfold init_u32. rewrite !init_u16_ole. change 4%nat with (2 + 2)%nat. rewrite ole_app.
  change (256 ^ Z.of_nat 2) with 65536. change (Z.of_nat 2) with 2.
  replace (b + 2 * (2 * i)) with (b + 4 * i) by lia. replace (b + 2 * (2 * i + 1)) with (b + 4 * i + 2) by lia. reflexivity.
Qed.

Lemma init_u64_ole : forall b i, init_u64 g b i = ole g (b + 8 * i) 8.
Proof.
  intros b i. unfold init_u64. rewrite !init_u32_ole. change 8%nat with (4 + 4)%nat. rewrite ole_app.
  change (256 ^ Z.of_nat 4) with 4294967296. change (Z.of_nat 4) with 4.
  replace (b + 4 * (2 * i)) with (b + 8 * i) by lia. replace (b + 4 * (2 * i + 1)) with (b + 8 * i + 4) by lia. reflexivity.
Qed.
End Init.

Lemma le8_Z : forall v, le8 (wz v) = Z_to_le_bytes 8 v.
Proof. intros v. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z_to_le_bytes_mod. cbn; lia. Qed.
Lemma le4_Z : forall v, le4 (wz v) = Z_to_le_bytes 4 v.
Proof. intros v. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z_to_le_bytes_mod. cbn; lia. Qed.
Lemma le2_Z : forall v, le2 (wz v) = Z_to_le_bytes 2 v.
Proof. intros v. unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply Z_to_le_bytes_mod. cbn; lia. Qed.
Lemma le1_Z : forall v, [Z_to_bv 8 v] = Z_to_le_bytes 1 v.
Proof. reflexivity. Qed.

Lemma swrap32_le : forall v, Z_to_le_bytes 4 (swrap32 v) = Z_to_le_bytes 4 v.
Proof.
  intros v. rewrite <- (Z_to_le_bytes_mod 4 (swrap32 v) 32), <- (Z_to_le_bytes_mod 4 v 32) by (cbn; lia). f_equal.
  unfold swrap32, two31. rewrite wrap32_mod.
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. f_equal. lia.
Qed.
Lemma swrap64_le : forall v, Z_to_le_bytes 8 (swrap64 v) = Z_to_le_bytes 8 v.
Proof.
  intros v. rewrite <- (Z_to_le_bytes_mod 8 (swrap64 v) 64), <- (Z_to_le_bytes_mod 8 v 64) by (cbn; lia). f_equal.
  unfold swrap64, two63. rewrite wrap64_mod.
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. f_equal. lia.
Qed.

Local Transparent zseq.
Section Cells.
Variable junk : list byte.
Local Notation g := (orc junk).
Local Notation LEN := (Z.of_nat (length junk)).

Lemma le1_orc : forall off, 0 <= off -> off + 1 <= LEN -> [Z_to_bv 8 (init_u8 g off 0)] = sub junk (Z.to_nat off) 1.
Proof. intros off H0 H. rewrite le1_Z, (init_u8_ole g (orc_range junk)), Z.add_0_r. apply le_ole; [exact H0| exact H]. Qed.
Lemma le2_orc : forall off, 0 <= off -> off + 2 <= LEN -> le2 (wz (init_u16 g off 0)) = sub junk (Z.to_nat off) 2.
Proof. intros off H0 H. rewrite le2_Z, (init_u16_ole g (orc_range junk)), Z.mul_0_r, Z.add_0_r. apply le_ole; [exact H0| exact H]. Qed.
Lemma le4_orc : forall off, 0 <= off -> off + 4 <= LEN -> le4 (wz (init_u32 g off 0)) = sub junk (Z.to_nat off) 4.
Proof. intros off H0 H. rewrite le4_Z, (init_u32_ole g (orc_range junk)), Z.mul_0_r, Z.add_0_r. apply le_ole; [exact H0| exact H]. Qed.
Lemma le4_orc_s : forall off, 0 <= off -> off + 4 <= LEN -> le4 (wz (swrap32 (init_u32 g off 0))) = sub junk (Z.to_nat off) 4.
Proof. intros off H0 H. rewrite le4_Z, swrap32_le, <- le4_Z. apply le4_orc; assumption. Qed.
Lemma le8_orc : forall off, 0 <= off -> off + 8 <= LEN -> le8 (wz (init_u64 g off 0)) = sub junk (Z.to_nat off) 8.
Proof. intros off H0 H. rewrite le8_Z, (init_u64_ole g (orc_range junk)), Z.mul_0_r, Z.add_0_r. apply le_ole; [exact H0| exact H]. Qed.
Lemma le8_orc_s : forall off, 0 <= off -> off + 8 <= LEN -> le8 (wz (swrap64 (init_u64 g off 0))) = sub junk (Z.to_nat off) 8.
Proof. intros off H0 H. rewrite le8_Z, swrap64_le, <- le8_Z. apply le8_orc; assumption. Qed.

Definition jw (off : Z) : word := wz (init_u64 g off 0).
Definition jp (off : Z) (n : nat) : list byte := sub junk (Z.to_nat off) n.

Lemma u8_map_seq : forall (f : Z -> Z) off n s, 0 <= off -> off + Z.of_nat (s + n) <= LEN ->
  (forall i, Z.of_nat s <= i < Z.of_nat (s + n) -> f i = g (off + i)) ->
  map (fun i => Z_to_bv 8 (f i)) (map Z.of_nat (seq s n)) = sub junk (Z.to_nat off + s) n.
Proof.
  intros f off n. induction n as [|n IH]; intros s H0 H Hf; [reflexivity|].
  cbn [seq map]. rewrite sub_S by lia. f_equal.
  - rewrite Hf by lia. unfold orc. replace (Z.to_nat (off + Z.of_nat s)) with (Z.to_nat off + s)%nat by lia.
    apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
  - replace (S (Z.to_nat off + s)) with (Z.to_nat off + S s)%nat by lia. apply IH; [exact H0| lia|]. intros i Hi. apply Hf. lia.
Qed.

Lemma av8_orc : forall (a : arr) off n, 0 <= off -> 0 <= n -> off + n <= LEN ->
  (forall i, 0 <= i < n -> arr_get a i = g (off + i)) ->
  av8 a n = sub junk (Z.to_nat off) (Z.to_nat n).
Proof.
  intros a off n H0 Hn H Hf. unfold av8, zseq.
  rewrite (u8_map_seq (arr_get a) off (Z.to_nat n) 0) by (try exact H0; try lia; intros i Hi; apply Hf; lia).
  rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma u16_map_seq : forall (f : Z -> Z) off n s, 0 <= off -> off + 2 * Z.of_nat (s + n) <= LEN ->
  (forall i, Z.of_nat s <= i < Z.of_nat (s + n) -> f i = ole g (off + 2 * i) 2) ->
  u16s (map (fun i => wz (f i)) (map Z.of_nat (seq s n))) = sub junk (Z.to_nat off + 2 * s) (2 * n).
Proof.
  intros f off n. induction n as [|n IH]; intros s H0 H Hf; [reflexivity|].
  cbn [seq map u16s]. rewrite Hf by lia. rewrite le2_Z, le_ole by lia.
  rewrite (IH (S s)) by (try exact H0; try lia; intros i Hi; apply Hf; lia).
  replace (Z.to_nat (off + 2 * Z.of_nat s)) with (Z.to_nat off + 2 * s)%nat by lia.
  replace (Z.to_nat off + 2 * S s)%nat with (Z.to_nat off + 2 * s + 2)%nat by lia.
  rewrite sub_app. f_equal. lia.
Qed.

Lemma av16_orc : forall (a : arr) off n, 0 <= off -> 0 <= n -> off + 2 * n <= LEN ->
  (forall i, 0 <= i < n -> arr_get a i = ole g (off + 2 * i) 2) ->
  u16s (av16 a n) = sub junk (Z.to_nat off) (Z.to_nat (2 * n)).
Proof.
  intros a off n H0 Hn H Hf. unfold av16, zseq.
  rewrite (u16_map_seq (arr_get a) off (Z.to_nat n) 0) by (try exact H0; try lia; intros i Hi; apply Hf; lia).
  f_equal; lia.
Qed.

Lemma avct_orc : forall (fc dl : arr) off n, 0 <= off -> 0 <= n -> off + 4 * n <= LEN ->
  (forall i, 0 <= i < n -> arr_get fc i = ole g (off + 4 * i) 2) ->
  (forall i, 0 <= i < n -> arr_get dl i = ole g (off + 4 * i + 2) 2) ->
  u16s (avct fc dl n) = sub junk (Z.to_nat off) (Z.to_nat (4 * n)).
Proof.
  intros fc dl off n H0 Hn H Hfc Hdl. unfold avct, zseq.
  change (map (ctw fc dl) (map Z.of_nat (seq 0 (Z.to_nat (2 * n)))))
    with (map (fun k => wz ((fun k => if Z.even k then arr_get fc (k / 2) else arr_get dl (k / 2)) k)) (map Z.of_nat (seq 0 (Z.to_nat (2 * n))))).
  rewrite (u16_map_seq _ off (Z.to_nat (2 * n)) 0); [f_equal; lia| exact H0| lia|].
  intros k Hk. cbv beta. destruct (even_div2_cases k ltac:(lia)) as [[E D]|[E D]]; rewrite E.
  - rewrite Hfc by lia. f_equal. lia.
  - rewrite Hdl by lia. f_equal. lia.
Qed.

Lemma u32_map_seq : forall (f : Z -> Z) off n s, 0 <= off -> off + 4 * Z.of_nat (s + n) <= LEN ->
  (forall i, Z.of_nat s <= i < Z.of_nat (s + n) -> Z_to_le_bytes 4 (f i) = Z_to_le_bytes 4 (ole g (off + 4 * i) 4)) ->
  u32s (map (fun i => wz (f i)) (map Z.of_nat (seq s n))) = sub junk (Z.to_nat off + 4 * s) (4 * n).
Proof.
  intros f off n. induction n as [|n IH]; intros s H0 H Hf; [reflexivity|].
  cbn [seq map u32s]. rewrite le4_Z, Hf by lia. rewrite le_ole by lia.
  rewrite (IH (S s)) by (try exact H0; try lia; intros i Hi; apply Hf; lia).
  replace (Z.to_nat (off + 4 * Z.of_nat s)) with (Z.to_nat off + 4 * s)%nat by lia.
  replace (Z.to_nat off + 4 * S s)%nat with (Z.to_nat off + 4 * s + 4)%nat by lia.
  rewrite sub_app. f_equal. lia.
Qed.

Lemma av32_orc_s : forall (a : arr) off n, 0 <= off -> 0 <= n -> off + 4 * n <= LEN ->
  (forall i, 0 <= i < n -> arr_get a i = swrap32 (ole g (off + 4 * i) 4)) ->
  u32s (av32 a n) = sub junk (Z.to_nat off) (Z.to_nat (4 * n)).
Proof.
  intros a off n H0 Hn H Hf. unfold av32, zseq.
  rewrite (u32_map_seq (arr_get a) off (Z.to_nat n) 0); [f_equal; lia| exact H0| lia|].
  intros i Hi. rewrite Hf by lia. apply swrap32_le.
Qed.
End Cells.

Lemma arr_u8_of_get : forall junk off n i, arr_get (arr_u8_of (orc junk) off 1 n) i = orc junk (off + i).
Proof. intros. unfold arr_u8_of. rewrite arr_get_init. unfold init_u8. rewrite wrap8_g by apply orc_range. f_equal. lia. Qed.
Lemma arr_u16_of_get : forall junk off stride n i, arr_get (arr_u16_of (orc junk) off stride n) i = ole (orc junk) (off + stride * i) 2.
Proof. intros. unfold arr_u16_of. rewrite arr_get_init, (init_u16_ole _ (orc_range junk)). f_equal. lia. Qed.
Lemma arr_s32_of_get : forall junk off stride n i, arr_get (arr_s32_of (orc junk) off stride n) i = swrap32 (ole (orc junk) (off + stride * i) 4).
Proof. intros. unfold arr_s32_of. rewrite arr_get_init, (init_u32_ole _ (orc_range junk)). f_equal. f_equal. lia. Qed.

Lemma cb_sub : forall m A (junk : list byte) (off n : nat), rw_cells psegs m A [CB (length junk) junk] ->
  (off + n <= length junk)%nat -> rw_cells psegs m (A + Z.of_nat off) [CB n (sub junk off n)].
Proof.
  intros m A junk off n H Hn.
  pose proof (rw_cells_split_CB psegs m A [] (length junk) junk [] [off; n; (length junk - off - n)%nat] H ltac:(cbn [sum_nat]; lia)) as S.
  cbn [app mk_CB_cells] in S.
  change ([CB off (firstn off junk); CB n (firstn n (skipn off junk)); CB (length junk - off - n) (firstn (length junk - off - n) (skipn n (skipn off junk)))])
    with ([CB off (firstn off junk)] ++ [CB n (firstn n (skipn off junk))] ++ [CB (length junk - off - n) (firstn (length junk - off - n) (skipn n (skipn off junk)))]) in S.
  apply rw_cells_app in S. destruct S as [_ S]. apply rw_cells_app in S. destruct S as [S _].
  cbn [cells_size csize] in S. rewrite Nat.add_0_r in S. exact S.
Qed.

Lemma cb_subZ : forall m A (junk : list byte) (off n : Z), rw_cells psegs m A [CB (length junk) junk] ->
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length junk) ->
  rw_cells psegs m (A + off) [CB (Z.to_nat n) (sub junk (Z.to_nat off) (Z.to_nat n))].
Proof.
  intros m A junk off n H H0 Hn HL. rewrite <- (Z2Nat.id off) at 1 by lia. apply cb_sub; [exact H| lia].
Qed.

(* 1.4 (a worker's deflateInit2_ template, ported): a word the oracle reads from bytes the
   memset zeroed is 0. *)
Lemma ole_zero : forall g n b, (forall k, b <= k < b + Z.of_nat n -> g k = 0) -> ole g b n = 0.
Proof.
  intros g n. induction n as [|n IH]; intros b H; cbn [ole]; [reflexivity|].
  rewrite H by lia. rewrite IH by (intros k Hk; apply H; lia). lia.
Qed.

Lemma jw_zero : forall junk off, 0 <= off -> (forall k, off <= Z.of_nat k < off + 8 -> nth k junk b0 = b0) -> jw junk off = wz 0.
Proof.
  intros junk off H0 HZ. unfold jw. f_equal.
  rewrite (init_u64_ole (orc junk) (orc_range junk)). rewrite Z.add_0_r.
  apply ole_zero. intros k Hk. unfold orc. rewrite HZ by lia. reflexivity.
Qed.

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_drep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg DeflateLz Deflate. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateInitLib RefDeflSafeI5b. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition dsA_raw (pS pPB pPO pGZ pW pP pH : word) (s : deflate_state) (h1 h2 h3 h4 h5 : list byte) : list cell :=
  [C8 pS;
   C4 (wz (ds_status s)); CB 4 h1;
   C8 pPB;
   C8 (wz (ds_pending_buf_size s));
   C8 pPO;
   C8 (wz (ds_pending s));
   C4 (wz (ds_wrap s)); CB 4 h2;
   C8 pGZ;
   C8 (wz (ds_gzindex s));
   C1 (Z_to_bv 8 (ds_method s)); CB 3 h3;
   C4 (wz (ds_last_flush s));
   C4 (wz (ds_w_size s));
   C4 (wz (ds_w_bits s));
   C4 (wz (ds_w_mask s)); CB 4 h4;
   C8 pW;
   C8 (wz (ds_window_size s));
   C8 pP;
   C8 pH;
   C4 (wz (ds_ins_h s));
   C4 (wz (ds_hash_size s));
   C4 (wz (ds_hash_bits s));
   C4 (wz (ds_hash_mask s));
   C4 (wz (ds_hash_shift s)); CB 4 h5;
   C8 (wz (ds_block_start s));
   C4 (wz (ds_match_length s));
   C4 (wz (ds_prev_match s));
   C4 (wz (ds_match_available s));
   C4 (wz (ds_strstart s));
   C4 (wz (ds_match_start s));
   C4 (wz (ds_lookahead s));
   C4 (wz (ds_prev_length s));
   C4 (wz (ds_max_chain_length s));
   C4 (wz (ds_max_lazy_match s));
   C4 (wz (ds_level s));
   C4 (wz (ds_strategy s));
   C4 (wz (ds_good_match s));
   C4 (wz (ds_nice_match s))].

(* 1.4: the tail takes bi_used (junk h3) and slid (junk h4), each followed by a zero pad; high_water at 5952. *)
Definition dsD_raw (pSB : word) (s : deflate_state) (h0 h1 h2 h3 h4 : list byte) : list cell :=
  [CB 7 h0;
   C8 pSB;
   C4 (wz (ds_lit_bufsize s));
   C4 (wz (ds_sym_next s));
   C4 (wz (ds_sym_end s)); CB 4 h1;
   C8 (wz (ds_opt_len s));
   C8 (wz (ds_static_len s));
   C4 (wz (ds_matches s));
   C4 (wz (ds_insert s));
   C2 (wz (ds_bi_buf s)); CB 2 h2;
   C4 (wz (ds_bi_valid s));
   CB 4 h3; C4 (wz 0);
   C8 (wz (ds_high_water s));
   CB 4 h4; C4 (wz 0)].

Section Recast.
Variable m : mem.
Variable As : Z.
Variable junk : list byte.
Variable b : blk.
Variable cs : cstrm.
Hypothesis H : rw_cells psegs m As [CB (Z.to_nat 5968) junk].
Local Notation g := (orc junk).
Local Notation s0 := (ds_of_oracle (orc junk) b cs).

Lemma recast_len : length junk = Z.to_nat 5968.
Proof. exact (proj1 (proj1 (proj1 H))). Qed.

Lemma recast_lenZ : Z.of_nat (length junk) = 5968.
Proof. rewrite recast_len. lia. Qed.

Local Ltac prep GA off n :=
  pose proof recast_len as LEN; pose proof recast_lenZ as LENZ;
  pose proof H as H'; rewrite <- LEN in H';
  pose proof (cb_subZ m As junk off n H' ltac:(lia) ltac:(lia) ltac:(lia)) as GA; clear H' LEN.

Lemma recast_A :
  rw_cells psegs m As (dsA_raw (jw junk 0) (jw junk 16) (jw junk 32) (jw junk 56) (jw junk 96) (jw junk 112) (jw junk 120) s0
                         (jp junk 12 4) (jp junk 52 4) (jp junk 73 3) (jp junk 92 4) (jp junk 148 4)).
Proof.
  prep GA 0 212. rewrite Z.add_0_r in GA.
  eapply rw_cells_recast; [exact GA| |].
  - unfold dsA_raw, jp. cbn [cells_wf cell_wf]. repeat split; apply sub_length; lia.
  - unfold dsA_raw, jw, jp.
    cbn [cells_bytes cbytes ds_of_oracle ds_status ds_pending_buf_size ds_pending ds_wrap ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask
         ds_window_size ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available
         ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match].
    rewrite ?le1_orc by lia.
    rewrite ?le8_orc_s, ?le8_orc, ?le4_orc_s, ?le4_orc by lia.
    rewrite (app_nil_r (sub junk (Z.to_nat 0) (Z.to_nat 212))).
    change (sub junk (Z.to_nat 0) (Z.to_nat 212)) with (sub junk (Z.to_nat 0) (sum_nat [8;4;4;8;8;8;8;4;4;8;8;1;3;4;4;4;4;4;8;8;8;8;4;4;4;4;4;4;8;4;4;4;4;4;4;4;4;4;4;4;4;4]%nat)).
    rewrite <- concat_subs_eq by lia. reflexivity.
Qed.

Lemma recast_Bi :
  rw_cells psegs m (As + 2904) (dsBi_cells s0 (jw junk 2904) (jw junk 2920) (jw junk 2928) (jw junk 2944) (jw junk 2952) (jw junk 2968)
                                  (jp junk 2916 4) (jp junk 2940 4) (jp junk 2964 4)).
Proof.
  prep GA 2904 72.
  eapply rw_cells_recast; [exact GA| |].
  - unfold dsBi_cells, jp. cbn [cells_wf cell_wf]. repeat split; apply sub_length; lia.
  - unfold dsBi_cells, jw, jp.
    cbn [cells_bytes cbytes ds_of_oracle ds_l_max_code ds_d_max_code ds_bl_max_code].
    rewrite ?le8_orc, ?le4_orc_s by lia.
    rewrite (app_nil_r (sub junk (Z.to_nat 2904) (Z.to_nat 72))).
    change (sub junk (Z.to_nat 2904) (Z.to_nat 72)) with (sub junk (Z.to_nat 2904) (sum_nat [8;4;4;8;8;4;4;8;8;4;4;8]%nat)).
    rewrite <- concat_subs_eq by lia. reflexivity.
Qed.

Lemma recast_C : rw_cells psegs m (As + 5300) (dsC_cells s0).
Proof.
  prep GA 5300 8.
  eapply rw_cells_recast; [exact GA| |].
  - unfold dsC_cells. cbn [cells_wf cell_wf]. auto.
  - unfold dsC_cells.
    cbn [cells_bytes cbytes ds_of_oracle ds_heap_len ds_heap_max].
    rewrite ?le4_orc_s by lia.
    rewrite (app_nil_r (sub junk (Z.to_nat 5300) (Z.to_nat 8))).
    change (sub junk (Z.to_nat 5300) (Z.to_nat 8)) with (sub junk (Z.to_nat 5300) (sum_nat [4;4]%nat)).
    rewrite <- concat_subs_eq by lia. reflexivity.
Qed.

(* 1.4: deflateInit2_ zeroes the state past its first 8 bytes (memset(s + 8, 0, 5960)) before the recast, so every
   byte from 8 on is 0. The tail's two pads are zero cells, and high_water (5952) reads the same zeros the 1.3.1
   oracle reads at 5944. *)
Hypothesis HZ : forall k, 8 <= Z.of_nat k < 5968 -> nth k junk b0 = b0.

Lemma sub_zero : forall n off, 8 <= Z.of_nat off -> Z.of_nat off + Z.of_nat n <= 5968 -> sub junk off n = repeat b0 n.
Proof.
  induction n as [|n IH]; intros off H8 Hn; [reflexivity|].
  pose proof recast_lenZ as LEN.
  rewrite sub_S by lia. rewrite HZ by lia. cbn [repeat]. f_equal. apply IH; lia.
Qed.

Lemma sub_zeroZ : forall off n, 8 <= off -> off + Z.of_nat n <= 5968 -> sub junk (Z.to_nat off) n = repeat b0 n.
Proof. intros off n H8 Hn. apply sub_zero; lia. Qed.

Lemma recast_D :
  rw_cells psegs m (As + 5881)
    (dsD_raw (jw junk 5888) s0 (jp junk 5881 7) (jp junk 5908 4) (jp junk 5938 2) (jp junk 5944 4) (jp junk 5960 4)).
Proof.
  prep GA 5881 87.
  eapply rw_cells_recast; [exact GA| |].
  - unfold dsD_raw, jp. cbn [cells_wf cell_wf]. repeat split; apply sub_length; lia.
  - unfold dsD_raw, jw, jp.
    cbn [cells_bytes cbytes ds_of_oracle ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water].
    rewrite ?le8_orc, ?le4_orc_s, ?le4_orc, ?le2_orc by lia.
    assert (ZA : le4 (wz 0) = sub junk (Z.to_nat 5948) 4) by (rewrite sub_zeroZ by lia; reflexivity).
    assert (ZB : le4 (wz 0) = sub junk (Z.to_nat 5964) 4) by (rewrite sub_zeroZ by lia; reflexivity).
    assert (ZH : sub junk (Z.to_nat 5944) 8 = sub junk (Z.to_nat 5952) 8) by (rewrite !sub_zeroZ by lia; reflexivity).
    rewrite ZA at 1. rewrite ZB. rewrite ZH.
    rewrite (app_nil_r (sub junk (Z.to_nat 5881) (Z.to_nat 87))).
    change (sub junk (Z.to_nat 5881) (Z.to_nat 87)) with (sub junk (Z.to_nat 5881) (sum_nat [7;8;4;4;4;4;8;8;4;4;2;2;4;4;4;8;4;4]%nat)).
    rewrite <- concat_subs_eq by lia. reflexivity.
Qed.

Local Ltac arr_prep GA off n :=
  prep GA off n; apply u8arr_of_rw_cells in GA.

Lemma recast_lt : dlt m (mkDL 0 As 0 0 0 0 0 0) s0.
Proof.
  arr_prep GA 212 2292.
  unfold dlt, u16arr. cbn [dl_As ds_of_oracle ds_dyn_ltree_fc ds_dyn_ltree_dl].
  rewrite (avct_orc junk _ _ 212 573) by (try lia; intros i Hi; rewrite arr_u16_of_get; f_equal; lia). exact GA.
Qed.
Lemma recast_dt : ddt m (mkDL 0 As 0 0 0 0 0 0) s0.
Proof.
  arr_prep GA 2504 244.
  unfold ddt, u16arr. cbn [dl_As ds_of_oracle ds_dyn_dtree_fc ds_dyn_dtree_dl].
  rewrite (avct_orc junk _ _ 2504 61) by (try lia; intros i Hi; rewrite arr_u16_of_get; f_equal; lia). exact GA.
Qed.
Lemma recast_bt : dbt m (mkDL 0 As 0 0 0 0 0 0) s0.
Proof.
  arr_prep GA 2748 156.
  unfold dbt, u16arr. cbn [dl_As ds_of_oracle ds_bl_tree_fc ds_bl_tree_dl].
  rewrite (avct_orc junk _ _ 2748 39) by (try lia; intros i Hi; rewrite arr_u16_of_get; f_equal; lia). exact GA.
Qed.
Lemma recast_blc : dblc m (mkDL 0 As 0 0 0 0 0 0) s0.
Proof.
  arr_prep GA 2976 32.
  unfold dblc, u16arr. cbn [dl_As ds_of_oracle ds_bl_count].
  rewrite (av16_orc junk _ 2976 16) by (try lia; intros i Hi; rewrite arr_u16_of_get; f_equal; lia). exact GA.
Qed.
Lemma recast_heap : dheap m (mkDL 0 As 0 0 0 0 0 0) s0.
Proof.
  prep GA 3008 2292. apply u8arr_of_rw_cells in GA.
  unfold dheap, u32arr. cbn [dl_As ds_of_oracle ds_heap].
  destruct GA as [GB GW]. split.
  - rewrite (av32_orc_s junk _ 3008 573) by (try lia; intros i Hi; rewrite arr_s32_of_get; f_equal; f_equal; lia). exact GB.
  - rewrite av32_length. rewrite sub_length in GW by lia. exact GW.
Qed.
Lemma recast_dep : ddep m (mkDL 0 As 0 0 0 0 0 0) s0.
Proof.
  arr_prep GA 5308 573.
  unfold ddep. cbn [dl_As ds_of_oracle ds_depth].
  rewrite (av8_orc junk _ 5308 573) by (try lia; intros i Hi; rewrite arr_u8_of_get; reflexivity). exact GA.
Qed.
End Recast.

Lemma recast_bytes : forall m A (junk : list byte) n, rw_cells psegs m A [CB (Z.to_nat n) junk] -> 0 <= n ->
  u8arr psegs m A (av8 (blk_bytes (orc junk) n) n).
Proof.
  intros m A junk n H Hn. assert (LEN : length junk = Z.to_nat n) by exact (proj1 (proj1 (proj1 H))). apply u8arr_of_rw_cells in H.
  rewrite (av8_orc junk _ 0 n) by (try lia; intros i Hi; unfold blk_bytes; rewrite arr_get_init; unfold init_u8; rewrite wrap8_g by apply orc_range; reflexivity).
  change (Z.to_nat 0) with 0%nat. rewrite <- LEN, sub_all. exact H.
Qed.

Lemma recast_ush : forall m A (junk : list byte) n, rw_cells psegs m A [CB (Z.to_nat (2 * n)) junk] -> 0 <= n ->
  u16arr psegs m A (av16 (blk_ush (orc junk) n) n).
Proof.
  intros m A junk n H Hn. assert (LEN : length junk = Z.to_nat (2 * n)) by exact (proj1 (proj1 (proj1 H))). apply u8arr_of_rw_cells in H.
  unfold u16arr.
  rewrite (av16_orc junk _ 0 n) by (try lia; intros i Hi; unfold blk_ush; rewrite arr_get_init, (init_u16_ole _ (orc_range junk)); reflexivity).
  change (Z.to_nat 0) with 0%nat. rewrite <- LEN, sub_all. exact H.
Qed.

From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Zlib_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation wq := (Z_to_bv 64).

Lemma relro_clean_of_zl : forall m, zl_statics m -> relro_clean m.
Proof.
  intros m (N1 & N2 & _) a Ha. unfold RELRO_LO, RELRO_HI in Ha. unfold ZL_RELRO_LO, ZL_RELRO_HI in N1. unfold ZL_GOT_LO, ZL_GOT_HI in N2.
  destruct (Z_lt_le_dec (bv_unsigned a) 0x293e0); [apply N1| apply N2]; lia.
Qed.

(* 1.4: zcalloc / zcfree are file-static and deflateInit2_ takes their addresses pc-relative (auipc + add); only
   the error path's z_errmsg slot (0x294d8) is still read from the GOT. *)
Lemma got_zalloc_relro : forall m, relro_clean m ->
  rw_cells psegs m 0x29438 [C8 (wq 0x29320)].
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC.
  pose (cs := [C8 (wq 0x29320)]).
  apply (InitMem.rw_cells_recast psegs m 0x29438 [CB 8 (cells_bytes cs)] cs).
  - apply (InitMem.rw_cells_image0 psegs m 0x29438 (cells_bytes cs)).
    + intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
    + vm_compute. reflexivity.
    + lia.
    + change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
  - cbn. repeat split; exact I.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Lemma cells_merge44 : forall m A pre (a b : word) post, rw_cells psegs m A (pre ++ C4 a :: C4 b :: post) ->
  rw_cells psegs m A (pre ++ CB 8 (le4 a ++ le4 b) :: post).
Proof.
  intros m A pre a b post H. eapply Zh_kit.rw_cells_recast; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. apply cells_wf_app. split; [exact W1|].
    cbn [cells_wf cell_wf] in *. split; [rewrite length_app, !length_le4; reflexivity| tauto].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma cells_split8_0 : forall m A pre post, rw_cells psegs m A (pre ++ C8 (wq 0) :: post) ->
  rw_cells psegs m A (pre ++ C4 (wq 0) :: C4 (wq 0) :: post).
Proof.
  intros m A pre post H. eapply Zh_kit.rw_cells_recast; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. apply cells_wf_app. split; [exact W1|].
    cbn [cells_wf cell_wf] in *. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. change (le8 (wq 0)) with (le4 (wq 0) ++ le4 (wq 0)). rewrite <- !app_assoc. reflexivity.
Qed.

Lemma u16s_zero_seq : forall (f : Z -> Z) n s, (forall i, Z.of_nat s <= i < Z.of_nat (s + n) -> f i = 0) ->
  u16s (map (fun i => wq (f i)) (map Z.of_nat (seq s n))) = repeat b0 (2 * n).
Proof.
  intros f n. induction n as [|n IH]; intros s Hf; [reflexivity|].
  cbn [seq map u16s]. rewrite Hf by lia. rewrite (IH (S s)) by (intros i Hi; apply Hf; lia).
  replace (2 * S n)%nat with (2 + 2 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma av16_zero : forall (a : arr) n, 0 <= n -> (forall i, 0 <= i < n -> arr_get a i = 0) ->
  u16s (av16 a n) = repeat b0 (Z.to_nat (2 * n)).
Proof.
  intros a n Hn Hf. unfold av16, zseq. rewrite (u16s_zero_seq (arr_get a) (Z.to_nat n) 0) by (intros i Hi; apply Hf; lia).
  f_equal. lia.
Qed.

Lemma c2_u8arr : forall m A (w : word), rw_cells psegs m A [C2 w] -> u8arr psegs m A (le2 w).
Proof.
  intros m A w [[_ Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw.
  split; [exact Hb| rewrite length_le2; exact Hw].
Qed.

Lemma head_cleared : forall m A (a : arr),
  rw_cells psegs m A [CB (Z.to_nat 65534) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 65534))] ->
  rw_cells psegs m (A + 65534) [C2 (wq 0)] -> arr_len a = 32768 ->
  u16arr psegs m A (av16 (arr_fill (arr_set a (32768 - 1) DeflateState.NIL) 0 (32768 - 1) 0) 32768).
Proof.
  intros m A a H1 H2 LEN. apply u8arr_of_rw_cells in H1. apply c2_u8arr in H2.
  unfold u16arr. rewrite (av16_zero _ 32768) by (first [lia | intros i Hi; apply RefDeflSafeI5b.cleared_get; [exact LEN| exact Hi]]).
  replace (repeat b0 (Z.to_nat (2 * 32768))) with (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 65534) ++ le2 (wq 0)).
  - apply u8arr_app. split; [exact H1|]. rewrite repeat_length. replace (A + Z.of_nat (Z.to_nat 65534)) with (A + 65534) by lia. exact H2.
  - change (le2 (wq 0)) with (repeat b0 2). change (Z_to_bv 8 (0 mod 256)) with b0. rewrite <- repeat_app.
    replace (Z.to_nat (2 * 32768)) with (Z.to_nat 65534 + 2)%nat by lia. reflexivity.
Qed.

Lemma dhead_LM_cleared : forall m L X, ds_hash_size X = 32768 -> dlens X ->
  rw_cells psegs m (dl_Ah L) [CB (Z.to_nat 65534) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 65534))] ->
  rw_cells psegs m (dl_Ah L + 65534) [C2 (wq 0)] -> dhead m L (RefDeflateInitLib.LM X).
Proof.
  intros m L X EHX LENS POST H2.
  unfold dhead, RefDeflateInitLib.LM, DeflateLz.clear_hash. FillWinModel.dsred. rewrite EHX.
  apply head_cleared; [exact POST| exact H2| exact (ln_head _ LENS)].
Qed.

Lemma errmsg6_relro : forall m, relro_clean m -> rw_cells psegs m 0x29350 [C8 (wq 0x10540)].
Proof.
  intros m RC. unfold relro_clean, RELRO_LO, RELRO_HI in RC.
  pose (cs := [C8 (wq 0x10540)]).
  apply (InitMem.rw_cells_recast psegs m 0x29350 [CB 8 (cells_bytes cs)] cs).
  - apply (InitMem.rw_cells_image0 psegs m 0x29350 (cells_bytes cs)).
    + intros a Ha. apply RC. change (Z.of_nat (length (cells_bytes cs))) with 8 in Ha. lia.
    + vm_compute. reflexivity.
    + lia.
    + change (Z.of_nat (length (cells_bytes cs))) with 8. lia.
  - cbn. repeat split; exact I.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Lemma zs_tail_recast : forall m A pre (jrest : list byte), rw_cells psegs m A (pre ++ [CB 24 jrest]) ->
  exists (dt : word) (p3 : list byte) (adl resv : word), rw_cells psegs m A (pre ++ [C4 dt; CB 4 p3; C8 adl; C8 resv]).
Proof.
  intros m A pre jrest H.
  assert (LEN : length jrest = 24%nat).
  { destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [W _]]. exact W. }
  destruct (Zh_kit.le4_of_bytes (firstn 4 jrest)) as (zd & _ & Ed); [rewrite length_firstn; lia|].
  destruct (Zh_kit.le8_of_bytes (firstn 8 (skipn 8 jrest))) as (za & _ & Ea); [rewrite length_firstn, length_skipn; lia|].
  destruct (Zh_kit.le8_of_bytes (skipn 16 jrest)) as (zr & _ & Er); [rewrite length_skipn; lia|].
  exists (wq zd), (firstn 4 (skipn 4 jrest)), (wq za), (wq zr).
  eapply Zh_kit.rw_cells_recast; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 _]. apply cells_wf_app. split; [exact W1|].
    cbn [cells_wf cell_wf]. repeat split. rewrite length_firstn, length_skipn. lia.
  - rewrite !cells_bytes_app. f_equal. cbn [cells_bytes cbytes]. rewrite Ed, Ea, Er, !app_nil_r.
    transitivity (firstn 4 jrest ++ skipn 4 jrest); [f_equal| apply firstn_skipn].
    transitivity (firstn 4 (skipn 4 jrest) ++ skipn 4 (skipn 4 jrest)); [f_equal| apply firstn_skipn].
    rewrite skipn_skipn. change (4 + 4)%nat with 8%nat.
    transitivity (firstn 8 (skipn 8 jrest) ++ skipn 8 (skipn 8 jrest)); [f_equal; rewrite skipn_skipn; reflexivity| apply firstn_skipn].
Qed.

Lemma agree_on_trans : forall lo hi m1 m2 m3, agree_on lo hi m1 m2 -> agree_on lo hi m2 m3 -> agree_on lo hi m1 m3.
Proof.
  intros lo hi m1 m2 m3 H1 H2 a Ha. destruct (H1 a Ha) as [E1 W1]. destruct (H2 a Ha) as [E2 W2]. split; [congruence| auto].
Qed.
Lemma agree_on_refl : forall lo hi m, agree_on lo hi m m.
Proof. intros lo hi m a _. auto. Qed.

Inductive Box (P : Prop) : Prop := box : P -> Box P.
Lemma unbox : forall P : Prop, Box P -> P.
Proof. intros P [H]. exact H. Qed.
