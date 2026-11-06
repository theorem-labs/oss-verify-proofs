From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC1i YC81 YC45 YC88 DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntryShapes DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoRo DiscoArm3 DiscoArm3FieldCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_table_c disco_json_reader_model disco_json_lemmas disco_jscalar_model slot_ser_defs slot_ser_tokb jtok_is_c
printf_facts_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma mdk_slice : forall (segs : list Segment) (m : word -> option byte) (base k : Z) (L : list byte) (n : nat),
  garr8 segs m base (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
  val_mem segs m (base + k) n (disco_table_c.u_at L k n) /\
  0 <= disco_table_c.u_at L k n < 2 ^ (8 * Z.of_nat n).
Proof.
  intros segs m base k L n HG Hk Hn. split.
  - intros j Hj. rewrite (ReacDiscoTableAge.u_at_byte L k n j Hk Hn Hj).
    replace (base + k + Z.of_nat j) with (base + Z.of_nat (Z.to_nat k + j)) by lia.
    rewrite (garr8_mbyte segs m base _ (Z.to_nat k + j) HG) by (rewrite length_map; lia).
    f_equal.
    assert (E : nth (Z.to_nat k + j) (map (fun b : byte => bv_unsigned b) L) 0 =
                bv_unsigned (nth (Z.to_nat k + j) L (Z_to_bv 8 0))).
    { rewrite <- (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0) (Z.to_nat k + j)). reflexivity. }
    rewrite E. apply Z_to_bv_bv_unsigned.
  - assert (LS : length (disco_table_c.sub L k n) = n).
    { unfold disco_table_c.sub. rewrite length_firstn, length_skipn. lia. }
    pose proof (YK11.bytes_le_to_Z_nonneg (disco_table_c.sub L k n)) as H0.
    pose proof (YK11.bytes_le_to_Z_bound (disco_table_c.sub L k n)) as H1.
    rewrite LS in H1. unfold disco_table_c.u_at. lia.
Qed.

Lemma mdk_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.

Lemma mdk_obj_len : forall buf vpad (o : disco_json_reader_model.jobj), length vpad = 4%nat ->
  length (slot_ser_defs.obj_bytes buf vpad o) = (24 * length o)%nat.
Proof.
  intros buf vpad o Hv. unfold slot_ser_defs.obj_bytes.
  induction o as [|t o IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH, mdk_slot24_len by exact Hv. lia.
Qed.

Lemma mdk_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os -> length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH, mdk_obj_len by exact Hv. rewrite Hol. lia.
Qed.

Lemma mdk_concat_off : forall (A C : Type) (f : A -> list C) (c : nat) (l : list A) (i : nat) (x : A),
  Forall (fun y => length (f y) = c) l -> nth_error l i = Some x -> forall r n, (r + n <= c)%nat ->
  firstn n (skipn (c * i + r) (concat (map f l))) = firstn n (skipn r (f x)).
Proof.
  intros A C f c l. induction l as [|a l IH]; intros i x HF Hx r n Hrn.
  - destruct i; cbn in Hx; discriminate Hx.
  - pose proof (Forall_inv HF) as Ha. pose proof (Forall_inv_tail HF) as HF'. cbv beta in Ha.
    cbn [map concat]. destruct i as [|i].
    + cbn [nth_error] in Hx. injection Hx as Hx. subst x.
      rewrite Nat.mul_0_r, Nat.add_0_l, skipn_app, firstn_app, length_skipn, Ha.
      replace (n - (c - r))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
    + cbn [nth_error] in Hx. rewrite Nat.mul_succ_r, skipn_app.
      assert (E0 : skipn (c * i + c + r) (f a) = []) by (apply skipn_all2; lia).
      rewrite E0. cbn [app].
      replace (c * i + c + r - length (f a))%nat with (c * i + r)%nat by lia.
      exact (IH i x HF' Hx r n Hrn).
Qed.

Lemma mdk_objs_slot : forall buf vpad (os : list disco_json_reader_model.jobj) p j o t,
  Forall (fun ob => length ob = 6%nat) os -> length vpad = 4%nat ->
  nth_error os (Z.to_nat p) = Some o -> nth_error o (Z.to_nat j) = Some t -> 0 <= p -> 0 <= j ->
  firstn 24 (skipn (Z.to_nat (144 * p + 24 * j)) (slot_ser_defs.objs_bytes buf vpad os)) =
  slot_ser_defs.slot24 buf vpad t.
Proof.
  intros buf vpad os p j o t HF Hv Ho Ht Hp Hj.
  assert (Ho6 : length o = 6%nat).
  { rewrite Forall_forall in HF. apply HF. eapply nth_error_In. exact Ho. }
  assert (Hj6 : (Z.to_nat j < length o)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
  assert (HFo : Forall (fun ob => length (slot_ser_defs.obj_bytes buf vpad ob) = 144%nat) os).
  { eapply Forall_impl; [|exact HF]. intros ob Hob. cbv beta in Hob |- *.
    rewrite mdk_obj_len by exact Hv. rewrite Hob. reflexivity. }
  assert (HFt : Forall (fun s => length (slot_ser_defs.slot24 buf vpad s) = 24%nat) o).
  { apply Forall_forall. intros s _. apply mdk_slot24_len. exact Hv. }
  replace (Z.to_nat (144 * p + 24 * j)) with (144 * Z.to_nat p + 24 * Z.to_nat j)%nat by lia.
  unfold slot_ser_defs.objs_bytes.
  rewrite (mdk_concat_off _ _ (slot_ser_defs.obj_bytes buf vpad) 144 os (Z.to_nat p) o HFo Ho (24 * Z.to_nat j) 24)
    by lia.
  unfold slot_ser_defs.obj_bytes.
  rewrite <- (Nat.add_0_r (24 * Z.to_nat j)).
  rewrite (mdk_concat_off _ _ (slot_ser_defs.slot24 buf vpad) 24 o (Z.to_nat j) t HFt Ht 0 24) by lia.
  cbn [skipn]. apply firstn_all2. rewrite mdk_slot24_len by exact Hv. lia.
Qed.

Lemma mdk_firstn_app : forall (A : Type) (l1 l2 : list A) n, length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof.
  intros A l1 l2 n H. rewrite firstn_app, H, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  apply firstn_all2. lia.
Qed.

Lemma mdk_skipn_app : forall (A : Type) (l1 l2 : list A) n, length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof.
  intros A l1 l2 n H. rewrite skipn_app, H, Nat.sub_diag. cbn [skipn].
  assert (E0 : skipn n l1 = []) by (apply skipn_all2; lia).
  rewrite E0. reflexivity.
Qed.

Lemma mdk_sub_in : forall (A : Type) (L S : list A) off c a n,
  firstn c (skipn off L) = S -> (a + n <= c)%nat -> firstn n (skipn (a + off) L) = firstn n (skipn a S).
Proof.
  intros A L S off c a n HS Han. subst S.
  rewrite <- skipn_skipn, skipn_firstn_comm, firstn_firstn. f_equal. lia.
Qed.

Lemma mdk_slot24_nz : forall buf vpad t, disco_json_reader_model.tv_kind t <> 0 ->
  slot_ser_defs.slot24 buf vpad t =
  Mem.le8 (Z_to_bv 64 (buf + snd (fst t))) ++ Mem.le8 (Z_to_bv 64 (snd t)) ++
  Mem.le4 (Z_to_bv 64 (disco_json_reader_model.tv_kind t)) ++ vpad.
Proof. intros buf vpad t H. unfold slot_ser_defs.slot24. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma mdk_ble8 : forall z, 0 <= z < 2 ^ 64 -> bytes_le_to_Z (Mem.le8 (Z_to_bv 64 z)) = z.
Proof.
  intros z Hz. unfold Mem.le8, word_to_le_bytes.
  rewrite Mem.bytes_le_to_Z_to_le_bytes by (rewrite (unsigned_lit_small z Hz); lia).
  change (8 * Z.of_nat 8) with 64. rewrite (unsigned_lit_small z Hz). apply Z.mod_small. exact Hz.
Qed.

Lemma mdk_ble4 : forall z, bytes_le_to_Z (Mem.le4 (Z_to_bv 64 z)) = z mod 2 ^ 32.
Proof.
  intros z. rewrite Mem.bytes_le_to_Z_le4, Z_to_bv_unsigned.
  change (bv_wrap 64 z) with (z mod 2 ^ 64).
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity].
Qed.

Lemma mdk_slot_fields : forall (segs : list Segment) (m : word -> option byte) (base buf : Z) (vpad : list byte)
    (os : list disco_json_reader_model.jobj) (p j : Z) (o : disco_json_reader_model.jobj)
    (t : disco_json_reader_model.tokv),
  garr8 segs m base (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) ->
  Forall (fun ob => length ob = 6%nat) os -> length vpad = 4%nat ->
  nth_error os (Z.to_nat p) = Some o -> nth_error o (Z.to_nat j) = Some t -> 0 <= p -> 0 <= j ->
  disco_json_reader_model.tv_kind t <> 0 -> 0 <= buf + snd (fst t) < 2 ^ 64 -> 0 <= snd t < 2 ^ 64 ->
  val_mem segs m (base + 144 * p + 24 * j) 8 (buf + snd (fst t)) /\
  val_mem segs m (base + 144 * p + 24 * j + 8) 8 (snd t) /\
  val_mem segs m (base + 144 * p + 24 * j + 16) 4 (disco_json_reader_model.tv_kind t mod 2 ^ 32).
Proof.
  intros segs m base buf vpad os p j o t HG HF Hv Ho Ht Hp Hj Hk Hvp Hvn.
  assert (Ho6 : length o = 6%nat).
  { rewrite Forall_forall in HF. apply HF. eapply nth_error_In. exact Ho. }
  assert (Hp' : (Z.to_nat p < length os)%nat) by (apply nth_error_Some; rewrite Ho; discriminate).
  assert (Hj' : (Z.to_nat j < length o)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
  pose proof (mdk_objs_len buf vpad os Hv HF) as HL.
  pose proof (mdk_objs_slot buf vpad os p j o t HF Hv Ho Ht Hp Hj) as HS.
  rewrite (mdk_slot24_nz buf vpad t Hk) in HS.
  destruct (mdk_slice segs m base (144 * p + 24 * j) _ 8 HG ltac:(lia) ltac:(lia)) as [V1 _].
  destruct (mdk_slice segs m base (144 * p + 24 * j + 8) _ 8 HG ltac:(lia) ltac:(lia)) as [V2 _].
  destruct (mdk_slice segs m base (144 * p + 24 * j + 16) _ 4 HG ltac:(lia) ltac:(lia)) as [V3 _].
  assert (E1 : disco_table_c.u_at (slot_ser_defs.objs_bytes buf vpad os) (144 * p + 24 * j) 8 = buf + snd (fst t)).
  { unfold disco_table_c.u_at, disco_table_c.sub.
    rewrite <- (Nat.add_0_l (Z.to_nat (144 * p + 24 * j))).
    rewrite (mdk_sub_in _ (slot_ser_defs.objs_bytes buf vpad os) _ (Z.to_nat (144 * p + 24 * j)) 24 0 8 HS) by lia.
    change (skipn 0 ?x) with x. rewrite mdk_firstn_app by apply Mem.length_le8. apply mdk_ble8. exact Hvp. }
  assert (E2 : disco_table_c.u_at (slot_ser_defs.objs_bytes buf vpad os) (144 * p + 24 * j + 8) 8 = snd t).
  { unfold disco_table_c.u_at, disco_table_c.sub.
    replace (Z.to_nat (144 * p + 24 * j + 8)) with (8 + Z.to_nat (144 * p + 24 * j))%nat by lia.
    rewrite (mdk_sub_in _ (slot_ser_defs.objs_bytes buf vpad os) _ (Z.to_nat (144 * p + 24 * j)) 24 8 8 HS) by lia.
    rewrite mdk_skipn_app by apply Mem.length_le8. rewrite mdk_firstn_app by apply Mem.length_le8.
    apply mdk_ble8. exact Hvn. }
  assert (E3 : disco_table_c.u_at (slot_ser_defs.objs_bytes buf vpad os) (144 * p + 24 * j + 16) 4 =
               disco_json_reader_model.tv_kind t mod 2 ^ 32).
  { unfold disco_table_c.u_at, disco_table_c.sub.
    replace (Z.to_nat (144 * p + 24 * j + 16)) with (16 + Z.to_nat (144 * p + 24 * j))%nat by lia.
    rewrite (mdk_sub_in _ (slot_ser_defs.objs_bytes buf vpad os) _ (Z.to_nat (144 * p + 24 * j)) 24 16 4 HS) by lia.
    rewrite app_assoc.
    rewrite mdk_skipn_app by (rewrite length_app, !Mem.length_le8; reflexivity).
    rewrite mdk_firstn_app by apply Mem.length_le4. apply mdk_ble4. }
  rewrite E1 in V1. rewrite E2 in V2. rewrite E3 in V3.
  split; [|split].
  - replace (base + 144 * p + 24 * j) with (base + (144 * p + 24 * j)) by lia. exact V1.
  - replace (base + 144 * p + 24 * j + 8) with (base + (144 * p + 24 * j + 8)) by lia. exact V2.
  - replace (base + 144 * p + 24 * j + 16) with (base + (144 * p + 24 * j + 16)) by lia. exact V3.
Qed.

Lemma mdk_pf_inj : forall a b, Forall (fun c => 0 <= c < 256) a -> Forall (fun c => 0 <= c < 256) b ->
  printf_facts_c.pf_bytes a = printf_facts_c.pf_bytes b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Fa Fb E; unfold printf_facts_c.pf_bytes in E; cbn [map] in E;
    try discriminate; [reflexivity|].
  pose proof (f_equal (hd (Z_to_bv 8 0)) E) as E1. pose proof (f_equal (@tl byte) E) as E2. cbn [hd tl] in E1, E2.
  inversion Fa as [|x' a' Hx Fa']; subst. inversion Fb as [|y' b' Hy Fb']; subst.
  f_equal; [|apply IH; [assumption | assumption | exact E2]].
  apply (f_equal bv_unsigned) in E1. rewrite !Z_to_bv_unsigned in E1. unfold bv_wrap in E1.
  change (bv_modulus 8) with 256 in E1. rewrite !Z.mod_small in E1 by lia. exact E1.
Qed.

Lemma mdk_forall_fs : forall (A : Type) (P : A -> Prop) l a b, Forall P l -> Forall P (firstn a (skipn b l)).
Proof.
  intros A P l a b H. apply Forall_forall. intros x Hx. rewrite Forall_forall in H. apply H.
  rewrite <- (firstn_skipn b l). apply in_or_app. right. rewrite <- (firstn_skipn a (skipn b l)).
  apply in_or_app. left. exact Hx.
Qed.

Lemma mdk_jt_iff : forall (X : list Z) (t : disco_json_reader_model.tokv) (kind : Z) (text : list Z),
  Forall (fun c => 0 <= c < 256) X -> Forall (fun c => 0 < c < 256) text -> 0 <= snd t < 2 ^ 64 ->
  jtok_is_c.jtok_match (disco_json_reader_model.tv_kind t) kind (Z_to_bv 64 (snd t))
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text X t)) (printf_facts_c.pf_bytes text) <->
  disco_json_reader_model.jtok_is X t kind text = true.
Proof.
  intros X t kind text FX FT Hl.
  assert (LP : length (printf_facts_c.pf_bytes text) = length text)
    by (unfold printf_facts_c.pf_bytes; apply length_map).
  unfold jtok_is_c.jtok_match, disco_json_reader_model.jtok_is.
  rewrite (unsigned_lit_small (snd t) Hl), LP.
  split.
  - intros (E1 & E2 & E3). rewrite E1, E2, !Z.eqb_refl. cbn [andb]. apply disco_json_lemmas.lzeqb_true.
    apply mdk_pf_inj; [| | exact E3].
    + unfold disco_json_reader_model.tv_text. apply mdk_forall_fs. exact FX.
    + eapply Forall_impl; [|exact FT]. intros c Hc. cbv beta in Hc |- *. lia.
  - intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply disco_json_lemmas.lzeqb_true in H3.
    split; [exact H1|]. split; [exact H2|]. rewrite H3. reflexivity.
Qed.

Lemma mdk_text_nz : forall s, Forall (fun c => 0 < c < 256) s -> ~ In (Z_to_bv 8 0) (printf_facts_c.pf_bytes s).
Proof.
  intros s F H. unfold printf_facts_c.pf_bytes in H. apply in_map_iff in H. destruct H as (c & E & Hc).
  rewrite Forall_forall in F. specialize (F c Hc).
  apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma mdk_map_pf : forall l, Forall (fun c => 0 <= c < 256) l -> map bv_unsigned (printf_facts_c.pf_bytes l) = l.
Proof.
  intros l F. unfold printf_facts_c.pf_bytes. rewrite map_map.
  induction F as [|x l Hx F IH]; [reflexivity|].
  cbn [map]. rewrite IH. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.

Lemma mdk_garr8_pf : forall (segs : list Segment) (m : word -> option byte) x L,
  garr8 segs m x L -> garr8 segs m x (map bv_unsigned (printf_facts_c.pf_bytes L)).
Proof.
  intros segs m x L H. rewrite mdk_map_pf; [exact H|]. exact (garr8_bytes_ok segs m x L H).
Qed.

Lemma mdk_garr8_str : forall (segs : list Segment) (m : word -> option byte) x s sl,
  garr8 segs m x (s ++ 0 :: sl) ->
  garr8 segs m x (map bv_unsigned (printf_facts_c.pf_bytes s ++ Z_to_bv 8 0 :: printf_facts_c.pf_bytes sl)).
Proof.
  intros segs m x s sl H.
  replace (printf_facts_c.pf_bytes s ++ Z_to_bv 8 0 :: printf_facts_c.pf_bytes sl)
    with (printf_facts_c.pf_bytes (s ++ 0 :: sl)) by (unfold printf_facts_c.pf_bytes; rewrite map_app; reflexivity).
  apply mdk_garr8_pf. exact H.
Qed.

Lemma mdk_garr8_sub : forall (segs : list Segment) (m : word -> option byte) p L (a n : nat),
  garr8 segs m p L -> (a + n <= length L)%nat -> garr8 segs m (p + Z.of_nat a) (firstn n (skipn a L)).
Proof.
  intros segs m p L a n HG Hle j Hj. rewrite length_firstn, length_skipn in Hj.
  rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn.
  destruct (HG (a + j)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
  replace (p + Z.of_nat a + Z.of_nat j) with (p + Z.of_nat (a + j)) by lia. exact Hv.
Qed.

Lemma mdk_text_sub : forall (X : list Z) s n, (s + n <= length X)%nat ->
  firstn n (skipn s (X ++ [0])) = firstn n (skipn s X).
Proof.
  intros X s n H. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length X - s))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma mdk_obj_tok : forall (os : list disco_json_reader_model.jobj) count (p : Z) (j : nat),
  length os = Z.to_nat count -> Forall (fun o => length o = 6%nat) os -> 0 <= p < count -> (j < 6)%nat ->
  nth_error os (Z.to_nat p) = Some (nth (Z.to_nat p) os []) /\
  nth_error (nth (Z.to_nat p) os []) j = Some (nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none) /\
  length (nth (Z.to_nat p) os []) = 6%nat.
Proof.
  intros os count p j Los Lo6 Hp Hj.
  assert (Ho : nth_error os (Z.to_nat p) = Some (nth (Z.to_nat p) os [])) by (apply nth_error_nth'; lia).
  assert (Hoi : In (nth (Z.to_nat p) os []) os) by (eapply nth_error_In; exact Ho).
  assert (Ho6 : length (nth (Z.to_nat p) os []) = 6%nat) by exact (proj1 (Forall_forall _ _) Lo6 _ Hoi).
  split; [exact Ho|]. split; [apply nth_error_nth'; lia | exact Ho6].
Qed.

Lemma mdk_jt_a3 : forall (T : list byte) now count os (p : Z) (j : nat) (kind : Z) (text : list Z)
    (t : disco_json_reader_model.tokv),
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (DiscoArm3.a3_text T now) 9 = Some (count, os) ->
  0 <= p < count -> (j < 6)%nat -> nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none = t ->
  kind <> 0 -> Forall (fun c => 0 < c < 256) text ->
  jtok_is_c.jtok_match (disco_json_reader_model.tv_kind t) kind (Z_to_bv 64 (snd t))
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T now) t))
    (printf_facts_c.pf_bytes text) <->
  disco_json_reader_model.jtok_is (DiscoArm3.a3_text T now) t kind text = true.
Proof.
  intros T now count os p j kind text t LT TOK Hnow JR Hp Hj Et Hk FT.
  destruct (DiscoArm3FieldCut.a3f_count T now count os LT TOK Hnow JR) as (_ & _ & Los & Lo6 & Inb & B33 & Lx).
  destruct (mdk_obj_tok os count p j Los Lo6 Hp Hj) as (Ho & Ht0 & Ho6).
  rewrite Et in Ht0.
  assert (Hoi : In (nth (Z.to_nat p) os []) os) by (eapply nth_error_In; exact Ho).
  assert (Hti : In t (nth (Z.to_nat p) os [])) by (eapply nth_error_In; exact Ht0).
  pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Inb _ Hoi) t Hti) as Hib.
  assert (FX : Forall (fun c => 0 <= c < 256) (DiscoArm3.a3_text T now)).
  { eapply Forall_impl; [|exact B33]. intros c Hc. cbv beta in Hc |- *. lia. }
  destruct (Z.eq_dec (disco_json_reader_model.tv_kind t) 0) as [Hz | Hnz].
  - split.
    + intros (E1 & _). lia.
    + intros H. unfold disco_json_reader_model.jtok_is in H.
      apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply Z.eqb_eq in H. lia.
  - destruct Hib as [Hz | (Hs0 & Hl0 & Hsl)]; [contradiction|]. unfold disco_jscalar_model.jlen in Hsl.
    apply mdk_jt_iff; [exact FX | exact FT | lia].
Qed.

Lemma mdk_site : forall (segs : list Segment) (m : word -> option byte) (T : list byte) (now count : Z)
    (os : list disco_json_reader_model.jobj) (p : Z) (j : nat) (base buf v kind : Z) (vpad : list byte)
    (text : list Z) (t : disco_json_reader_model.tokv),
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (DiscoArm3.a3_text T now) 9 = Some (count, os) ->
  0 <= p < count -> (j < 6)%nat -> length vpad = 4%nat ->
  garr8 segs m base (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) ->
  garr8 segs m buf (DiscoArm3.a3_text T now ++ [0]) ->
  0 <= buf -> buf + Z.of_nat (length (DiscoArm3.a3_text T now)) <= 2 ^ 63 ->
  nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none = t ->
  kind <> 0 -> Forall (fun c => 0 < c < 256) text ->
  disco_json_reader_model.jtok_is (DiscoArm3.a3_text T now) t kind text = true ->
  v = base + 144 * p + 24 * Z.of_nat j ->
  disco_json_reader_model.tv_kind t = kind /\ snd t = Z.of_nat (length text) /\
  disco_json_reader_model.tv_text (DiscoArm3.a3_text T now) t = text /\
  val_mem segs m v 8 (buf + snd (fst t)) /\ val_mem segs m (v + 8) 8 (snd t) /\
  val_mem segs m (v + 16) 4 (disco_json_reader_model.tv_kind t mod 2 ^ 32) /\
  0 <= buf + snd (fst t) < 2 ^ 64 /\ 0 <= snd t < 2 ^ 64 /\
  jtok_is_c.jtok_match (disco_json_reader_model.tv_kind t) kind (Z_to_bv 64 (snd t))
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T now) t))
    (printf_facts_c.pf_bytes text) /\
  length (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T now) t)) =
    length (printf_facts_c.pf_bytes text) /\
  garr8 segs m (buf + snd (fst t))
    (map bv_unsigned (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T now) t))) /\
  0 <= buf + snd (fst t) /\ buf + snd (fst t) + Z.of_nat (length (printf_facts_c.pf_bytes text)) <= 2 ^ 63.
Proof.
  intros segs m T now count os p j base buf v kind vpad text t LT TOK Hnow JR Hp Hj Hv GO GB Hb0 Hb63 Et Hk FT JT Ev.
  subst v.
  destruct (DiscoArm3FieldCut.a3f_count T now count os LT TOK Hnow JR) as (_ & _ & Los & Lo6 & Inb & B33 & _).
  destruct (mdk_obj_tok os count p j Los Lo6 Hp Hj) as (Ho & Ht0 & Ho6).
  rewrite Et in Ht0.
  assert (Ht : nth_error (nth (Z.to_nat p) os []) (Z.to_nat (Z.of_nat j)) = Some t) by (rewrite Nat2Z.id; exact Ht0).
  assert (Hoi : In (nth (Z.to_nat p) os []) os) by (eapply nth_error_In; exact Ho).
  assert (Hti : In t (nth (Z.to_nat p) os [])) by (eapply nth_error_In; exact Ht0).
  pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Inb _ Hoi) t Hti) as Hib.
  pose proof JT as JT0. unfold disco_json_reader_model.jtok_is in JT0.
  apply andb_prop in JT0 as [JT0 J3]. apply andb_prop in JT0 as [J1 J2].
  apply Z.eqb_eq in J1. apply Z.eqb_eq in J2. apply disco_json_lemmas.lzeqb_true in J3.
  assert (Hk' : disco_json_reader_model.tv_kind t <> 0) by (rewrite J1; exact Hk).
  destruct Hib as [Hz | (Hs0 & Hl0 & Hsl)]; [contradiction|]. unfold disco_jscalar_model.jlen in Hsl.
  assert (Hvp : 0 <= buf + snd (fst t) < 2 ^ 64) by lia.
  assert (Hvn : 0 <= snd t < 2 ^ 64) by lia.
  destruct (mdk_slot_fields segs m base buf vpad os p (Z.of_nat j) (nth (Z.to_nat p) os []) t GO Lo6 Hv Ho Ht
             ltac:(lia) ltac:(lia) Hk' Hvp Hvn) as (F1 & F2 & F3).
  assert (FX : Forall (fun c => 0 <= c < 256) (DiscoArm3.a3_text T now)).
  { eapply Forall_impl; [|exact B33]. intros c Hc. cbv beta in Hc |- *. lia. }
  pose proof (proj2 (mdk_jt_iff _ t kind text FX FT Hvn) JT) as JM.
  assert (GT : garr8 segs m (buf + snd (fst t)) (disco_json_reader_model.tv_text (DiscoArm3.a3_text T now) t)).
  { pose proof (mdk_garr8_sub segs m buf (DiscoArm3.a3_text T now ++ [0]) (Z.to_nat (snd (fst t))) (Z.to_nat (snd t))
      GB ltac:(rewrite length_app; cbn [length]; lia)) as G.
    rewrite Z2Nat.id in G by lia. rewrite mdk_text_sub in G by lia. exact G. }
  assert (LT' : length (printf_facts_c.pf_bytes text) = length text)
    by (unfold printf_facts_c.pf_bytes; apply length_map).
  split; [exact J1|]. split; [exact J2|]. split; [exact J3|].
  split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
  split; [exact Hvp|]. split; [exact Hvn|]. split; [exact JM|].
  split; [rewrite J3; reflexivity|].
  split; [exact (mdk_garr8_pf segs m _ _ GT)|].
  split; [lia|]. rewrite LT'. lia.
Qed.

Lemma mdk_tok_inb : forall (T : list byte) now count os (p : Z) (j : nat) (kind : Z) (text : list Z)
    (t : disco_json_reader_model.tokv),
  length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (DiscoArm3.a3_text T now) 9 = Some (count, os) ->
  0 <= p < count -> (j < 6)%nat -> nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none = t ->
  kind <> 0 -> Forall (fun c => 0 < c < 256) text ->
  disco_json_reader_model.jtok_is (DiscoArm3.a3_text T now) t kind text = true ->
  0 <= snd (fst t) /\
  snd (fst t) + Z.of_nat (length text) <= Z.of_nat (length (DiscoArm3.a3_text T now)).
Proof.
  intros T now count os p j kind text t LT TOK Hnow JR Hp Hj Et Hk FT JT.
  destruct (DiscoArm3FieldCut.a3f_count T now count os LT TOK Hnow JR) as (_ & _ & Los & Lo6 & Inb & _ & _).
  destruct (mdk_obj_tok os count p j Los Lo6 Hp Hj) as (Ho & Ht0 & Ho6).
  rewrite Et in Ht0.
  assert (Hoi : In (nth (Z.to_nat p) os []) os) by (eapply nth_error_In; exact Ho).
  assert (Hti : In t (nth (Z.to_nat p) os [])) by (eapply nth_error_In; exact Ht0).
  pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Inb _ Hoi) t Hti) as Hib.
  unfold disco_json_reader_model.jtok_is in JT.
  apply andb_prop in JT as [JT0 _]. apply andb_prop in JT0 as [J1 J2].
  apply Z.eqb_eq in J1. apply Z.eqb_eq in J2.
  assert (Hk' : disco_json_reader_model.tv_kind t <> 0) by (rewrite J1; exact Hk).
  destruct Hib as [Hz | (Hs0 & Hl0 & Hsl)]; [contradiction|].
  unfold disco_jscalar_model.jlen in Hsl. rewrite J2 in Hsl.
  split; [exact Hs0 | exact Hsl].
Qed.

Section mdk_sec.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section mdk_f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Section mdk_h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.

Lemma mdk_heap : forall ly S (W : world SEGS) m md p n a k,
  AR SEGS B ly S W m md -> In (p, n) (ablocks B ly S) -> p <= a -> a + k <= p + req_size n -> 0 <= k ->
  amem_range a k /\ range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a k /\
  (0 < k -> shadow_hull_vis (aview SEGS (w_H W) m) a k) /\ 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof.
intros ly S W m md p n a k HAR Hin H1 H2 Hk.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (HbSh & HbHull).
split; [exact (amem_range_sub_app p (req_size n) a k Hbapp Hbceil H1 H2 Hk)|].
split; [exact (block_shadow_range _ _ p (req_size n) a k HbSh H1 H2)|].
split; [|lia].
intros Hk0 s Hs. apply HbHull.
pose proof (YCbq.shadow_mono p a H1) as S1.
pose proof (YCbq.shadow_mono (a + k - 1) (p + req_size n - 1) ltac:(lia)) as S2.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) S1) as D1.
pose proof (Z.div_le_mono _ _ 8 ltac:(lia) S2) as D2. lia.
Qed.

Lemma mdk_cut_site : forall (cx : dcx) ly3 S3 (W : world SEGS) mem3 md3 k (h nn now op : Z)
    (T0 T1 : list byte) (buf count : Z) (os : list disco_json_reader_model.jobj) (vpad : list byte)
    (p : Z) (j : nat) (v kind : Z) (text : list Z) (t : disco_json_reader_model.tokv),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_body B cx h nn (a3_xb buf op) dsh_md ly3 S3 W mem3 ->
  a3_tab cx now T0 T1 W mem3 -> a3_buf op T1 now buf W mem3 ->
  0 <= now < 2 ^ 64 ->
  disco_json_reader_model.json_read (DiscoArm3.a3_text T1 now) 9 = Some (count, os) ->
  length vpad = 4%nat ->
  garr8 SEGS (rd W mem3) (d_obj cx OO)
    (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad os)) ->
  0 <= p < count -> (j < 6)%nat -> kind <> 0 -> Forall (fun c => 0 < c < 256) text ->
  disco_json_reader_model.jtok_is (DiscoArm3.a3_text T1 now) t kind text = true ->
  nth j (nth (Z.to_nat p) os []) disco_json_reader_model.tok_none = t ->
  v = d_obj cx OO + 144 * p + 24 * Z.of_nat j ->
  disco_json_reader_model.tv_kind t = kind /\ snd t = Z.of_nat (length text) /\
  disco_json_reader_model.tv_text (DiscoArm3.a3_text T1 now) t = text /\
  val_mem SEGS (rd W mem3) v 8 (buf + snd (fst t)) /\ val_mem SEGS (rd W mem3) (v + 8) 8 (snd t) /\
  val_mem SEGS (rd W mem3) (v + 16) 4 (disco_json_reader_model.tv_kind t mod 2 ^ 32) /\
  0 <= buf + snd (fst t) < 2 ^ 64 /\ 0 <= snd t < 2 ^ 64 /\
  jtok_is_c.jtok_match (disco_json_reader_model.tv_kind t) kind (Z_to_bv 64 (snd t))
    (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T1 now) t))
    (printf_facts_c.pf_bytes text) /\
  length (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T1 now) t)) =
    length (printf_facts_c.pf_bytes text) /\
  garr8 SEGS (rd W mem3) (buf + snd (fst t))
    (map bv_unsigned (printf_facts_c.pf_bytes (disco_json_reader_model.tv_text (DiscoArm3.a3_text T1 now) t))) /\
  0 <= buf + snd (fst t) /\ buf + snd (fst t) + Z.of_nat (length (printf_facts_c.pf_bytes text)) <= 2 ^ 63.
Proof.
intros cx ly3 S3 W mem3 md3 k h nn now op T0 T1 buf count os vpad p j v kind text t
  HCTX HBODY HTAB HBUF Hnow HJR Hvp HOO Hp Hj Hk FT JT Et Ev.
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof (proj1 HAP) as HLT1.
destruct HAP as (_ & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAR3 & _).
pose proof HBODY as (TT & GG & LL & HH & _ & _ & _ & HBLK & _).
pose proof HBLK as (HPerm0 & _).
assert (Hin : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hb4 & Hbc & _).
pose proof (YCbq.req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hbr & HGB).
pose proof alloc_ceiling_lt as Hclt.
assert (Hb63 : buf + Z.of_nat (length (DiscoArm3.a3_text T1 now)) <= 2 ^ 63).
{ unfold DiscoArm3.a3_r in Hbr. pose proof (Z.le_max_l (slot_ser_defs.ser_cap op) 1) as Hmx.
  assert (Hp47 : (2:Z) ^ 47 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). lia. }
subst v.
exact (mdk_site SEGS (rd W mem3) T1 now count os p j (d_obj cx OO) buf
  (d_obj cx OO + 144 * p + 24 * Z.of_nat j) kind vpad text t
  HLT1 HTOK1 Hnow HJR Hp Hj Hvp HOO HGB ltac:(lia) Hb63 Et Hk FT JT eq_refl).
Qed.
End mdk_h.
End mdk_f.
End mdk_sec.
