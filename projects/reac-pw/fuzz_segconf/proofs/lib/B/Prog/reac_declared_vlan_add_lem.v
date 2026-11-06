(* reac_declared_vlan_add, image B walk (lib/B/Prog/reac_declared_vlan_add.v, fuzz_segconf.asan-ubsan): the pure facts
   it uses, over byte lists, SegModel and Z only (no reader, no image). Written for the image-B G4 + G5 walks: the
   image-B port of lib/A/Prog/reac_declared_vlan_add_lem.v (commit fcd2fa03dd27), whose text it
   keeps, with the strcmp bridge of lib/A/Prog/check_declared.v (commit 68125773e710) and the
   integer facts of image B's UBSan tests added.
   - the search loop's model: [vad_match], [vad_existsb_skipn_S], and the three answers of SegModel.vlan_add;
   - one table entry decoded: [vad_entry_fields] (the parent's bytes up to its NUL, the vid's two bytes);
   - the appended entry: [vad_new_entry_enc] (strncpy's 15 bytes over memset's zeros, byte 15 still 0, then the vid's
     two little-endian bytes encode (firstn 15 (cut_nul p), vid)) and [vad_rtab_enc_snoc];
   - [vad_le2_byte]: the bytes of le2 as the shifts a 2-byte chunk reads;
   - [vad_bridge_strcmp]: SegModel.strcmp of two NUL-free byte strings is 0 only when they are equal;
   - the words of image B's UBSan tests: [vad_ovf_ok] (the pointer-overflow test tab + 18 k against tab, k >= 0, of
     0x8a618 .. 0x8a638, 0x8a660 .. 0x8a680 and 0x8a6a4 .. 0x8a6c8). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

(* ---------- the model of the search ---------- *)
Definition vad_match (vid : Z) (p : list Z) (e : list Z * Z) : bool := (snd e =? vid) && (strcmp (fst e) p =? 0).

Lemma vad_existsb_skipn_S : forall {A} (f : A -> bool) (l : list A) i d, (i < length l)%nat ->
  existsb f (skipn i l) = f (nth i l d) || existsb f (skipn (S i) l).
Proof.
  intros A f l. induction l as [|x l IH]; intros [|i] d Hi; cbn [length] in Hi; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma vad_existsb_skipn_all : forall {A} (f : A -> bool) (l : list A) i, (length l <= i)%nat -> existsb f (skipn i l) = false.
Proof. intros A f l i H. rewrite skipn_all2 by exact H. reflexivity. Qed.

Lemma vad_vlan_add_dup : forall t max p vid, existsb (vad_match vid p) t = true -> vlan_add t max p vid = (0, t).
Proof. intros t max p vid H. unfold vlan_add. unfold vad_match in H. rewrite H. reflexivity. Qed.

Lemma vad_vlan_add_full : forall t max p vid, existsb (vad_match vid p) t = false -> max <= Z.of_nat (length t) ->
  vlan_add t max p vid = (-1, t).
Proof.
  intros t max p vid H Hm. unfold vlan_add. unfold vad_match in H. rewrite H.
  rewrite (proj2 (Z.leb_le _ _) Hm). reflexivity.
Qed.

Lemma vad_vlan_add_app : forall t max p vid, existsb (vad_match vid p) t = false -> Z.of_nat (length t) < max ->
  vlan_add t max p vid = (1, t ++ [(firstn 15 (cut_nul p), vid)]).
Proof.
  intros t max p vid H Hm. unfold vlan_add. unfold vad_match in H. rewrite H.
  rewrite (proj2 (Z.leb_gt _ _) Hm). reflexivity.
Qed.

(* the call only appends, and only below max *)
Lemma vad_vlan_add_len : forall t max p vid, Z.of_nat (length t) <= max ->
  (length t <= length (snd (vlan_add t max p vid)))%nat /\ Z.of_nat (length (snd (vlan_add t max p vid))) <= max.
Proof.
  intros t max p vid H. unfold vlan_add.
  match goal with |- context [if existsb ?f ?l then _ else _] => destruct (existsb f l) end; [cbn [snd]; lia|].
  destruct (max <=? Z.of_nat (length t)) eqn:E; [cbn [snd]; lia|].
  apply Z.leb_gt in E. cbn [snd]. rewrite length_app. cbn [length]. lia.
Qed.

(* ---------- list helpers ---------- *)
Lemma vad_firstn_S : forall {A} (l : list A) n d, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] d H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma vad_nth_fld : forall off n bs k d, (k < n)%nat -> nth k (fld off n bs) d = nth (off + k) bs d.
Proof.
  intros off n bs k d Hk. unfold fld. rewrite nth_firstn.
  destruct (Nat.ltb_spec k n) as [_|]; [|lia]. rewrite nth_skipn; f_equal; lia.
Qed.

Lemma vad_firstn_len_app : forall {A} (a b : list A), firstn (length a) (a ++ b) = a.
Proof. intros A a b. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

(* ---------- one entry of the table ---------- *)
(* entry i of a table encoding: the parent string's bytes sx (zs sx = fst e, no NUL among them, at most 15), its
   NUL after them inside the 16-byte field, and the vid field's two bytes *)
Lemma vad_entry_fields : forall t bs i, rtab_enc t bs -> (i < length t)%nat ->
  exists sx : list byte,
    zs sx = fst (nth i t ([], 0)) /\ ~ In (Z_to_bv 8 0) sx /\ (length sx < 16)%nat /\
    (forall k, (k <= length sx)%nat -> nth (18 * i + k) bs (Z_to_bv 8 0) = nth k (sx ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) /\
    0 <= snd (nth i t ([], 0)) < 65536 /\
    (forall k, (k < 2)%nat ->
      nth (18 * i + 16 + k) bs (Z_to_bv 8 0) = nth k (Mem.le2 (Z_to_bv 64 (snd (nth i t ([], 0))))) (Z_to_bv 8 0)) /\
    (18 * i + 18 <= length bs)%nat.
Proof.
  intros t bs i [HL HE] Hi.
  destruct (HE i Hi) as (Lf & (L16 & Ls & Hn0 & Hpre) & Hv & Hvid).
  set (e := nth i t ([], 0)) in *. set (f := fld (18 * i) 18 bs) in *. set (f16 := fld 0 16 f) in *.
  set (len := length (fst e)) in *.
  assert (Hnth16 : nth len f16 (Z_to_bv 8 0) = Z_to_bv 8 0).
  { assert (Hz : nth len (firstn (S len) (zs f16)) 0 = nth len (fst e ++ [0]) 0) by (rewrite Hpre; reflexivity).
    rewrite nth_firstn in Hz. destruct (Nat.ltb_spec len (S len)) as [_|]; [|lia].
    rewrite app_nth2 in Hz by lia. rewrite Nat.sub_diag in Hz. cbn [nth] in Hz.
    unfold zs in Hz. rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) in Hz by (rewrite length_map; lia).
    rewrite map_nth in Hz. apply bv_eq. rewrite Hz. reflexivity. }
  exists (firstn len f16).
  assert (Lsx : length (firstn len f16) = len) by (rewrite length_firstn; lia).
  assert (Zsx : zs (firstn len f16) = fst e).
  { unfold zs. rewrite <- firstn_map. fold (zs f16).
    replace (firstn len (zs f16)) with (firstn len (firstn (S len) (zs f16))) by (rewrite firstn_firstn; f_equal; lia).
    rewrite Hpre. apply vad_firstn_len_app. }
  assert (Hpre16 : firstn (S len) f16 = firstn len f16 ++ [Z_to_bv 8 0]).
  { rewrite (vad_firstn_S f16 len (Z_to_bv 8 0)) by lia. rewrite Hnth16. reflexivity. }
  split; [exact Zsx|]. split.
  { intros Hin. apply Hn0. rewrite <- Zsx. change 0 with (bv_unsigned (Z_to_bv 8 0)). unfold zs. apply in_map. exact Hin. }
  split; [lia|]. split.
  { intros k Hk. rewrite Lsx in Hk. rewrite <- Hpre16.
    rewrite nth_firstn. destruct (Nat.ltb_spec k (S len)) as [_|]; [|lia].
    unfold f16. rewrite vad_nth_fld by lia. unfold f. rewrite vad_nth_fld by lia. f_equal. }
  split; [exact Hv|]. split.
  { intros k Hk. rewrite <- Hvid. rewrite vad_nth_fld by lia. unfold f. rewrite vad_nth_fld by lia. f_equal. lia. }
  rewrite HL. nia.
Qed.

(* ---------- the appended entry ---------- *)
Lemma vad_firstn_min_len : forall {A} (l : list A) n, firstn (Nat.min (length l) n) l = firstn n l.
Proof.
  intros A l n. destruct (Nat.le_ge_cases (length l) n) as [H|H].
  - rewrite Nat.min_l by exact H. rewrite firstn_all, firstn_all2 by exact H. reflexivity.
  - rewrite Nat.min_r by exact H. reflexivity.
Qed.

(* strncpy(dst, parent, 15) over memset's zeros (the 15 bytes are the parent's first min(|pb|, 15) bytes, then
   zeros), byte 15 left 0, then the vid's two bytes: seg_spec.rvlan_enc of (firstn 15 (cut_nul p), vid). *)
Lemma vad_new_entry_enc : forall (pb : list byte) p vid,
  zs pb = p -> ~ In 0 p -> 0 <= vid < 65536 ->
  rvlan_enc (firstn 15 (cut_nul p), vid)
    ((firstn (Nat.min (length pb) 15) pb ++ repeat (Z_to_bv 8 0) (15 - Nat.min (length pb) 15)) ++
     [Z_to_bv 8 0] ++ Mem.le2 (Z_to_bv 64 vid)).
Proof.
  intros pb p vid Hz Hn Hv.
  rewrite (cut_nul_id p Hn).
  assert (Lp : length pb = length p) by (rewrite <- Hz; unfold zs; symmetry; apply length_map).
  remember (Nat.min (length pb) 15) as k eqn:Ek.
  remember (firstn k pb) as q eqn:Eq.
  assert (Lq : length q = k) by (subst q k; rewrite length_firstn; lia).
  assert (Hk : (k <= 15)%nat) by (subst k; lia).
  assert (Zq : zs q = firstn 15 p).
  { subst q k. unfold zs. rewrite <- firstn_map. fold (zs pb). rewrite Hz, Lp. apply vad_firstn_min_len. }
  remember (q ++ repeat (Z_to_bv 8 0) (15 - k) ++ [Z_to_bv 8 0]) as f16 eqn:Ef16.
  replace ((q ++ repeat (Z_to_bv 8 0) (15 - k)) ++ [Z_to_bv 8 0] ++ Mem.le2 (Z_to_bv 64 vid))
    with (f16 ++ Mem.le2 (Z_to_bv 64 vid)) by (subst f16; rewrite <- !app_assoc; reflexivity).
  assert (L16 : length f16 = 16%nat) by (subst f16; rewrite !length_app, repeat_length, Lq; cbn [length]; lia).
  assert (F16 : firstn 16 (f16 ++ Mem.le2 (Z_to_bv 64 vid)) = f16) by (rewrite <- L16; apply Cells.firstn_app_exact).
  assert (S16 : skipn 16 (f16 ++ Mem.le2 (Z_to_bv 64 vid)) = Mem.le2 (Z_to_bv 64 vid))
    by (rewrite <- L16; apply Cells.skipn_app_exact).
  unfold rvlan_enc, fld. cbn [fst snd].
  change (skipn 0 (f16 ++ Mem.le2 (Z_to_bv 64 vid))) with (f16 ++ Mem.le2 (Z_to_bv 64 vid)).
  rewrite F16, S16.
  split; [rewrite length_app, L16, Mem.length_le2; reflexivity|].
  split; [|split; [exact Hv|]].
  - split; [exact L16|].
    split; [rewrite length_firstn; lia|].
    split; [intros H; apply Hn; rewrite <- (firstn_skipn 15 p); apply in_or_app; left; exact H|].
    rewrite <- Zq, Ef16. unfold zs. rewrite !map_app, length_map.
    rewrite firstn_app, firstn_all2 by (rewrite length_map; lia). rewrite length_map.
    replace (S (length q) - length q)%nat with 1%nat by lia.
    f_equal. destruct (15 - k)%nat; reflexivity.
  - apply firstn_all2. rewrite Mem.length_le2. lia.
Qed.

(* the table t at bt with one more entry's bytes after it *)
Lemma vad_rtab_enc_snoc : forall t bt e f, rtab_enc t bt -> rvlan_enc e f -> rtab_enc (t ++ [e]) (bt ++ f).
Proof.
  intros t bt e f [HL HE] HF. pose proof HF as (Lf & _).
  split.
  - rewrite !length_app, HL, Lf. cbn [length]. lia.
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length t)) as [Hlt|Hge].
    + rewrite app_nth1 by exact Hlt. unfold fld. rewrite skipn_app.
      replace (18 * i - length bt)%nat with 0%nat by lia. cbn [skipn].
      rewrite firstn_app, length_skipn.
      replace (18 - (length bt - 18 * i))%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
      exact (HE i Hlt).
    + assert (Ei : i = length t) by lia. subst i.
      rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      unfold fld. replace (18 * length t)%nat with (length bt) by lia.
      rewrite Cells.skipn_app_exact, firstn_all2 by lia. exact HF.
Qed.

(* ---------- the vid's two bytes ---------- *)
Lemma vad_le2_byte : forall v k, 0 <= v < 65536 -> (k < 2)%nat ->
  bv_unsigned (nth k (Mem.le2 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = Z.shiftr (v mod 2 ^ 16) (8 * Z.of_nat k) mod 256.
Proof.
  intros v k Hv Hk. rewrite (Z.mod_small v (2 ^ 16)) by lia.
  unfold Mem.le2. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small v (2 ^ 64)) by lia.
  destruct k as [|[|k]]; [| |lia]; cbn [Z_to_le_bytes nth];
    rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256.
  - change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - change (8 * Z.of_nat 1) with 8. reflexivity.
Qed.

(* ---------- strcmp on NUL-free strings ---------- *)
Lemma vad_zs_inj : forall l l' : list byte, zs l = zs l' -> l = l'.
Proof.
  unfold zs. induction l as [|x l IH]; intros [|y l'] H; cbn [map] in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma vad_zs_nonul : forall l : list byte, ~ In (Z_to_bv 8 0) l -> ~ In 0 (zs l).
Proof.
  intros l H Hin. unfold zs in Hin. apply in_map_iff in Hin as (b & Hb & Hin). apply H.
  replace (Z_to_bv 8 0) with b; [exact Hin|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.
Lemma vad_strcmp_eq : forall s t, ~ In 0 s -> ~ In 0 t -> strcmp s t = 0 -> s = t.
Proof.
  induction s as [|a s IH]; intros [|b t] Hs Ht H; cbn [strcmp] in H.
  - reflexivity.
  - exfalso. apply Ht. left. lia.
  - exfalso. apply Hs. left. lia.
  - revert H. destruct (Z.eqb_spec a b) as [E|E]; destruct (Z.eqb_spec a 0) as [E0|E0]; cbn [andb negb]; intros H.
    + exfalso. apply Hs. left. lia.
    + subst b. f_equal. apply IH; [intros X; apply Hs; right; exact X | intros X; apply Ht; right; exact X | exact H].
    + exfalso. lia.
    + exfalso. lia.
Qed.
Lemma vad_strcmp_refl : forall s, ~ In 0 s -> strcmp s s = 0.
Proof.
  induction s as [|a s IH]; intros Hs; cbn [strcmp]; [reflexivity|].
  rewrite Z.eqb_refl. destruct (Z.eqb_spec a 0) as [E0|E0]; [exfalso; apply Hs; left; lia|].
  cbn [andb negb]. apply IH. intros X. apply Hs. right. exact X.
Qed.
(* SegModel.strcmp of two NUL-free byte strings is 0 exactly when they are equal *)
Lemma vad_bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  (strcmp (zs sx) (zs sy) = 0 <-> sx = sy).
Proof.
  intros sx sy Hx Hy. split.
  - intros H. apply vad_zs_inj. apply vad_strcmp_eq; [apply vad_zs_nonul; exact Hx | apply vad_zs_nonul; exact Hy | exact H].
  - intros ->. apply vad_strcmp_refl. apply vad_zs_nonul. exact Hy.
Qed.

(* ---------- the words of image B's pointer-overflow tests ---------- *)
(* 0x8a618 .. 0x8a638 (and its twins after each call): a0 := tab + 18 k (mod 2^64); trap when a0 = 0, and trap
   unless (a0 <u tab) = (k <s 0). With 0 < tab, 0 <= k and tab + 18 k < 2^64 neither holds. *)
Lemma vad_ovf_ok : forall tab k, 0 < tab -> 0 <= k -> tab + 18 * k < 2 ^ 64 ->
  (tab + 18 * k) mod 2 ^ 64 <> 0 /\ ((tab + 18 * k) mod 2 ^ 64 <? tab) = false.
Proof.
  intros tab k H1 H2 H3. rewrite Z.mod_small by lia. split; [lia|]. apply Z.ltb_ge. lia.
Qed.

(* the end of the 8-byte word that holds byte e, against seg_spec.cstr_span's end of the read span after e *)
Lemma vad_word_end : forall e, e - e mod 8 + 8 = e + 1 + (- (e + 1)) mod 8.
Proof.
  intros e. pose proof (Z.div_mod e 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hb.
  set (q := e / 8) in *. set (r := e mod 8) in *.
  replace (- (e + 1)) with ((7 - r) + (- q - 1) * 8) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
