(** Facts for the checking segment of reac-pw/fuzz_headamp's LLVMFuzzerTestOneInput: the reads of the record in the
    pp block (Pod/Layout.v's pp_bytes), the entry fields pod_string / pod_bool / pod_int / pod_float read, C strings
    in an entry body, the word arithmetic of the compiled tests, and the memory transports the walk uses (stack
    cells, MemNorm.task_mem). fuzz_role's checking-segment facts with the module path renamed and its role-only
    lemmas left out. Image-independent: the segment list is a Section variable, so the UBSan walk uses the same
    lemmas. No function of a binary is proved here. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa.
Import ListNotations.
Open Scope Z_scope.

(** A disjunction lia does not split. *)
Definition or_h (P Q : Prop) : Prop := P \/ Q.

(** ** Word arithmetic of the compiled tests *)
Lemma signed_lit : forall x, -2^63 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - replace (x mod 2^64) with (x + 2^64) by (apply Z.mod_unique with (q := -1); lia).
    destruct (Z.ltb_spec (x + 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec x (2^63)); lia.
Qed.

Lemma eqb_s : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|Hne]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros E. apply Hne.
  Z.div_mod_to_equations. lia.
Qed.

Lemma eqb_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bv_eqb_true : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma zxb_eqb0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof. intros b. unfold zxb. pose proof (byte_range b). apply eqb_u; lia. Qed.

Lemma swrap32_id : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(** addiw x, x, 1 of a small value. *)
Lemma addiw1_small : forall x, 0 <= x -> x + 1 < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + 1)) = Z_to_bv 64 (x + 1).
Proof. intros x H1 H2. f_equal. rewrite unsigned_lit by lia. apply swrap32_id. lia. Qed.

Lemma lts_s : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.

Lemma ltu_u : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma swrap32_s32 : forall t, 0 <= t < 2^32 -> bv_swrap 32 t = s32 t.
Proof.
  intros t Ht. unfold bv_swrap, bv_wrap, s32. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.ltb_spec t (2^31)).
  - rewrite Z.mod_small by lia. lia.
  - replace (t + 2^31) with ((t - 2^31) + 1 * 2^32) by lia. rewrite Z.mod_add by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma sx32_lit : forall t, 0 <= t < 2^32 -> sx32 (Z_to_bv 64 t) = Z_to_bv 64 (s32 t).
Proof. intros t Ht. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_s32 by lia. reflexivity. Qed.

Lemma s32_small : forall t, 0 <= t < 2^31 -> s32 t = t.
Proof. intros t Ht. unfold s32. destruct (Z.ltb_spec t (2^31)); lia. Qed.

Lemma sx32_small : forall t, 0 <= t < 2^31 -> sx32 (Z_to_bv 64 t) = Z_to_bv 64 t.
Proof. intros t Ht. rewrite sx32_lit by lia. rewrite s32_small by lia. reflexivity. Qed.

Lemma s32_eq_small : forall t c, 0 <= t < 2^32 -> 0 <= c < 2^31 -> (s32 t =? c) = (t =? c).
Proof. intros t c Ht Hc. unfold s32. destruct (Z.ltb_spec t (2^31)); [reflexivity|]. destruct (Z.eqb_spec (t - 2^32) c); destruct (Z.eqb_spec t c); lia. Qed.

Lemma sx32_eqb : forall t c, 0 <= t < 2^32 -> 0 <= c < 2^31 -> bv_eqb (sx32 (Z_to_bv 64 t)) (Z_to_bv 64 c) = (t =? c).
Proof.
  intros t c Ht Hc. rewrite sx32_lit by lia. pose proof (s32_range t Ht) as R.
  rewrite eqb_s by lia. apply s32_eq_small; lia.
Qed.

(** sext.w of a small value. *)
Lemma sextw_small : forall v, -2^31 <= v < 2^31 -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0)) = Z_to_bv 64 v.
Proof.
  intros v Hv. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, Z.add_0_r.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  replace ((v mod 2^64 + 2^31) mod 2^32) with (v + 2^31)
    by (rewrite <- Z.add_mod_idemp_l by lia;
        rewrite (Z.mod_mod_divide v (2^64) (2^32)) by (exists (2^32); reflexivity);
        rewrite Z.add_mod_idemp_l by lia; symmetry; apply Z.mod_small; lia).
  f_equal. lia.
Qed.

(** The 32-bit zero extension `slli 32; srli 32` of a small value. *)
Lemma zext32_small : forall z, 0 <= z < 2^32 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 32))) 32) = Z_to_bv 64 z.
Proof.
  intros z Hz. f_equal. rewrite (unsigned_lit z) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia.
Qed.

(** ent[v]'s offset 104 v by `slli 32; mulhu` with 104 << 32. *)
Lemma mulhu_idx : forall v, 0 <= v < 2^31 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 v)) 32)) * 446676598784) 64)
  = Z_to_bv 64 (104 * v).
Proof.
  intros v Hv. f_equal. rewrite (unsigned_lit v) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (v * 2 ^ 32 * 446676598784) with (104 * v * 2^64) by (change 446676598784 with (104 * 2^32); ring).
  apply Z.div_mul. lia.
Qed.

(** ** The record in the pp block *)
Lemma ents_bodies : forall r, pod_rec_wf r -> Forall (fun e => (length (e_body e) <= 96)%nat) (ents r).
Proof.
  intros r Hw. destruct (ents_wf r Hw) as [_ Hf]. eapply Forall_impl; [|exact Hf].
  intros e (_ & Hb & Hs). lia.
Qed.

Lemma buf_len : forall r, pod_rec_wf r -> Z.of_nat (length (buf r)) <= POD_BUF_MAX.
Proof. intros r Hw. destruct (buf_header r Hw) as (_ & _ & _ & H). unfold POD_BUF_MAX. lia. Qed.

Ltac pp_side r Hw :=
  first [ exact (buf_len r Hw) | exact (proj1 (ents_wf r Hw)) | exact (ents_bodies r Hw) ].

Lemma pp_corrupt : forall r, pod_rec_wf r ->
  firstn 4 (skipn (Z.to_nat OFF_CORRUPT) (pp_bytes r)) = le32 (Z.b2z (corrupt r)).
Proof. intros r Hw. unfold pp_bytes. apply pp_read_corrupt; pp_side r Hw. Qed.

Lemma pp_is_props : forall r, pod_rec_wf r ->
  firstn 4 (skipn (Z.to_nat OFF_IS_PROPS) (pp_bytes r)) = le32 (Z.b2z (is_props r)).
Proof. intros r Hw. unfold pp_bytes. apply pp_read_is_props; pp_side r Hw. Qed.

Lemma pp_params_struct : forall r, pod_rec_wf r ->
  firstn 4 (skipn (Z.to_nat OFF_PARAMS_STRUCT) (pp_bytes r)) = le32 (Z.b2z (params_struct r)).
Proof. intros r Hw. unfold pp_bytes. apply pp_read_params_struct; pp_side r Hw. Qed.

Lemma pp_n_ent : forall r, pod_rec_wf r ->
  firstn 4 (skipn (Z.to_nat OFF_N_ENT) (pp_bytes r)) = le32 (Z.of_nat (length (ents r))).
Proof. intros r Hw. unfold pp_bytes. apply pp_read_n_ent; pp_side r Hw. Qed.

Lemma pp_ent : forall r i, pod_rec_wf r -> (i < length (ents r))%nat ->
  firstn 104 (skipn (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat i)) (pp_bytes r)) = ent_mem (nth i (ents r) (Ent 0 0 [])).
Proof. intros r i Hw Hi. unfold pp_bytes. apply pp_read_ent; [pp_side r Hw | pp_side r Hw | pp_side r Hw | exact Hi]. Qed.

Lemma pp_buf : forall r, firstn (length (buf r)) (pp_bytes r) = buf r.
Proof. intros r. unfold pp_bytes, pp_image. apply firstn_app_eq. reflexivity. Qed.

Lemma ent_wf_nth : forall r i, pod_rec_wf r -> (i < length (ents r))%nat -> ent_wf (nth i (ents r) (Ent 0 0 [])).
Proof.
  intros r i Hw Hi. destruct (ents_wf r Hw) as [_ Hf]. rewrite Forall_forall in Hf. apply Hf. apply nth_In. exact Hi.
Qed.

(** ** One step of pod_next_pair over the record (Pod/Accessors.v pairs_by) *)
Lemma skipn_nth_cons : forall {A} (l : list A) j d, (j < length l)%nat -> skipn j l = nth j l d :: skipn (S j) l.
Proof.
  intros A l. induction l as [|x l IH]; intros j d Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(** The key test of pod_string. *)
Lemma key_of_cases : forall e,
  key_of e = if (e_type e =? POD_STRING) && (1 <=? e_size e) && (last_body_byte e =? 0)
             then Some (cstr (e_body e)) else None.
Proof. reflexivity. Qed.

(** ** C strings in an entry body *)
Lemma nul_idx_le_k : forall l k, (k < length l)%nat -> bv_unsigned (nth k l NUL) = 0 -> (nul_idx l <= k)%nat.
Proof.
  induction l as [|x l IH]; intros k Hk H; cbn [length] in Hk; [lia|]. cbn [nul_idx].
  destruct (Z.eqb_spec (bv_unsigned x) 0); [lia|]. destruct k as [|k]; [cbn [nth] in H; contradiction|].
  cbn [nth] in H. specialize (IH k ltac:(lia) H). lia.
Qed.

Lemma cstr_split : forall l, (nul_idx l < length l)%nat -> exists rest, l = cstr l ++ NUL :: rest.
Proof.
  induction l as [|x l IH]; intros H; cbn [length nul_idx] in H; [lia|]. unfold cstr. cbn [nul_idx].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
  - exists l. cbn [firstn app]. f_equal. apply bv_eq. rewrite E. reflexivity.
  - destruct (IH ltac:(lia)) as [rest Hr]. exists rest. cbn [firstn app]. f_equal. exact Hr.
Qed.

Lemma cstr_no_nul : forall l, ~ In (Z_to_bv 8 0) (cstr l).
Proof.
  induction l as [|x l IH]; unfold cstr; cbn [nul_idx]; [cbn; tauto|].
  destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; cbn [firstn In]; [tauto|].
  intros [H|H]; [subst x; apply E; reflexivity | exact (IH H)].
Qed.

Section Gen.
Variable segs : list Segment.

(** ** Reads of a run of bytes *)
Lemma bytes_at_sub : forall m a l k n, bytes_at segs m a l -> (k + n <= length l)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma read_le4 : forall m a l k v, bytes_at segs m a l -> (k + 4 <= length l)%nat ->
  firstn 4 (skipn k l) = le32 v -> 0 <= v < 2^64 ->
  ov_read_bytes segs m (wa (a + Z.of_nat k)) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m a l k v H Hk E Hv. rewrite (bytes_at_ov_read segs m a l k 4 H Hk). rewrite E. unfold le32.
  rewrite le4_lit by exact Hv. reflexivity.
Qed.

Lemma read_le8 : forall m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. pose proof (length_le8 v) as L.
  pose proof (bytes_at_ov_read segs m a (le8 v) 0 8 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. try (f_equal; cbn [skipn]; apply firstn_all2; lia).
Qed.

Lemma read_le4_cell : forall m a v, bytes_at segs m a (le4 v) -> ov_read_bytes segs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. pose proof (length_le4 v) as L.
  pose proof (bytes_at_ov_read segs m a (le4 v) 0 4 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. try (f_equal; cbn [skipn]; apply firstn_all2; lia).
Qed.

(** The fields of the record. *)
Lemma read_field : forall m pp r off v, bytes_at segs m pp (pp_bytes r) -> pod_rec_wf r ->
  firstn 4 (skipn (Z.to_nat off) (pp_bytes r)) = le32 v -> 0 <= off -> off + 4 <= PP_SIZE -> 0 <= v < 2^64 ->
  ov_read_bytes segs m (wa (pp + off)) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m pp r off v H Hw E H1 H2 Hv. pose proof (length_pp_bytes r Hw) as L.
  replace (pp + off) with (pp + Z.of_nat (Z.to_nat off)) by lia.
  apply (read_le4 m pp (pp_bytes r)); [exact H | lia | exact E | exact Hv].
Qed.

Lemma bytes_at_ent : forall m pp r i, bytes_at segs m pp (pp_bytes r) -> pod_rec_wf r -> (i < length (ents r))%nat ->
  bytes_at segs m (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) (ent_mem (nth i (ents r) (Ent 0 0 []))).
Proof.
  intros m pp r i H Hw Hi. pose proof (length_pp_bytes r Hw) as L. pose proof (proj1 (ents_wf r Hw)) as Hn.
  pose proof (bytes_at_sub m pp (pp_bytes r) (Z.to_nat (OFF_ENT + ENT_SIZE * Z.of_nat i)) 104 H) as X.
  rewrite (pp_ent r i Hw Hi) in X. rewrite Z2Nat.id in X by (unfold OFF_ENT, ENT_SIZE; lia).
  replace (pp + OFF_ENT + ENT_SIZE * Z.of_nat i) with (pp + (OFF_ENT + ENT_SIZE * Z.of_nat i)) by lia.
  apply X. unfold OFF_ENT, ENT_SIZE, PP_SIZE in *. lia.
Qed.

(** The fields of an entry: type, size, the body bytes. *)
Lemma ent_mem_split : forall e, ent_mem e = le32 (e_type e) ++ le32 (e_size e) ++ e_body e ++ zeros (96 - length (e_body e)).
Proof. reflexivity. Qed.

Lemma ent_type_read : forall m A e, bytes_at segs m A (ent_mem e) -> 0 <= e_type e < 2^32 ->
  ov_read_bytes segs m (wa A) 4 = Some (le4 (Z_to_bv 64 (e_type e))).
Proof.
  intros m A e H Ht. rewrite ent_mem_split in H. apply bytes_at_app in H as [H _].
  apply read_le4_cell. unfold le32 in H. rewrite le4_lit in H by lia. exact H.
Qed.

Lemma ent_size_read : forall m A e, bytes_at segs m A (ent_mem e) -> 0 <= e_size e < 2^32 ->
  ov_read_bytes segs m (wa (A + 4)) 4 = Some (le4 (Z_to_bv 64 (e_size e))).
Proof.
  intros m A e H Ht. rewrite ent_mem_split in H. apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [H _].
  rewrite length_le32 in H. apply read_le4_cell. unfold le32 in H. rewrite le4_lit in H by lia. exact H.
Qed.

Lemma bytes_at_ent_body : forall m A e, bytes_at segs m A (ent_mem e) ->
  bytes_at segs m (A + 8) (e_body e ++ zeros (96 - length (e_body e))).
Proof.
  intros m A e H. rewrite ent_mem_split in H. apply bytes_at_app in H as [_ H]. apply bytes_at_app in H as [_ H].
  rewrite !length_le32 in H. replace (A + Z.of_nat 4 + Z.of_nat 4) with (A + 8) in H by lia. exact H.
Qed.

Lemma ent_byte_read : forall m A e k, bytes_at segs m A (ent_mem e) -> (k < length (e_body e))%nat ->
  ov_read_bytes segs m (wa (A + 8 + Z.of_nat k)) 1 = Some [nth k (e_body e) NUL].
Proof.
  intros m A e k H Hk. apply bytes_at_ent_body in H.
  rewrite (bytes_at_ov_read segs m (A + 8) _ k 1 H) by (rewrite length_app; lia).
  f_equal. rewrite skipn_app. replace (k - length (e_body e))%nat with 0%nat by lia.
  rewrite (skipn_nth_cons (e_body e) k NUL Hk). reflexivity.
Qed.

Lemma ent_word_read : forall m A e, bytes_at segs m A (ent_mem e) -> (4 <= length (e_body e))%nat ->
  ov_read_bytes segs m (wa (A + 8)) 4 = Some (firstn 4 (e_body e)).
Proof.
  intros m A e H Hk. apply bytes_at_ent_body in H.
  pose proof (bytes_at_ov_read segs m (A + 8) _ 0 4 H ltac:(rewrite length_app; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. change (skipn 0 ?l) with l. rewrite firstn_app.
  replace (4 - length (e_body e))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed.

Lemma ent_key_bytes : forall m A e, bytes_at segs m A (ent_mem e) -> (nul_idx (e_body e) < length (e_body e))%nat ->
  bytes_at segs m (A + 8) (cstr (e_body e) ++ [Z_to_bv 8 0]).
Proof.
  intros m A e H Hn. apply bytes_at_ent_body in H. destruct (cstr_split (e_body e) Hn) as [rest Hr].
  rewrite Hr in H at 1. rewrite <- app_assoc in H. apply bytes_at_app in H as [H1 H2].
  apply bytes_at_app. split; [exact H1|]. cbn [app] in H2. change (NUL :: rest ++ _) with ([NUL] ++ rest ++ zeros (96 - length (e_body e))) in H2.
  apply bytes_at_app in H2 as [H2 _]. exact H2.
Qed.

(** The loaded int and float of a 4-byte body prefix. *)
Lemma sext_rd32 : forall l, length l = 4%nat ->
  sext 64 (bv_extract 0 32 (le_bytes_to_word l)) = Z_to_bv 64 (s32 (rd32 l)).
Proof.
  intros l Hl. rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word, rd32. rewrite firstn_all2 by lia. pose proof (le_bytes_bound l) as B.
  pose proof (le_bytes_nonneg l) as N. rewrite Hl in B. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in B.
  rewrite unsigned_lit by lia. change (Z.of_N 32) with 32. rewrite swrap32_s32 by lia. reflexivity.
Qed.

Lemma extract_rd32 : forall l, length l = 4%nat -> bv_extract 0 32 (le_bytes_to_word l) = Z_to_bv 32 (rd32 l).
Proof.
  intros l Hl. apply bv_eq. rewrite extract_low_mod by lia. unfold le_bytes_to_word, rd32.
  rewrite firstn_all2 by lia. pose proof (le_bytes_bound l) as B. pose proof (le_bytes_nonneg l) as N.
  rewrite Hl in B. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in B. rewrite unsigned_lit by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). reflexivity.
Qed.

Lemma rd32_firstn : forall l, rd32 (firstn 4 l) = rd32 l.
Proof. intros l. unfold rd32. rewrite firstn_firstn. reflexivity. Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells segs m A [CB n bs] -> bytes_at segs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

(** ** Stack cells *)
Lemma stk_wr_at : forall m lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at segs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma stk_store_ok : forall m lo hi a (n : nat), stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  store_ok segs m (wa a) n = true.
Proof.
  intros m lo hi a n H H1 H2. pose proof (stk_wr_at m lo hi a (Z.of_nat n) H H1 H2 ltac:(lia)) as W.
  pose proof (wr_at_store_ok segs m a (Z.of_nat n) 0 n W ltac:(lia) ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
Qed.

Lemma stk_read : forall m lo hi a (n : nat), stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, ov_read_bytes segs m (wa a) n = Some bs.
Proof.
  intros m lo hi a n H H1 H2. destruct (stk_bytes segs m lo hi H ltac:(lia)) as (bs & Hl & Hb).
  exists (firstn n (skipn (Z.to_nat (a - lo)) bs)).
  replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) at 1 by lia.
  apply bytes_at_ov_read; [exact Hb | lia].
Qed.

(** A run of bytes where the image has none is in the memory map itself. *)
Lemma bytes_at_some : forall m A bs x, bytes_at segs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> seg_rom segs (wa a) = None) ->
  A <= x < A + Z.of_nat (length bs) -> exists b, m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) HR Hx. specialize (H (Z.to_nat (x - A)) ltac:(lia)).
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in H by lia. unfold mrd in H.
  destruct (m (wa x)) as [b|] eqn:E; [exists b; reflexivity|]. rewrite (HR x Hx) in H.
  destruct (nth_error bs (Z.to_nat (x - A))) eqn:N; [discriminate|]. apply nth_error_None in N. lia.
Qed.

(** ** MemNorm.task_mem across a callee and a store *)
Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_gt_dec lo x); destruct (Z_lt_ge_dec x hi).
  - right. intros [H' _]. apply H'. lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Lemma wview_task : forall m x, MemNorm.task_mem segs m -> wview segs m x <> None ->
  find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m x T W. destruct (m x) as [b|] eqn:E.
  - exact (T x b E).
  - left. unfold wview in W. rewrite E in W.
    destruct (find_segment segs (bv_unsigned x) 1); [discriminate | exfalso; apply W; reflexivity].
Qed.

Lemma task_mem_munch : forall W m m', MemNorm.task_mem segs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview segs m x <> None) -> MemNorm.task_mem segs m'.
Proof.
  intros W m m' T MU H x b E. destruct (outside_dec W (bv_unsigned x)) as [O|O].
  - rewrite (MU x O) in E. exact (T x b E).
  - exact (wview_task m x T (H x O)).
Qed.

Lemma task_mem_write : forall m a bs, MemNorm.task_mem segs m -> store_ok segs m a (length bs) = true ->
  MemNorm.task_mem segs (write_to_mem m a bs).
Proof.
  intros m a bs T S x b E. destruct (write_to_mem_some _ _ _ _ _ E) as [E' | (i & Hi & ->)].
  - exact (T x b E').
  - exact (wview_task m _ T (store_ok_wview segs m a (length bs) i S Hi)).
Qed.

(** The stack region covers every address of a footprint inside it. *)
Lemma stk_wview : forall m lo hi W, stk segs m lo hi ->
  (forall x, ~ outside W x -> lo <= x < hi) -> forall x : word, ~ outside W (bv_unsigned x) -> wview segs m x <> None.
Proof.
  intros m lo hi W (H0 & H1 & H) HW x Hx. specialize (HW _ Hx). pose proof (proj1 (H (bv_unsigned x) HW)) as X.
  unfold wa in X. rewrite Z_to_bv_lit_self in X. exact X.
Qed.

End Gen.
