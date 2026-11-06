(** Facts for the walk of rb_ent_contract (U/Prog/HeadBuild/EntCut.v, UBSan image): the contract's premises
    packed as [ent_pre], its postcondition [QJ] for a given (e, r'), the memory [MemC] the walk carries (the
    footprint so far and e's 104 bytes at sp + 0xb8 as type word, size word, body), its transports across the
    turn's stores and calls, the reads of the input, of the five frame cells and of the image's tables and strings,
    the join at 0x13df0, and the statements of the case entries (the jump table's targets, 0x1386c for kind 9,
    0x13a20 for an empty input). No function of the binary is proved here. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut.
Import ListNotations.
Open Scope Z_scope.

(** ** Functions of one byte, checked on all 256 values *)
Lemma byte_check : forall (f g : Z -> Z), forallb (fun z => f z =? g z) (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> f x = g x.
Proof.
  intros f g H x Hx. rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.

Lemma byte_checkb : forall (f g : Z -> bool), forallb (fun z => Bool.eqb (f z) (g z)) (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> f x = g x.
Proof.
  intros f g H x Hx. rewrite forallb_forall in H. apply Bool.eqb_prop. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia | apply in_seq; lia].
Qed.

(** [byte_eq b] proves L = R (in Z or bool) where the byte b occurs only as [bv_unsigned b] (zxb unfolded). *)
Ltac byte_eq b :=
  cbv delta [zxb]; unfold bv_signed; rewrite ?Z_to_bv_unsigned; pose proof (byte_range b) as Hbr; revert Hbr;
  generalize (bv_unsigned b) as x; first [apply byte_check | apply byte_checkb]; vm_compute; reflexivity.

(** (int8) kind as the head computes it (0x13520 `slli a0,a0,0x38`; 0x13528 `srai s4,a0,0x38`): its sign is bit 7. *)
Lemma sext8_sign : forall b : byte,
  (bv_signed (Z_to_bv 64 (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b)) 56)) ≫ 56)) <? 0)
  = Z.testbit (bv_unsigned b) 7.
Proof. intros b. byte_eq b. Qed.

(** ** Words and byte lists *)
Lemma le4_le32 : forall v, le4 (Z_to_bv 64 v) = le32 v.
Proof.
  intros v. unfold le4, le32. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z_to_le_bytes_mod. cbn. lia.
Qed.

Lemma unsigned_lnot : forall x, 0 <= x < 2^64 -> bv_unsigned (Z_to_bv 64 (Z.lnot x)) = 2^64 - 1 - x.
Proof.
  intros x Hx. rewrite unsigned_lit_wrap. unfold Z.lnot.
  rewrite <- (Z.mod_add (Z.pred (- x)) 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma skipn_zeros : forall k n, skipn k (zeros n) = zeros (n - k).
Proof.
  induction k as [|k IH]; intros n; [rewrite Nat.sub_0_r; reflexivity|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn zeros repeat]. apply IH.
Qed.

(** bs written right after the prefix A of A ++ zeros k. *)
Lemma upd_app_zeros : forall (A bs : list byte) k, (length bs <= k)%nat ->
  upd_bytes (A ++ zeros k) (length A) bs = A ++ bs ++ zeros (k - length bs).
Proof.
  intros A bs k H. unfold upd_bytes. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
  f_equal. f_equal. rewrite skipn_app, skipn_all2 by lia. cbn [app].
  replace (length A + length bs - length A)%nat with (length bs) by lia. apply skipn_zeros.
Qed.

Lemma upd_zeros0 : forall (bs : list byte) k, (length bs <= k)%nat -> upd_bytes (zeros k) 0 bs = bs ++ zeros (k - length bs).
Proof. intros bs k H. exact (upd_app_zeros [] bs k H). Qed.

Lemma length_upd : forall cs k bs, (k + length bs <= length cs)%nat -> length (upd_bytes cs k bs) = length cs.
Proof. intros. apply upd_bytes_length. lia. Qed.

(** ** The contract's premises *)
Definition ent_pre (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z) : Prop :=
  0 < src /\ bytes_at rsegs m src r /\ src + Z.of_nat (length r) <= lo /\
  bytes_at rsegs m (bv_unsigned sp + 0) (le8 (Z_to_bv 64 0x15555556)) /\
  bytes_at rsegs m (bv_unsigned sp + 80) (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0x160)))) /\
  bytes_at rsegs m (bv_unsigned sp + 112) (le8 (Z_to_bv 64 pp)) /\
  bytes_at rsegs m (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
  bytes_at rsegs m (bv_unsigned sp + 128) (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0xc0)))) /\
  stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS) /\ lo + MID_STACK <= bv_unsigned sp /\ bv_unsigned sp mod 16 = 0 /\
  (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None) /\
  (forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) /\
  mem_inv rsegs m.

(** The bytes the turn may change: the callees' stack below sp, and e, parts, ch and t. *)
Definition WE (sp : word) : list (Z * Z) :=
  [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0xb8, bv_unsigned sp + FRAME_LOCALS)].

(** The contract's postcondition for the ent and the input left er (pp gives s7 and s8). *)
Definition QJ (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
    (src pp lo : Z) (er : ent * list byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1
                  a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat (length (snd er)))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4'
                  (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd er))))
                  s6' (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp)
                  (Z_to_bv 64 95)
                  (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length (snd er)))) (Z_to_bv 64 4) t3' t4' t5' t6')
             F (Z_to_bv 64 ENT_JOIN) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' (bv_unsigned sp + 0xb8) (ent_mem (fst er)) /\
    munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp); (bv_unsigned sp + 0xb8, bv_unsigned sp + FRAME_LOCALS)]
          m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + FRAME_LOCALS).

(** The memory the walk carries: the footprint so far, and e (sp + 0xb8) as its type word t, size word sz and
    96-byte body bd. *)
Definition MemC (sp : word) (m : word -> option byte) (lo : Z) (m1 : word -> option byte) (t sz : word)
    (bd : list byte) : Prop :=
  munch (WE sp) m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + FRAME_LOCALS) /\
  bytes_at rsegs m1 (bv_unsigned sp + 184) (le4 t ++ le4 sz ++ bd) /\ length bd = 96%nat.

(** ** General memory lemmas *)
Lemma stk_store_ok : forall m lo hi a (j : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok rsegs m (wa a) j = true.
Proof.
  intros m lo hi a j (H1 & H2 & H) Ha Hj.
  assert (W : wr_at rsegs m lo (hi - lo)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. }
  pose proof (wr_at_store_ok rsegs m lo (hi - lo) (a - lo) j W ltac:(lia) ltac:(lia)) as X.
  replace (lo + (a - lo)) with a in X by lia. exact X.
Qed.

Lemma stk_rw_cells : forall m lo hi A (n : nat), stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists junk, length junk = n /\ rw_cells rsegs m A [CB n junk].
Proof.
  intros m lo hi A n Hs H1 H2. pose proof Hs as (S1 & S2 & S).
  assert (Hs' : stk rsegs m A (A + Z.of_nat n)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply S. lia. }
  destruct (stk_bytes rsegs m A (A + Z.of_nat n) Hs' ltac:(lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (A + Z.of_nat n - A)) with n in Hlen by lia.
  exists bs. split; [exact Hlen|]. split.
  - split. { cbn. split; [lia | exact I]. }
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply S. lia.
Qed.

Lemma stk_bytes_at : forall m lo hi A (n : nat), stk rsegs m lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ bytes_at rsegs m A bs.
Proof.
  intros m lo hi A n Hs H1 H2. destruct (stk_rw_cells m lo hi A n Hs H1 H2) as (bs & L & C).
  exists bs. split; [exact L|]. destruct C as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma rw_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs /\ length bs = n.
Proof.
  intros m A n bs [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn in Hwf. destruct Hwf as [L _]. split; [exact Hb | exact L].
Qed.

Lemma bytes_at_munch_upd : forall m1 m2 c cs d (n : Z) bs,
  bytes_at rsegs m1 c cs -> munch [(d, d + n)] m1 m2 -> bytes_at rsegs m2 d bs -> Z.of_nat (length bs) = n ->
  c <= d -> d + n <= c + Z.of_nat (length cs) ->
  bytes_at rsegs m2 c (upd_bytes cs (Z.to_nat (d - c)) bs).
Proof.
  intros m1 m2 c cs d n bs (Hc0 & Hc1 & Hc) MU (Hd0 & Hd1 & Hd) Hn Hcd Hdn.
  unfold bytes_at. rewrite upd_bytes_length by lia. split; [lia|]. split; [lia|]. intros i Hi.
  rewrite upd_bytes_nth by lia.
  destruct (Nat.leb (Z.to_nat (d - c)) i && Nat.ltb i (Z.to_nat (d - c) + length bs))%bool eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    replace (c + Z.of_nat i) with (d + Z.of_nat (i - Z.to_nat (d - c))) by lia. apply Hd. lia.
  - unfold mrd. rewrite (MU (wa (c + Z.of_nat i))).
    + exact (Hc i Hi).
    + rewrite wa_unsigned by lia. cbn [outside]. split; [|exact I].
      apply andb_false_iff in E as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
Qed.

(** After a callee whose only writes are the n bytes at d, with those bytes present: the stack stays present. *)
Lemma stk_after_call : forall m1 m2 lo hi d (n : Z) bs,
  stk rsegs m1 lo hi -> munch [(d, d + n)] m1 m2 -> wmono rsegs m1 m2 -> bytes_at rsegs m2 d bs ->
  Z.of_nat (length bs) = n -> (forall a, lo <= a < hi -> seg_rom rsegs (wa a) = None) -> stk rsegs m2 lo hi.
Proof.
  intros m1 m2 lo hi d n bs Hs MU WM (B0 & B1 & B) Hn HR. pose proof Hs as (S1 & S2 & _).
  apply (stk_transport rsegs [(d, d + n)] m1 m2 lo hi Hs MU WM). intros x Hx.
  destruct (Z.le_gt_cases d x) as [H1|H1]; [destruct (Z.lt_ge_cases x (d + n)) as [H2|H2]|].
  - right. pose proof (B (Z.to_nat (x - d)) ltac:(lia)) as E. replace (d + Z.of_nat (Z.to_nat (x - d))) with x in E by lia.
    unfold mrd in E. rewrite (HR x Hx) in E. destruct (m2 (wa x)) as [b|]; [exists b; reflexivity|].
    destruct (nth_error bs (Z.to_nat (x - d))) eqn:N; [discriminate E|]. apply nth_error_None in N. lia.
  - left. cbn [outside]. split; [lia | exact I].
  - left. cbn [outside]. split; [lia | exact I].
Qed.

Lemma bytes_at_byte : forall m a bs j, bytes_at rsegs m a bs -> (j < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat j)) 1 = Some [nth j bs NUL].
Proof.
  intros m a bs j H Hj.
  rewrite (bytes_at_ov_read rsegs m a bs j 1 H) by lia.
  f_equal. clear H. revert j Hj. induction bs as [|x bs IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma bytes_at_read8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H L. pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. cbn [skipn]. f_equal. rewrite <- L. apply firstn_all.
Qed.

Lemma bytes_at_prefix : forall m a bs cs, bytes_at rsegs m a (bs ++ cs) -> bytes_at rsegs m a bs.
Proof. intros m a bs cs H. apply bytes_at_app in H. exact (proj1 H). Qed.

(** ** The image: rodata words, RELRO pointers, rodata strings, by computation *)
Definition ro4_ok (A : Z) (vs : list Z) : bool :=
  forallb (fun i => ro_bytes_b rsegs (A + 4 * Z.of_nat i) (le4 (Z_to_bv 64 (nth i vs 0)))) (seq 0 (length vs)).

Lemma ro4_read : forall m A vs i, mem_inv rsegs m -> ro4_ok A vs = true -> (i < length vs)%nat ->
  0 <= A -> A + 4 * Z.of_nat (length vs) <= 2^64 ->
  ov_read_bytes rsegs m (wa (A + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 (nth i vs 0))).
Proof.
  intros m A vs i MI H Hi H0 H1. unfold ro4_ok in H. rewrite forallb_forall in H.
  pose proof (H i ltac:(apply in_seq; lia)) as Hb.
  pose proof (ro_bytes_at rsegs m (A + 4 * Z.of_nat i) _ MI ltac:(lia) ltac:(rewrite length_le4; lia)
                (ro_bytes_b_sound rsegs _ _ Hb)) as B.
  rewrite <- (Z.add_0_r (A + 4 * Z.of_nat i)). change 0 with (Z.of_nat 0).
  rewrite (bytes_at_ov_read rsegs m _ _ 0 4 B) by (rewrite length_le4; lia).
  cbn [skipn]. f_equal.
Qed.

Definition le8s (ps : list Z) : list byte := flat_map (fun p => le8 (Z_to_bv 64 p)) ps.

Definition relro8_ok (A : Z) (ps : list Z) : bool :=
  forallb (fun k => match seg_rom rsegs (wa (A + Z.of_nat k)), nth_error (le8s ps) k with
                    | Some x, Some y => bv_eqb x y
                    | _, _ => false
                    end) (seq 0 (length (le8s ps))).

Lemma length_le8s : forall ps, length (le8s ps) = (8 * length ps)%nat.
Proof. induction ps as [|p ps IH]; [reflexivity|]. cbn [le8s flat_map length]. rewrite length_app, length_le8. fold (le8s ps). lia. Qed.

Lemma le8s_nth : forall ps i, (i < length ps)%nat ->
  firstn 8 (skipn (8 * i) (le8s ps)) = le8 (Z_to_bv 64 (nth i ps 0)).
Proof.
  induction ps as [|p ps IH]; intros i Hi; cbn [length] in Hi; [lia|].
  cbn [le8s flat_map]. fold (le8s ps). destruct i as [|i].
  - rewrite Nat.mul_0_r. change (skipn 0 ?l) with l. cbn [nth]. rewrite firstn_app, length_le8, firstn_all2 by (rewrite length_le8; lia).
    cbn [Nat.sub firstn]. apply app_nil_r.
  - replace (8 * S i)%nat with (length (le8 (Z_to_bv 64 p)) + 8 * i)%nat by (rewrite length_le8; lia).
    rewrite skipn_app_len. cbn [nth]. apply IH. lia.
Qed.

(** A table of 8-byte pointers at A, read through memory whose bytes there are the image's. *)
Lemma relro8_read : forall m A ps i, relro8_ok A ps = true -> (i < length ps)%nat -> 0 <= A ->
  A + 8 * Z.of_nat (length ps) <= 2^64 ->
  (forall a, A <= a < A + 8 * Z.of_nat (length ps) -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  ov_read_bytes rsegs m (wa (A + 8 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 (nth i ps 0))).
Proof.
  intros m A ps i H Hi H0 H1 HM.
  assert (B : bytes_at rsegs m A (le8s ps)).
  { split; [lia|]. split; [rewrite length_le8s; lia|]. intros k Hk. rewrite length_le8s in Hk.
    rewrite HM by lia. unfold relro8_ok in H. rewrite forallb_forall in H.
    pose proof (H k ltac:(apply in_seq; rewrite length_le8s; lia)) as Hc.
    destruct (seg_rom rsegs (wa (A + Z.of_nat k))) as [x|]; [|discriminate].
    destruct (nth_error (le8s ps) k) as [y|] eqn:Ny; [|discriminate].
    unfold bv_eqb in Hc. apply Z.eqb_eq in Hc. apply bv_eq in Hc. subst. reflexivity. }
  replace (A + 8 * Z.of_nat i) with (A + Z.of_nat (8 * i)) by lia.
  rewrite (bytes_at_ov_read rsegs m A _ (8 * i) 8 B) by (rewrite length_le8s; lia).
  rewrite le8s_nth by exact Hi. reflexivity.
Qed.

(** A C string s at p in .rodata, with the bytes after its NUL up to the next 8-byte boundary (strlen's slack). *)
Definition slack_n (p : Z) (s : list byte) : nat := Z.to_nat ((- (p + Z.of_nat (length s) + 1)) mod 8).
Definition img_slack (p : Z) (s : list byte) : list byte :=
  match image_bytes rsegs (p + Z.of_nat (length s) + 1) (slack_n p s) with Some l => l | None => [] end.
Definition rostr_ok (p : Z) (s : list byte) : bool :=
  no_nul s && ro_bytes_b rsegs p (s ++ NUL :: img_slack p s) && Nat.eqb (length (img_slack p s)) (slack_n p s) &&
  (0 <=? p) && (p + 128 <=? 2^64) && (length s <? 64)%nat.

Lemma no_nul_not_in : forall l, no_nul l = true -> ~ In NUL l.
Proof.
  induction l as [|x l IH]; intros H Hin; [exact Hin|]. cbn in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [E|Hin]; [subst x; vm_compute in H1; discriminate H1 | exact (IH H2 Hin)].
Qed.

Lemma rostr_bytes : forall m p s, mem_inv rsegs m -> rostr_ok p s = true ->
  bytes_at rsegs m p (s ++ NUL :: img_slack p s) /\ ~ In (Z_to_bv 8 0) s /\
  (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length (img_slack p s)) /\
  0 <= p /\ p + 128 <= 2^64 /\ (length s < 64)%nat.
Proof.
  intros m p s MI H. unfold rostr_ok in H. repeat rewrite andb_true_iff in H.
  destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6).
  apply Nat.eqb_eq in H3. apply Z.leb_le in H4. apply Z.leb_le in H5. apply Nat.ltb_lt in H6.
  assert (Hsl : Z.of_nat (length (img_slack p s)) = (- (p + Z.of_nat (length s) + 1)) mod 8).
  { rewrite H3. unfold slack_n. rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia. }
  pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as Hm.
  split.
  - apply ro_bytes_at; [exact MI | lia | | exact (ro_bytes_b_sound rsegs _ _ H2)].
    rewrite length_app. cbn [length]. lia.
  - split; [exact (no_nul_not_in s H1)|]. split; [lia|]. lia.
Qed.

(** Every byte of the builder's .data.rel.ro tables is in the image. *)
Lemma relro_present : forallb (fun k => match seg_rom rsegs (wa (RELRO_TBL + Z.of_nat k)) with Some _ => true | None => false end)
  (seq 0 (Z.to_nat (RELRO_TBL_END - RELRO_TBL))) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma relro_rom : forall a, RELRO_TBL <= a < RELRO_TBL_END -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha. pose proof relro_present as H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - RELRO_TBL))). replace (RELRO_TBL + Z.of_nat (Z.to_nat (a - RELRO_TBL))) with a in H by lia.
  destruct (seg_rom rsegs (wa a)); [discriminate|]. exfalso. assert (X : false = true) by (apply H; apply in_seq;
    unfold RELRO_TBL, RELRO_TBL_END in *; lia). discriminate X.
Qed.

(** The callees' stack below sp the contract allows (U/Prog/LLVMFuzzerTestOneInput_c.v: the parse chain's). *)
Lemma mid_stack_512 : MID_STACK = 512.
Proof. reflexivity. Qed.

(** ** The walk's frame *)
Section Frame.
Variables (sp : word) (m : word -> option byte) (r : list byte) (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Lemma ep_range : 0 < src /\ src + Z.of_nat (length r) <= lo /\ 0 <= lo /\ lo + 512 <= bv_unsigned sp /\
  bv_unsigned sp + 0x1d8 <= 2^64 /\ bv_unsigned sp mod 16 = 0.
Proof.
  destruct HE as (A & _ & B & _ & _ & _ & _ & _ & ST & C & D & _). pose proof ST as (E & G & _).
  pose proof mid_stack_512. unfold FRAME_LOCALS in *. lia.
Qed.

Lemma ep_stk : stk rsegs m lo (bv_unsigned sp + FRAME_LOCALS).
Proof. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ep_rom : forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None.
Proof. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ep_mem_inv : mem_inv rsegs m.
Proof. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

(** e's 104 bytes are writable cells at 0x134bc (memset's destination). *)
Lemma ep_e_cells : exists junk, length junk = 104%nat /\ rw_cells rsegs m (bv_unsigned sp + 184) [CB 104 junk].
Proof.
  pose proof ep_range as R. apply (stk_rw_cells m lo (bv_unsigned sp + FRAME_LOCALS)); [exact ep_stk | |];
    unfold FRAME_LOCALS; lia.
Qed.

(** A byte outside the footprint keeps its value. *)
Lemma MemC_out : forall m1 t sz bd a, MemC sp m lo m1 t sz bd -> 0 <= a < 2^64 ->
  ~ (bv_unsigned sp - MID_STACK <= a < bv_unsigned sp) -> ~ (bv_unsigned sp + 0xb8 <= a < bv_unsigned sp + FRAME_LOCALS) ->
  mrd rsegs m1 (wa a) = mrd rsegs m (wa a).
Proof.
  intros m1 t sz bd a (MU & _) Ha H1 H2. unfold mrd. rewrite (MU (wa a)); [reflexivity|].
  rewrite wa_unsigned by lia. cbn [outside WE]. unfold WE. cbn [outside]. tauto.
Qed.

Lemma MemC_bytes_out : forall m1 t sz bd A bs, MemC sp m lo m1 t sz bd -> bytes_at rsegs m A bs ->
  disjoint_from (WE sp) A (Z.of_nat (length bs)) -> bytes_at rsegs m1 A bs.
Proof. intros m1 t sz bd A bs (MU & _) B D. exact (bytes_at_transport rsegs _ _ _ _ _ B MU D). Qed.

Lemma MemC_in : forall m1 t sz bd, MemC sp m lo m1 t sz bd -> bytes_at rsegs m1 src r.
Proof.
  intros m1 t sz bd MC. pose proof ep_range as R. destruct HE as (_ & HR & _).
  apply (MemC_bytes_out m1 t sz bd); [exact MC | exact HR |].
  unfold WE, FRAME_LOCALS. pose proof mid_stack_512. cbn [disjoint_from]. lia.
Qed.

(** Byte j of the input. *)
Lemma MemC_in_byte : forall m1 t sz bd (j : nat), MemC sp m lo m1 t sz bd -> (j < length r)%nat ->
  ov_read_bytes rsegs m1 (wa (src + Z.of_nat j)) 1 = Some [nth j r NUL].
Proof. intros m1 t sz bd j MC Hj. apply bytes_at_byte; [exact (MemC_in m1 t sz bd MC) | exact Hj]. Qed.

Lemma MemC_in_byte0 : forall m1 t sz bd, MemC sp m lo m1 t sz bd -> (0 < length r)%nat ->
  ov_read_bytes rsegs m1 (wa src) 1 = Some [nth 0 r NUL].
Proof. intros m1 t sz bd MC Hj. rewrite <- (Z.add_0_r src) at 1. exact (MemC_in_byte m1 t sz bd 0 MC Hj). Qed.

(** The five frame cells. *)
Local Ltac cell_out MC H :=
  apply bytes_at_read8; [|apply length_le8];
  apply (MemC_bytes_out _ _ _ _ _ _ MC H); rewrite length_le8;
  pose proof ep_range; pose proof mid_stack_512; unfold WE, FRAME_LOCALS; cbn [disjoint_from]; lia.

(** The cell at sp itself (`ld a1,0(sp)`): the load reads at the word sp. *)
Lemma MemC_c0 : forall m1 t sz bd, MemC sp m lo m1 t sz bd ->
  ov_read_bytes rsegs m1 sp 8 = Some (le8 (Z_to_bv 64 0x15555556)).
Proof.
  intros m1 t sz bd MC. destruct HE as (_ & _ & _ & H & _).
  rewrite <- (Z_to_bv_bv_unsigned sp), <- (Z.add_0_r (bv_unsigned sp)). cell_out MC H.
Qed.

Lemma MemC_c50 : forall m1 t sz bd, MemC sp m lo m1 t sz bd ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 80)) 8 = Some (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0x160)))).
Proof. intros m1 t sz bd MC. destruct HE as (_ & _ & _ & _ & H & _). cell_out MC H. Qed.

Lemma MemC_c70 : forall m1 t sz bd, MemC sp m lo m1 t sz bd ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 112)) 8 = Some (le8 (Z_to_bv 64 pp)).
Proof. intros m1 t sz bd MC. destruct HE as (_ & _ & _ & _ & _ & H & _). cell_out MC H. Qed.

Lemma MemC_c78 : forall m1 t sz bd, MemC sp m lo m1 t sz bd ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 120)) 8 = Some (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))).
Proof. intros m1 t sz bd MC. destruct HE as (_ & _ & _ & _ & _ & _ & H & _). cell_out MC H. Qed.

Lemma MemC_c80 : forall m1 t sz bd, MemC sp m lo m1 t sz bd ->
  ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 128)) 8 = Some (le8 (Z_to_bv 64 (Z.lnot (bv_unsigned sp + 0xc0)))).
Proof. intros m1 t sz bd MC. destruct HE as (_ & _ & _ & _ & _ & _ & _ & H & _). cell_out MC H. Qed.

(** The .data.rel.ro tables read as in the image. *)
Lemma MemC_relro : forall m1 t sz bd a, MemC sp m lo m1 t sz bd -> RELRO_TBL <= a < RELRO_TBL_END ->
  mrd rsegs m1 (wa a) = seg_rom rsegs (wa a).
Proof.
  intros m1 t sz bd a MC Ha. pose proof ep_range as R. pose proof (relro_rom a Ha) as Hr.
  assert (N : ~ (lo <= a < bv_unsigned sp + FRAME_LOCALS)) by (intros X; exact (Hr (ep_rom a X))).
  rewrite (MemC_out m1 t sz bd a MC) by (pose proof mid_stack_512; unfold RELRO_TBL, RELRO_TBL_END, FRAME_LOCALS in *; lia).
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREL & _). exact (HREL a Ha).
Qed.

Lemma MemC_mem_inv : forall m1 t sz bd, MemC sp m lo m1 t sz bd -> mem_inv rsegs m1.
Proof. intros m1 t sz bd (_ & _ & H & _). exact H. Qed.

Lemma MemC_stk : forall m1 t sz bd, MemC sp m lo m1 t sz bd -> stk rsegs m1 lo (bv_unsigned sp + FRAME_LOCALS).
Proof. intros m1 t sz bd (_ & _ & _ & H & _). exact H. Qed.

Lemma MemC_e : forall m1 t sz bd, MemC sp m lo m1 t sz bd -> bytes_at rsegs m1 (bv_unsigned sp + 184) (le4 t ++ le4 sz ++ bd).
Proof. intros m1 t sz bd (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma MemC_len : forall m1 t sz bd, MemC sp m lo m1 t sz bd -> length bd = 96%nat.
Proof. intros m1 t sz bd (_ & _ & _ & _ & _ & H). exact H. Qed.

Lemma MemC_ext : forall m1 t sz bd t' sz' bd', MemC sp m lo m1 t sz bd -> t = t' -> sz = sz' -> bd = bd' ->
  MemC sp m lo m1 t' sz' bd'.
Proof. intros; subst; assumption. Qed.

(** A store needs store_ok at its bytes: any n bytes of the frame's locals and e. *)
Lemma MemC_store_ok : forall m1 t sz bd a (n : nat), MemC sp m lo m1 t sz bd ->
  bv_unsigned sp + 0xb8 <= a -> a + Z.of_nat n <= bv_unsigned sp + FRAME_LOCALS -> store_ok rsegs m1 (wa a) n = true.
Proof.
  intros m1 t sz bd a n MC H1 H2. pose proof ep_range as R.
  apply (stk_store_ok m1 lo (bv_unsigned sp + FRAME_LOCALS)); [exact (MemC_stk _ _ _ _ MC) | lia | lia].
Qed.

(** n writable bytes at a in the frame's locals (a callee's destination), and n present bytes (strlen's slack). *)
Lemma MemC_cells : forall m1 t sz bd a (n : nat), MemC sp m lo m1 t sz bd ->
  bv_unsigned sp + 0xb8 <= a -> a + Z.of_nat n <= bv_unsigned sp + FRAME_LOCALS ->
  exists junk, length junk = n /\ rw_cells rsegs m1 a [CB n junk].
Proof.
  intros m1 t sz bd a n MC H1 H2. pose proof ep_range as R.
  apply (stk_rw_cells m1 lo (bv_unsigned sp + FRAME_LOCALS) a n (MemC_stk _ _ _ _ MC)); lia.
Qed.

Lemma MemC_any_bytes : forall m1 t sz bd a (n : nat), MemC sp m lo m1 t sz bd ->
  bv_unsigned sp + 0xb8 <= a -> a + Z.of_nat n <= bv_unsigned sp + FRAME_LOCALS ->
  exists bs, length bs = n /\ bytes_at rsegs m1 a bs.
Proof.
  intros m1 t sz bd a n MC H1 H2. pose proof ep_range as R.
  apply (stk_bytes_at m1 lo (bv_unsigned sp + FRAME_LOCALS) a n (MemC_stk _ _ _ _ MC)); lia.
Qed.

(** e's bytes after a store of bs at offset k of e. *)
Lemma e_upd_t : forall t sz bd v, upd_bytes (le4 t ++ le4 sz ++ bd) 0 (le4 v) = le4 v ++ le4 sz ++ bd.
Proof. intros t sz bd v. reflexivity. Qed.

Lemma e_upd_sz : forall t sz bd v, upd_bytes (le4 t ++ le4 sz ++ bd) 4 (le4 v) = le4 t ++ le4 v ++ bd.
Proof. intros t sz bd v. reflexivity. Qed.

Lemma e_upd_bd : forall t sz bd k bs, upd_bytes (le4 t ++ le4 sz ++ bd) (8 + k) bs = le4 t ++ le4 sz ++ upd_bytes bd k bs.
Proof. intros t sz bd k bs. reflexivity. Qed.

(** A store into e (offset k). *)
Lemma MemC_store_gen : forall m1 t sz bd k bs, MemC sp m lo m1 t sz bd -> (k + length bs <= 104)%nat ->
  munch (WE sp) m (write_to_mem m1 (wa (bv_unsigned sp + 184 + Z.of_nat k)) bs) /\
  wmono rsegs m (write_to_mem m1 (wa (bv_unsigned sp + 184 + Z.of_nat k)) bs) /\
  mem_inv rsegs (write_to_mem m1 (wa (bv_unsigned sp + 184 + Z.of_nat k)) bs) /\
  stk rsegs (write_to_mem m1 (wa (bv_unsigned sp + 184 + Z.of_nat k)) bs) lo (bv_unsigned sp + FRAME_LOCALS) /\
  bytes_at rsegs (write_to_mem m1 (wa (bv_unsigned sp + 184 + Z.of_nat k)) bs) (bv_unsigned sp + 184)
    (upd_bytes (le4 t ++ le4 sz ++ bd) k bs).
Proof.
  intros m1 t sz bd k bs (MU & WM & MI & ST & EB & L) Hk. pose proof ep_range as R.
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + 184 + Z.of_nat k)) (length bs) = true)
    by (apply (stk_store_ok m1 lo (bv_unsigned sp + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  split. { apply munch_write; [exact MU | lia | unfold FRAME_LOCALS in *; lia |]. unfold WE, FRAME_LOCALS. cbn [inside]. lia. }
  split; [apply wmono_write; exact WM|]. split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | lia | unfold FRAME_LOCALS in *; lia]|].
  pose proof (bytes_at_write_inside rsegs m1 _ _ (Z.of_nat k) bs EB ltac:(lia)
    ltac:(rewrite Nat2Z.id, length_app, length_app, !length_le4; lia)) as X.
  rewrite Nat2Z.id in X. exact X.
Qed.

Lemma MemC_st_t : forall m1 t sz bd v, MemC sp m lo m1 t sz bd ->
  MemC sp m lo (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 184)) (le4 v)) v sz bd.
Proof.
  intros m1 t sz bd v MC. pose proof (MemC_len _ _ _ _ MC) as L.
  destruct (MemC_store_gen m1 t sz bd 0 (le4 v) MC ltac:(rewrite length_le4; lia)) as (A & B & C & D & E).
  rewrite Z.add_0_r in A, B, C, D, E. rewrite e_upd_t in E. unfold wa in *.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E | exact L].
Qed.

Lemma MemC_st_sz : forall m1 t sz bd v, MemC sp m lo m1 t sz bd ->
  MemC sp m lo (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 188)) (le4 v)) t v bd.
Proof.
  intros m1 t sz bd v MC. pose proof (MemC_len _ _ _ _ MC) as L.
  destruct (MemC_store_gen m1 t sz bd 4 (le4 v) MC ltac:(rewrite length_le4; lia)) as (A & B & C & D & E).
  replace (bv_unsigned sp + 184 + Z.of_nat 4) with (bv_unsigned sp + 188) in A, B, C, D, E by lia.
  rewrite e_upd_sz in E. unfold wa in *.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E | exact L].
Qed.

(** A store of bs at body offset k (address sp + 0xc0 + k). *)
Lemma MemC_st_bd : forall m1 t sz bd a k bs, MemC sp m lo m1 t sz bd -> a = bv_unsigned sp + 192 + Z.of_nat k ->
  (k + length bs <= 96)%nat ->
  MemC sp m lo (write_to_mem m1 (Z_to_bv 64 a) bs) t sz (upd_bytes bd k bs).
Proof.
  intros m1 t sz bd a k bs MC -> Hk. pose proof (MemC_len _ _ _ _ MC) as L.
  destruct (MemC_store_gen m1 t sz bd (8 + k) bs MC ltac:(lia)) as (A & B & C & D & E).
  replace (bv_unsigned sp + 184 + Z.of_nat (8 + k)) with (bv_unsigned sp + 192 + Z.of_nat k) in A, B, C, D, E by lia.
  rewrite e_upd_bd in E. unfold wa in *.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|].
  rewrite length_upd; lia.
Qed.

(** A store of bs at a in [sp + 0x140, sp + 0x1d8) (r, parts, ch, t): e unchanged. *)
Lemma MemC_st_hi : forall m1 t sz bd a bs, MemC sp m lo m1 t sz bd ->
  bv_unsigned sp + 0x140 <= a -> a + Z.of_nat (length bs) <= bv_unsigned sp + FRAME_LOCALS ->
  MemC sp m lo (write_to_mem m1 (Z_to_bv 64 a) bs) t sz bd.
Proof.
  intros m1 t sz bd a bs (MU & WM & MI & ST & EB & L) H1 H2. pose proof ep_range as R. unfold FRAME_LOCALS in *.
  assert (HS : store_ok rsegs m1 (wa a) (length bs) = true)
    by (apply (stk_store_ok m1 lo (bv_unsigned sp + FRAME_LOCALS)); [exact ST | lia | unfold FRAME_LOCALS; lia]).
  change (Z_to_bv 64 a) with (wa a).
  split. { apply munch_write; [exact MU | lia | lia |]. unfold WE, FRAME_LOCALS. cbn [inside]. lia. }
  split; [apply wmono_write; exact WM|]. split; [apply mem_inv_store; [exact MI | exact HS]|].
  split; [apply stk_write; [exact ST | lia | lia]|].
  split; [|exact L]. apply bytes_at_write_other; [exact EB | lia | lia |].
  rewrite !length_app, !length_le4, L. lia.
Qed.

(** A callee that writes n bytes bs at d. *)
Lemma MemC_call_gen : forall m1 m2 t sz bd d (n : Z) bs, MemC sp m lo m1 t sz bd ->
  munch [(d, d + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 d bs ->
  Z.of_nat (length bs) = n -> bv_unsigned sp + 0xb8 <= d -> d + n <= bv_unsigned sp + FRAME_LOCALS ->
  munch (WE sp) m m2 /\ wmono rsegs m m2 /\ mem_inv rsegs m2 /\ stk rsegs m2 lo (bv_unsigned sp + FRAME_LOCALS).
Proof.
  intros m1 m2 t sz bd d n bs (MU & WM & MI & ST & EB & L) MU2 WM2 MI2 B2 Hn H1 H2. pose proof ep_range as R.
  split.
  { apply (munch_trans _ m m1 m2 MU). apply (munch_weaken [(d, d + n)] _ m1 m2); [|exact MU2].
    unfold sub_fp, WE. cbn [outside]. unfold FRAME_LOCALS in *. intros x (O1 & O2 & _). split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact MI2|].
  apply (stk_after_call m1 m2 lo _ d n bs ST MU2 WM2 B2 Hn). exact ep_rom.
Qed.

Lemma MemC_call_bd : forall m1 m2 t sz bd d k bs, MemC sp m lo m1 t sz bd ->
  munch [(d, d + Z.of_nat (length bs))] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 d bs ->
  d = bv_unsigned sp + 192 + Z.of_nat k -> (k + length bs <= 96)%nat ->
  MemC sp m lo m2 t sz (upd_bytes bd k bs).
Proof.
  intros m1 m2 t sz bd d k bs MC MU2 WM2 MI2 B2 -> Hk. pose proof ep_range as R. pose proof MC as (_ & _ & _ & _ & EB & L).
  destruct (MemC_call_gen m1 m2 t sz bd _ _ bs MC MU2 WM2 MI2 B2 eq_refl ltac:(lia) ltac:(unfold FRAME_LOCALS; lia))
    as (A & B & C & D).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [|rewrite length_upd; lia].
  pose proof (bytes_at_munch_upd m1 m2 _ _ _ _ bs EB MU2 B2 eq_refl ltac:(lia)
    ltac:(rewrite !length_app, !length_le4; lia)) as X.
  replace (Z.to_nat (bv_unsigned sp + 192 + Z.of_nat k - (bv_unsigned sp + 184))) with (8 + k)%nat in X by lia.
  rewrite e_upd_bd in X. exact X.
Qed.

Lemma MemC_call_hi : forall m1 m2 t sz bd d (n : Z) bs, MemC sp m lo m1 t sz bd ->
  munch [(d, d + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> bytes_at rsegs m2 d bs ->
  Z.of_nat (length bs) = n -> bv_unsigned sp + 0x140 <= d -> d + n <= bv_unsigned sp + FRAME_LOCALS ->
  MemC sp m lo m2 t sz bd.
Proof.
  intros m1 m2 t sz bd d n bs MC MU2 WM2 MI2 B2 Hn H1 H2. pose proof ep_range as R. pose proof MC as (_ & _ & _ & _ & EB & L).
  destruct (MemC_call_gen m1 m2 t sz bd d n bs MC MU2 WM2 MI2 B2 Hn ltac:(lia) H2) as (A & B & C & D).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [|exact L].
  apply (bytes_at_transport rsegs _ m1 m2 _ _ EB MU2). cbn [disjoint_from]. rewrite !length_app, !length_le4, L.
  split; [lia | exact I].
Qed.

(** A callee that writes nothing (strlen). *)
Lemma MemC_call_nil : forall m1 m2 t sz bd, MemC sp m lo m1 t sz bd ->
  munch [] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> MemC sp m lo m2 t sz bd.
Proof.
  intros m1 m2 t sz bd (MU & WM & MI & ST & EB & L) MU2 WM2 MI2.
  split; [apply (munch_trans _ m m1 m2 MU); exact (munch_weaken [] _ m1 m2 (fun x _ => I) MU2)|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM2)|]. split; [exact MI2|].
  split; [exact (stk_transport_disjoint rsegs _ _ _ _ _ ST MU2 WM2 I)|].
  split; [exact (bytes_at_transport rsegs _ _ _ _ _ EB MU2 I) | exact L].
Qed.

End Frame.


(** ** Walk tactics *)
(** Branch conditions over words of the form Z_to_bv 64 z, decided by lia from the context. *)
Ltac unlit := repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 (Z.lnot ?z))] => rewrite (unsigned_lnot z) by lia
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
  end.
Ltac solve_cz := unfold_cond; fold_lit_ux; unlit; solve_cond_rec.
Ltac brf := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry; solve_cz]
  end.
Ltac brt := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with true; [cbv iota | symmetry; solve_cz]
  end.

(** Name the memory of the goal (after a store or a call). *)
Ltac name_mem :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      tryif is_var mm then idtac else (let m2 := fresh "m" in set (m2 := mm) in *; clearbody m2)
  end.

(** A store step into e (type word at sp + 0xb8, size word at sp + 0xbc, body at sp + 0xc0 + k), MemC carried. *)
Ltac est_t HE MC :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + 184)) 4 = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 184)) (le4 ?v)) _) =>
      let MC2 := fresh "MC" in
      pose proof (MemC_st_t _ _ _ _ _ _ HE m1 t sz bd v MC) as MC2; clear MC; rename MC2 into MC; name_mem
    end
  end.

Ltac est_sz HE MC :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + 188)) 4 = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + 188)) (le4 ?v)) _) =>
      let MC2 := fresh "MC" in
      pose proof (MemC_st_sz _ _ _ _ _ _ HE m1 t sz bd v MC) as MC2; clear MC; rename MC2 into MC; name_mem
    end
  end.

(** A store of n bytes at address a (a Z expression) into e's body at offset k. *)
Ltac est_bd HE MC a k n :=
  lazymatch type of MC with MemC ?sp ?m ?lo ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa a) n = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    unlit; step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 ?a') ?bs) _) =>
      let MC2 := fresh "MC" in
      pose proof (MemC_st_bd _ _ _ _ _ _ HE m1 t sz bd a' k bs MC ltac:(unlit; lia)
                    ltac:(rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length]; lia)) as MC2;
      clear MC; rename MC2 into MC; name_mem
    end
  end.

(** ent_build r for r = b :: .. with b mod 10 = k. *)
Ltac eb_tac Er Hk := rewrite Er; unfold ent_build; cbn [fuzz_u8]; rewrite Hk; reflexivity.

(** e right after memset(e, 0, 104). *)
Lemma zeros104 : zeros 104 = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ zeros 96.
Proof. vm_compute. reflexivity. Qed.

(** ** The join at 0x13df0 and the case entries *)
Section Join.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s1 F fc m r src pp lo (ent_build r)).

Lemma join_13df0 : forall (ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 : word) m1 e r' t sz bd,
  ent_build r = (e, r') ->
  s2 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s10 = s5 ->
  MemC sp m lo m1 t sz bd -> le4 t = le32 (e_type e) -> le4 sz = le32 (e_size e) ->
  bd = e_body e ++ zeros (96 - length (e_body e)) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
             (Z_to_bv 64 (0xcccccccd * 2^32)) s4 s5 s6 (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) (Z_to_bv 64 95)
             s10 (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 ENT_JOIN) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s10 t3 t4 t5 t6 m1 e r' t sz bd Eb -> -> ->
    (MU & WM & MI & ST & EB & L) Et Esz Ebd.
  apply evt_done. unfold QJ. rewrite Eb. cbn [fst snd].
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, s4, s6, t3, t4, t5, t6, m1.
  split; [reflexivity|]. split.
  - unfold ent_mem. rewrite <- Et, <- Esz, <- Ebd. exact EB.
  - split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** The registers at a target of the jump table (kinds 0-8: kind = b, kind % 10 = k), after memset(e) and the
    kind read: s2 = |r|, s5 = src + 1, s6 = |r| - 1, s10 = src, s4 = (int8) kind (its sign is bit 7 of kind), e
    zero; the constants of the head unchanged. *)
Definition case_at (k pc : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (b : byte) (rest : list byte) m1,
    r = b :: rest -> bv_unsigned b mod 10 = k ->
    (bv_signed s4 <? 0) = Z.testbit (bv_unsigned b) 7 ->
    MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
    evt rsegs QE
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4 (Z_to_bv 64 (src + 1))
               (Z_to_bv 64 (Z.of_nat (length r) + -1)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp)
               (Z_to_bv 64 95) (Z_to_bv 64 src) (Z_to_bv 64 4) t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

(** Kind 9 (0x1386c, taken by `bltu a2,a1` before the jump). *)
Definition case9_at : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) (b : byte) (rest : list byte) m1,
    r = b :: rest -> bv_unsigned b mod 10 = 9 ->
    MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
    evt rsegs QE
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4 (Z_to_bv 64 (src + 1))
               (Z_to_bv 64 (Z.of_nat (length r) + -1)) (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp)
               (Z_to_bv 64 95) (Z_to_bv 64 src) (Z_to_bv 64 4) t3 t4 t5 t6)
          F (Z_to_bv 64 0x1386c) fc None m1 (seg_rom rsegs)).

(** The input empty (0x134cc `beqz s2` taken to 0x13a20): kind 0 read from nothing, the head-amp key of c = p = 0. *)
Definition case0_nil_at : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word) m1,
    r = [] ->
    MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
    evt rsegs QE
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length r))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4 (Z_to_bv 64 src) s6
               (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp)
               (Z_to_bv 64 95) (Z_to_bv 64 src) (Z_to_bv 64 4) t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a20) fc None m1 (seg_rom rsegs)).

End Join.
