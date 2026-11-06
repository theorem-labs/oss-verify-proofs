From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem LibcNeeds_c has_prefixed_c readings_scan_c.
Import ListNotations.
Open Scope Z_scope.

Lemma cw_le : forall f (l : list Z), (count_while f l <= length l)%nat.
Proof. intros f l; induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma byte_at_skipn : forall (t : list Z) p, (p < length t)%nat -> skipn p t = byte_at t p :: skipn (S p) t.
Proof.
  unfold byte_at. induction t as [|x t IH]; intros p Hp; cbn in Hp; [lia|].
  destruct p as [|p]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma cw_step : forall f (t : list Z) p, (p < length t)%nat ->
  count_while f (skipn p t) = if f (byte_at t p) then S (count_while f (skipn (S p) t)) else O.
Proof. intros f t p Hp. rewrite (byte_at_skipn t p Hp). reflexivity. Qed.

Lemma cw_end : forall f (t : list Z) p, (length t <= p)%nat -> count_while f (skipn p t) = O.
Proof. intros. rewrite skipn_all2 by lia. reflexivity. Qed.

Lemma byte_at_past : forall (t : list Z) p, (length t <= p)%nat -> byte_at t p = 0.
Proof. intros. unfold byte_at. apply nth_overflow. lia. Qed.

Lemma zbytes_length : forall bs, length (zbytes bs) = length bs.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma bmod8 : bv_modulus 8 = 256.
Proof. reflexivity. Qed.

Lemma u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bmod8. lia. Qed.

Lemma z8_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma byte_at_zbytes : forall bs k, (k < length bs)%nat ->
  byte_at (zbytes bs) k = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
  intros bs k Hk. unfold byte_at, zbytes.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  apply map_nth.
Qed.

Lemma byte_range : forall bs k, 0 <= byte_at (zbytes bs) k < 256.
Proof.
  intros bs k. destruct (Nat.lt_ge_cases k (length bs)) as [H|H].
  - rewrite byte_at_zbytes by exact H. pose proof (bv_unsigned_in_range 8 (nth k bs (Z_to_bv 8 0))) as R.
    rewrite bmod8 in R. exact R.
  - rewrite byte_at_past by (rewrite zbytes_length; exact H). lia.
Qed.

Lemma byte_nz : forall bs k, Forall (fun b => bv_unsigned b <> 0) bs -> (k < length bs)%nat ->
  byte_at (zbytes bs) k <> 0.
Proof.
  intros bs k H Hk. rewrite byte_at_zbytes by exact Hk. rewrite Forall_forall in H.
  apply H. apply nth_In. exact Hk.
Qed.

Lemma firstn1_skipn : forall {A} (l : list A) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof.
  intros A l. induction l as [|x l IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma rd_byte : forall m a bs ts k, bytes_at rsegs m a (bs ++ Z_to_bv 8 0 :: ts) -> (k <= length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [Z_to_bv 8 (byte_at (zbytes bs) k)].
Proof.
  intros m a bs ts k H Hk.
  rewrite (bytes_at_ov_read rsegs m a _ k 1 H) by (rewrite length_app; cbn; lia).
  rewrite (firstn1_skipn _ k (Z_to_bv 8 0)) by (rewrite length_app; cbn; lia). f_equal. f_equal.
  destruct (Nat.eq_dec k (length bs)) as [E|E].
  - subst k. rewrite byte_at_past by (rewrite zbytes_length; lia).
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by lia. rewrite byte_at_zbytes by lia. symmetry. apply z8_self.
Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma byte_table : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
  intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma sp_lt : forall c, 0 <= c < 256 ->
  bv_ltu (Z_to_bv 64 (c + -9)) (Z_to_bv 64 5) = (9 <=? c) && (c <=? 13).
Proof.
  intros c Hc. apply Bool.eqb_prop.
  exact (byte_table (fun c => Bool.eqb (bv_ltu (Z_to_bv 64 (c + -9)) (Z_to_bv 64 5)) ((9 <=? c) && (c <=? 13)))
           ltac:(vm_compute; reflexivity) c Hc).
Qed.

Lemma beq_lit : forall c k, 0 <= c < 2^64 -> 0 <= k < 2^64 -> bv_eqb (Z_to_bv 64 c) (Z_to_bv 64 k) = (c =? k).
Proof. intros c k Hc Hk. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma nm_mask : forall c, 0 <= c < 256 -> c <= 58 ->
  bv_eqb (Z_to_bv 64 (Z.land (Z.shiftr 4294983169 (c mod 64)) 1)) (Z_to_bv 64 0) = negb ((c =? 0) || is_space c).
Proof.
  intros c Hc H58.
  pose proof (byte_table (fun c => (58 <? c) ||
    Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (Z.shiftr 4294983169 (c mod 64)) 1)) (Z_to_bv 64 0))
             (negb ((c =? 0) || is_space c))) ltac:(vm_compute; reflexivity) c Hc) as T.
  cbv beta in T. replace (58 <? c) with false in T by (symmetry; apply Z.ltb_ge; lia).
  apply Bool.eqb_prop. exact T.
Qed.

Lemma swrap_small_d : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

Lemma eqb0 : forall x : word, bv_eqb x (Z_to_bv 64 0) = (bv_unsigned x =? 0).
Proof. intros x. reflexivity. Qed.

Lemma lt45 : forall c, 0 <= c < 256 -> c < 45 -> bv_ltu (Z_to_bv 64 50) (Z_to_bv 64 (c + -45)) = true.
Proof.
  intros c Hc H45.
  pose proof (byte_table (fun c => (45 <=? c) || bv_ltu (Z_to_bv 64 50) (Z_to_bv 64 (c + -45)))
    ltac:(vm_compute; reflexivity) c Hc) as T.
  cbv beta in T. replace (45 <=? c) with false in T by (symmetry; apply Z.leb_gt; lia). exact T.
Qed.

Lemma pl_alnum : forall c, is_alnum c = true -> plain_ok c = true.
Proof. intros c H. unfold plain_ok. rewrite H. reflexivity. Qed.

Lemma pl_low : forall c, 0 <= c < 256 -> c < 45 -> is_alnum c = false -> plain_ok c = false.
Proof.
  intros c Hc H45 Ha.
  pose proof (byte_table (fun c => (45 <=? c) || is_alnum c || negb (plain_ok c))
    ltac:(vm_compute; reflexivity) c Hc) as T.
  cbv beta in T. replace (45 <=? c) with false in T by (symmetry; apply Z.leb_gt; lia). rewrite Ha in T.
  destruct (plain_ok c); [discriminate|reflexivity].
Qed.

Lemma pl_high : forall c, 0 <= c < 256 -> 50 < c + -45 -> is_alnum c = false -> plain_ok c = false.
Proof.
  intros c Hc H95 Ha.
  pose proof (byte_table (fun c => (c <? 96) || is_alnum c || negb (plain_ok c))
    ltac:(vm_compute; reflexivity) c Hc) as T.
  cbv beta in T. replace (c <? 96) with false in T by (symmetry; apply Z.ltb_ge; lia). rewrite Ha in T.
  destruct (plain_ok c); [discriminate|reflexivity].
Qed.

Lemma pl_mask : forall c, 0 <= c < 256 -> 45 <= c -> c + -45 <= 50 -> is_alnum c = false ->
  bv_eqb (Z_to_bv 64 (Z.land (Z.shiftr 1125899906850819 ((c + -45) mod 64)) 1)) (Z_to_bv 64 0) = negb (plain_ok c).
Proof.
  intros c Hc H45 H95 Ha.
  apply Bool.eqb_prop.
  pose proof (byte_table (fun c => (c <? 45) || negb (c <? 96) || is_alnum c ||
    Bool.eqb (bv_eqb (Z_to_bv 64 (Z.land (Z.shiftr 1125899906850819 ((c + -45) mod 64)) 1)) (Z_to_bv 64 0))
             (negb (plain_ok c))) ltac:(vm_compute; reflexivity) c Hc) as T2.
  cbv beta in T2. replace (c <? 45) with false in T2 by (symmetry; apply Z.ltb_ge; lia).
  replace (c <? 96) with true in T2 by (symmetry; apply Z.ltb_lt; lia). rewrite Ha in T2. exact T2.
Qed.

Ltac u8fix := cbv beta; repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 8 (byte_at (zbytes ?b) ?k))] => rewrite (u8 _ (byte_range b k))
  end.

Ltac bdestr := repeat match goal with
  | H : context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec0 a b); cbn [andb orb negb] in *
  | H : context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec0 a b); cbn [andb orb negb] in *
  | H : context [Z.eqb ?a ?b] |- _ => destruct (Z.eqb_spec a b); cbn [andb orb negb] in *
  end.

Ltac bcontra := bdestr; try discriminate; try congruence; lia.

Definition dbody (t : list Z) (p0 : nat) : decl_r :=
  if negb (is_space (byte_at t p0)) then DNone else
  let p1 := (p0 + count_while is_space (skipn p0 t))%nat in
  let p2 := (p1 + count_while name_ok (skipn p1 t))%nat in
  if negb (byte_at t p2 =? 58) then DNone else
  let p3 := (S p2 + count_while is_space (skipn (S p2) t))%nat in
  if negb (byte_at t p3 =? 60) then DNone else
  match find_idx (fun c => c =? 62) (skipn (S p3) t) with
  | None => DCut
  | Some o => DFound p1 (p2 - p1) (S p3) o (S p3 + o)
  end.

Lemma decl_some : forall t i p0, head t i = Some p0 -> decl t i = dbody t p0.
Proof. intros t i p0 H. unfold decl. rewrite H. reflexivity. Qed.

Lemma decl_none : forall t i, head t i = None -> decl t i = DNone.
Proof. intros t i H. unfold decl. rewrite H. reflexivity. Qed.

Lemma db_nsp : forall t p0, is_space (byte_at t p0) = false -> dbody t p0 = DNone.
Proof. intros t p0 H. unfold dbody. rewrite H. reflexivity. Qed.

Lemma db_ncolon : forall t p0 p1 p2, is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 <> 58 -> dbody t p0 = DNone.
Proof.
  intros t p0 p1 p2 Hs E1 E2 Hc. unfold dbody. rewrite Hs. cbn [negb]. cbv beta iota zeta.
  rewrite <- E1, <- E2, (proj2 (Z.eqb_neq _ _) Hc). reflexivity.
Qed.

Lemma db_nlt : forall t p0 p1 p2 p3, is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 = 58 -> p3 = (S p2 + count_while is_space (skipn (S p2) t))%nat ->
  byte_at t p3 <> 60 -> dbody t p0 = DNone.
Proof.
  intros t p0 p1 p2 p3 Hs E1 E2 Hc E3 Hl. unfold dbody. rewrite Hs. cbn [negb]. cbv beta iota zeta.
  rewrite <- E1, <- E2, Hc, Z.eqb_refl. cbn [negb]. cbv beta iota zeta.
  rewrite <- E3, (proj2 (Z.eqb_neq _ _) Hl). reflexivity.
Qed.

Lemma db_res : forall t p0 p1 p2 p3, is_space (byte_at t p0) = true ->
  p1 = (p0 + count_while is_space (skipn p0 t))%nat -> p2 = (p1 + count_while name_ok (skipn p1 t))%nat ->
  byte_at t p2 = 58 -> p3 = (S p2 + count_while is_space (skipn (S p2) t))%nat ->
  byte_at t p3 = 60 ->
  dbody t p0 = match find_idx (fun c => c =? 62) (skipn (S p3) t) with
               | None => DCut
               | Some o => DFound p1 (p2 - p1) (S p3) o (S p3 + o)
               end.
Proof.
  intros t p0 p1 p2 p3 Hs E1 E2 Hc E3 Hl. unfold dbody. rewrite Hs. cbn [negb]. cbv beta iota zeta.
  rewrite <- E1, <- E2, Hc, Z.eqb_refl. cbn [negb]. cbv beta iota zeta.
  rewrite <- E3, Hl, Z.eqb_refl. reflexivity.
Qed.

Lemma sc_end : forall t u i d f, (length t <= i)%nat -> scan t u i d (S f) = 0 /\ readings t u i d (S f) = O.
Proof. intros t u i d f H. cbn [scan readings]. rewrite (proj2 (Nat.leb_le _ _) H). split; reflexivity. Qed.

Lemma sc_none : forall t u i d f, (i < length t)%nat -> decl t i = DNone ->
  scan t u i d (S f) = scan t u (S i) d f /\ readings t u i d (S f) = readings t u (S i) d f.
Proof. intros t u i d f H D. cbn [scan readings]. rewrite (proj2 (Nat.leb_gt _ _) H), D. split; reflexivity. Qed.

Lemma sc_cut : forall t u i d f, (i < length t)%nat -> decl t i = DCut ->
  scan t u i d (S f) = 0 /\ readings t u i d (S f) = O.
Proof. intros t u i d f H D. cbn [scan readings]. rewrite (proj2 (Nat.leb_gt _ _) H), D. split; reflexivity. Qed.

Lemma sc_nomatch : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = false ->
  scan t u i d (S f) = scan t u (S close) d f /\ readings t u i d (S f) = readings t u (S close) d f.
Proof.
  intros t u i d f name nl ns nl2 close H D M. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M. split; reflexivity.
Qed.

Lemma sc_cnt : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = true -> (16 <= d)%nat ->
  scan t u i d (S f) = 1 /\ readings t u i d (S f) = O.
Proof.
  intros t u i d f name nl ns nl2 close H D M Hd. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M, (proj2 (Nat.ltb_lt 16 (S d)) ltac:(lia)). split; reflexivity.
Qed.

Lemma sc_tok : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = true -> (d < 16)%nat ->
  token t (firstn nl (skipn name t)) (skipn nl2 u) = true ->
  scan t u i d (S f) = 1 /\ readings t u i d (S f) = 1%nat.
Proof.
  intros t u i d f name nl ns nl2 close H D M Hd T. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M, (proj2 (Nat.ltb_ge 16 (S d)) ltac:(lia)), T. split; reflexivity.
Qed.

Lemma sc_next : forall t u i d f name nl ns nl2 close, (i < length t)%nat ->
  decl t i = DFound name nl ns nl2 close -> matches t u ns nl2 = true -> (d < 16)%nat ->
  token t (firstn nl (skipn name t)) (skipn nl2 u) = false ->
  scan t u i d (S f) = scan t u (S close) (S d) f /\
  readings t u i d (S f) = S (readings t u (S close) (S d) f).
Proof.
  intros t u i d f name nl ns nl2 close H D M Hd T. cbn [scan readings].
  rewrite (proj2 (Nat.leb_gt _ _) H), D, M, (proj2 (Nat.ltb_ge 16 (S d)) ltac:(lia)), T. split; reflexivity.
Qed.

Lemma head_at : forall t i, (i < length t)%nat -> byte_at t i = 64 ->
  head t i = if zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc then Some (i + 7)%nat else None.
Proof.
  intros t i Hi Hb. unfold head. rewrite Hb, Z.eqb_refl. cbn [andb].
  destruct (zl_eqb (firstn 6 (skipn (S i) t)) prefix_lc); [reflexivity|].
  rewrite (byte_at_skipn t i Hi), Hb. reflexivity.
Qed.

Lemma ci_at64 : forall t i, (i < length t)%nat -> byte_at t i = 64 -> ci_eqb (firstn 6 (skipn i t)) prefix_lc = false.
Proof. intros t i Hi Hb. rewrite (byte_at_skipn t i Hi), Hb. reflexivity. Qed.

Lemma head_nat : forall t i, byte_at t i <> 64 ->
  head t i = if ci_eqb (firstn 6 (skipn i t)) prefix_lc &&
                match i with O => true | S i' => is_space (byte_at t i') end
             then Some (i + 6)%nat else None.
Proof. intros t i Hb. unfold head. rewrite (proj2 (Z.eqb_neq _ _) Hb). reflexivity. Qed.

Lemma ci_len : forall a b, ci_eqb a b = true -> length a = length b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [_ H]. f_equal. apply IH. exact H.
Qed.

Lemma firstn_full : forall (l : list Z) n, length (firstn n l) = n -> (n <= length l)%nat.
Proof. intros l n H. rewrite length_firstn in H. lia. Qed.

Lemma find_idx_lt : forall f (l : list Z) o, find_idx f l = Some o -> (o < length l)%nat.
Proof.
  intros f l. induction l as [|x l IH]; intros o H; cbn in H; [discriminate|].
  destruct (f x); [inversion H; cbn; lia|].
  destruct (find_idx f l) as [o'|] eqn:E; cbn in H; [|discriminate]. inversion H; subst. cbn. specialize (IH o' eq_refl). lia.
Qed.

Lemma zbytes_skipn : forall bs k, zbytes (skipn k bs) = skipn k (zbytes bs).
Proof. intros bs k. unfold zbytes. revert k. induction bs as [|b bs IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.

Lemma Forall_skipn_z : forall {A} (P : A -> Prop) (l : list A) k, Forall P l -> Forall P (skipn k l).
Proof. intros A P l k H. revert k. induction H as [|x l Hx Hl IH]; intros [|k]; cbn; auto. Qed.

Lemma zbytes_nz : forall bs, Forall (fun b => bv_unsigned b <> 0) bs -> Forall (fun c => c <> 0) (zbytes bs).
Proof. intros bs H. unfold zbytes. apply Forall_map. exact H. Qed.

Lemma firstn_app0 : forall (l p : list Z), Forall (fun c => c <> 0) l -> Forall (fun c => c <> 0) p ->
  firstn (length p) (l ++ [0]) = p <-> firstn (length p) l = p.
Proof.
  intros l p Hl Hp. revert l Hl. induction p as [|y p IH]; intros l Hl; cbn [length firstn]; [tauto|].
  inversion Hp as [|y' p' Hy Hp']; subst.
  destruct l as [|x l]; cbn [app firstn].
  - split; intros H; [|discriminate]. injection H as H1 _. exfalso. apply Hy. symmetry. exact H1.
  - inversion Hl as [|x' l' Hx Hl']; subst.
    split; intros H; injection H as H1 H2; subst x; f_equal.
    + apply (proj1 (IH Hp' l Hl')). exact H2.
    + apply (proj2 (IH Hp' l Hl')). exact H2.
Qed.

Lemma tolower_app0 : forall (l p : list Z), Forall (fun c => 0 < c) l -> Forall (fun y => 97 <= y <= 122) p ->
  map tolower (firstn (length p) (l ++ [0])) = p <-> ci_eqb (firstn (length p) l) p = true.
Proof.
  intros l p Hl Hp. revert l Hl. induction p as [|y p IH]; intros l Hl; cbn [length firstn map ci_eqb]; [tauto|].
  inversion Hp as [|y' p' Hy Hp']; subst.
  destruct l as [|x l]; cbn [app firstn map ci_eqb].
  - split; intros H; [|discriminate]. injection H as H1 _. unfold tolower in H1. cbn in H1. lia.
  - inversion Hl as [|x' l' Hx Hl']; subst. split; intros H.
    + injection H as H1 H2. apply andb_true_iff. split.
      * unfold tolower in H1.
        destruct ((65 <=? x) && (x <=? 90)) eqn:E; apply orb_true_iff; [right|left]; apply Z.eqb_eq; lia.
      * apply (proj1 (IH Hp' l Hl')). exact H2.
    + apply andb_true_iff in H as [H1 H2]. f_equal.
      * apply orb_true_iff in H1 as [H1|H1]; apply Z.eqb_eq in H1; unfold tolower; subst x.
        -- destruct ((65 <=? y) && (y <=? 90)) eqn:E; [|reflexivity].
           apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
        -- destruct ((65 <=? y - 32) && (y - 32 <=? 90)) eqn:E; [lia|].
           apply andb_false_iff in E as [E|E]; apply Z.leb_gt in E; lia.
      * apply (proj2 (IH Hp' l Hl')). exact H2.
Qed.

Lemma firstn_app_le : forall (l r : list Z) n, (n <= length l)%nat -> firstn n (l ++ r) = firstn n l.
Proof. intros l r n H. rewrite firstn_app. replace (n - length l)%nat with O by lia. cbn. apply app_nil_r. Qed.

Lemma last_nth' : forall (l : list Z) d, (0 < length l)%nat -> last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x l IH]; intros d H; cbn in H; [lia|].
  destruct l as [|y l]; [reflexivity|].
  change (last (x :: y :: l) d) with (last (y :: l) d). rewrite IH by (cbn; lia).
  cbn [length]. replace (S (S (length l)) - 1)%nat with (S (S (length l) - 1)) by lia. reflexivity.
Qed.

Lemma nth_skipn' : forall (l : list Z) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros l m. revert l. induction m as [|m IH]; intros l n d; [reflexivity|].
  destruct l as [|x l]; cbn [skipn]; [destruct n; reflexivity | apply IH].
Qed.

Lemma last_skipn : forall (l : list Z) k, (k < length l)%nat -> last (skipn k l) 0 = byte_at l (length l - 1).
Proof.
  intros l k Hk. rewrite last_nth' by (rewrite length_skipn; lia). unfold byte_at.
  rewrite nth_skipn', length_skipn. f_equal. lia.
Qed.

Lemma cstr_at_suf : forall m a bs ts k, bytes_at rsegs m a (bs ++ Z_to_bv 8 0 :: ts) ->
  Forall (fun b => bv_unsigned b <> 0) bs -> (- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length ts) ->
  (k <= length bs)%nat -> cstr_at m (a + Z.of_nat k) (skipn k bs) ts.
Proof.
  intros m a bs ts k H Hnz Hal Hk.
  assert (E : bs ++ Z_to_bv 8 0 :: ts = firstn k bs ++ (skipn k bs ++ Z_to_bv 8 0 :: ts))
    by (rewrite app_assoc, firstn_skipn; reflexivity).
  rewrite E in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
  split; [exact H|]. split; [apply Forall_skipn_z; exact Hnz|].
  rewrite length_skipn. replace (a + Z.of_nat k + Z.of_nat (length bs - k)) with (a + Z.of_nat (length bs)) by lia.
  exact Hal.
Qed.

Lemma cstr0_suf : forall m a bs ts k, bytes_at rsegs m a (bs ++ Z_to_bv 8 0 :: ts) ->
  Forall (fun b => bv_unsigned b <> 0) bs -> (k <= length bs)%nat -> cstr0 m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs ts k H Hnz Hk.
  assert (E : bs ++ Z_to_bv 8 0 :: ts = firstn k bs ++ ((skipn k bs ++ [Z_to_bv 8 0]) ++ ts))
    by (rewrite <- !app_assoc, app_assoc, firstn_skipn; reflexivity).
  rewrite E in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
  apply bytes_at_app in H. destruct H as [H _].
  split; [exact H | apply Forall_skipn_z; exact Hnz].
Qed.

Lemma cstr0_full : forall m a bs ts, bytes_at rsegs m a (bs ++ Z_to_bv 8 0 :: ts) ->
  Forall (fun b => bv_unsigned b <> 0) bs -> cstr0 m a bs.
Proof. intros m a bs ts H Hnz. pose proof (cstr0_suf m a bs ts 0 H Hnz ltac:(lia)) as C. rewrite Z.add_0_r in C. exact C. Qed.

Lemma cstr_at_w : forall m (w : word) a bs ts k, bytes_at rsegs m a (bs ++ Z_to_bv 8 0 :: ts) ->
  Forall (fun b => bv_unsigned b <> 0) bs -> (- (a + Z.of_nat (length bs) + 1)) mod 8 <= Z.of_nat (length ts) ->
  (k <= length bs)%nat -> bv_unsigned w = a + Z.of_nat k -> cstr_at m (bv_unsigned w) (skipn k bs) ts.
Proof. intros m w a bs ts k H1 H2 H3 H4 H5. rewrite H5. apply cstr_at_suf; assumption. Qed.

Lemma cstr0_w : forall m (w : word) a bs ts k, bytes_at rsegs m a (bs ++ Z_to_bv 8 0 :: ts) ->
  Forall (fun b => bv_unsigned b <> 0) bs ->
  (k <= length bs)%nat -> bv_unsigned w = a + Z.of_nat k -> cstr0 m (bv_unsigned w) (skipn k bs).
Proof. intros m w a bs ts k H1 H2 H4 H5. rewrite H5. apply (cstr0_suf m a bs ts k); assumption. Qed.

Definition PLB6 : list byte := [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102; Z_to_bv 8 105; Z_to_bv 8 120].
Definition PUB6 : list byte := [Z_to_bv 8 80; Z_to_bv 8 82; Z_to_bv 8 69; Z_to_bv 8 70; Z_to_bv 8 73; Z_to_bv 8 88].

Lemma cstr0_pl : forall m, bytes_at rsegs m 66582 [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102;
  Z_to_bv 8 105; Z_to_bv 8 120; Z_to_bv 8 0] -> cstr0 m 66582 PLB6.
Proof. intros m H. split; [exact H|]. unfold PLB6. repeat constructor; intro Hx; vm_compute in Hx; discriminate Hx. Qed.

Lemma cstr0_pu : forall m, bytes_at rsegs m 66442 [Z_to_bv 8 80; Z_to_bv 8 82; Z_to_bv 8 69; Z_to_bv 8 70;
  Z_to_bv 8 73; Z_to_bv 8 88; Z_to_bv 8 0] -> cstr0 m 66442 PUB6.
Proof. intros m H. split; [exact H|]. unfold PUB6. repeat constructor; intro Hx; vm_compute in Hx; discriminate Hx. Qed.

Lemma pl_eq : firstn 6 (zbytes PLB6 ++ [0]) = prefix_lc.
Proof. vm_compute. reflexivity. Qed.

Lemma pu_eq : map tolower (firstn 6 (zbytes PUB6 ++ [0])) = prefix_lc.
Proof. vm_compute. reflexivity. Qed.

Lemma zbytes_pos : forall bs, Forall (fun b => bv_unsigned b <> 0) bs -> Forall (fun c => 0 < c) (zbytes bs).
Proof.
  intros bs H. unfold zbytes. apply Forall_map. eapply Forall_impl; [|exact H].
  intros b Hb. cbv beta in *. pose proof (bv_unsigned_in_range 8 b) as R. rewrite bmod8 in R. lia.
Qed.

Lemma ncmp6 : forall l, Forall (fun c => c <> 0) l ->
  (firstn 6 (l ++ [0]) = prefix_lc <-> zl_eqb (firstn 6 l) prefix_lc = true).
Proof.
  intros l H. rewrite zl_eqb_eq.
  pose proof (firstn_app0 l prefix_lc H ltac:(unfold prefix_lc; repeat constructor; discriminate)) as E.
  change (length prefix_lc) with 6%nat in E. exact E.
Qed.

Lemma ncase6 : forall l, Forall (fun c => 0 < c) l ->
  (map tolower (firstn 6 (l ++ [0])) = prefix_lc <-> ci_eqb (firstn 6 l) prefix_lc = true).
Proof.
  intros l H.
  pose proof (tolower_app0 l prefix_lc H ltac:(unfold prefix_lc; repeat constructor; lia)) as E.
  change (length prefix_lc) with 6%nat in E. exact E.
Qed.

Lemma lts_lit : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 -> bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt a (2^63)) ltac:(lia)), (proj2 (Z.ltb_lt b (2^63)) ltac:(lia)). reflexivity.
Qed.

Ltac litbad H := exfalso; revert H; vm_compute; let E := fresh "E" in intro E; discriminate E.

Section Scan.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z).
Variables (txt uri rp g : word) (tb ts ub us j0 : list byte) (m0 : word -> option byte).

Hypothesis NZT : Forall (fun b => bv_unsigned b <> 0) tb.
Hypothesis NZU : Forall (fun b => bv_unsigned b <> 0) ub.
Hypothesis ALT : (- (bv_unsigned txt + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length ts).
Hypothesis ALU : (- (bv_unsigned uri + Z.of_nat (length ub) + 1)) mod 8 <= Z.of_nat (length us).
Hypothesis UNE : ub <> [].
Hypothesis T0 : 4096 <= bv_unsigned txt.
Hypothesis TL63 : Z.of_nat (length tb) + 1 < 2^63.
Hypothesis U0 : 4096 <= bv_unsigned uri.
Hypothesis LO0 : 0 <= lo.
Hypothesis LO : lo + 2368 <= bv_unsigned sp + -176.
Hypothesis SPR : bv_unsigned sp < 2^64.
Hypothesis TXR : bv_unsigned txt + Z.of_nat (length tb + 1 + length ts) <= 2^64.
Hypothesis URR : bv_unsigned uri + Z.of_nat (length ub + 1 + length us) <= 2^64.
Hypothesis RPR : 0 <= bv_unsigned rp /\ bv_unsigned rp + 8 <= 2^64.
Hypothesis OT : bv_unsigned txt + Z.of_nat (length tb + 1 + length ts) <= bv_unsigned sp - 2544 \/
                bv_unsigned sp <= bv_unsigned txt.
Hypothesis OU : bv_unsigned uri + Z.of_nat (length ub + 1 + length us) <= bv_unsigned sp - 2544 \/
                bv_unsigned sp <= bv_unsigned uri.
Hypothesis ORP : bv_unsigned rp + 8 <= bv_unsigned sp - 2544 \/ bv_unsigned sp <= bv_unsigned rp.
Hypothesis OPL : 66582 + 7 <= bv_unsigned sp - 2544 \/ bv_unsigned sp <= 66582.
Hypothesis OPU : 66442 + 7 <= bv_unsigned sp - 2544 \/ bv_unsigned sp <= 66442.
Hypothesis DT : bv_unsigned rp + 8 <= bv_unsigned txt \/
                bv_unsigned txt + Z.of_nat (length tb + 1 + length ts) <= bv_unsigned rp.
Hypothesis DU : bv_unsigned rp + 8 <= bv_unsigned uri \/
                bv_unsigned uri + Z.of_nat (length ub + 1 + length us) <= bv_unsigned rp.
Hypothesis DPL : bv_unsigned rp + 8 <= 66582 \/ 66582 + 7 <= bv_unsigned rp.
Hypothesis ALNUM : isalnum_contract.
Hypothesis NCMP : strncmp_contract.
Hypothesis NCASE : strncasecmp_contract.
Hypothesis CHR : strchr_contract.
Hypothesis LEN : strlen_contract.
Hypothesis HP : has_prefixed_contract.
Hypothesis DPU : bv_unsigned rp + 8 <= 66442 \/ 66442 + 7 <= bv_unsigned rp.
Hypothesis GW8 : 0x4f6c8 + 8 <= bv_unsigned sp - 2544.
Hypothesis GC8 : 0x1e0b8 + 8 <= bv_unsigned sp - 2544.
Hypothesis DGC : bv_unsigned rp + 8 <= 0x1e0b8 \/ 0x1e0b8 + 8 <= bv_unsigned rp.
Hypothesis DGW : bv_unsigned rp + 8 <= 0x4f6c8 \/ 0x4f6c8 + 8 <= bv_unsigned rp.

Local Abbreviation tz := (zbytes tb).
Local Abbreviation uz := (zbytes ub).
Local Abbreviation TL := (length tb).
Local Abbreviation UL := (length ub).

Definition frame (dw : word) : list cell :=
  [CB 8 j0; C8 rp; C8 dw; C8 uri; C8 (Z_to_bv 64 1125899906850819); C8 (Z_to_bv 64 (Z.of_nat (length ub)));
   C8 txt; C8 (Z_to_bv 64 (bv_unsigned uri + -3)); C8 (Z_to_bv 64 (bv_unsigned uri + -2));
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition mfacts (m : word -> option byte) (dw v : word) : Prop :=
  bytes_at rsegs m (bv_unsigned txt) (tb ++ Z_to_bv 8 0 :: ts) /\
  bytes_at rsegs m (bv_unsigned uri) (ub ++ Z_to_bv 8 0 :: us) /\
  bytes_at rsegs m 66582 [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 102; Z_to_bv 8 105;
                          Z_to_bv 8 120; Z_to_bv 8 0] /\
  bytes_at rsegs m 66442 [Z_to_bv 8 80; Z_to_bv 8 82; Z_to_bv 8 69; Z_to_bv 8 70; Z_to_bv 8 73;
                          Z_to_bv 8 88; Z_to_bv 8 0] /\
  bytes_at rsegs m 0x1e0b8 (le8 (Z_to_bv 64 0x4f6c8)) /\
  bytes_at rsegs m 0x4f6c8 (le8 g) /\
  rw_cells rsegs m (bv_unsigned rp) [C8 v] /\
  rw_cells rsegs m (bv_unsigned sp + -176) (frame dw) /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp + -176) /\
  munch [(bv_unsigned sp - 2544, bv_unsigned sp); (bv_unsigned rp, bv_unsigned rp + 8)] m0 m /\
  wmono rsegs m0 m.

Definition stL (pc : Z) (m : word -> option byte)
    (ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word) : machine_state :=
  MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -176)) gp tp t0 t1 t2 x8 (Z_to_bv 64 32) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 4294983169) (Z_to_bv 64 5) (Z_to_bv 64 66582) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 58)
          t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition POSTv (r : Z) (n : nat) (v : word) : machine_state -> Prop :=
  kretm ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 2544 m0 [(bv_unsigned rp, bv_unsigned rp + 8)]
    (fun a m' => a = Z_to_bv 64 r /\
                 bytes_at rsegs m' (bv_unsigned rp) (le8 (Z_to_bv 64 (bv_unsigned v + Z.of_nat n)))).

Lemma u_sp1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176.
Proof. apply unsigned_lit. lia. Qed.

Ltac kpost :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; unfold kret, STRNCASECMP_K, STRCHR_K, HAS_PREFIXED_K in PO; rewrite ?u_sp1 in PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in
  let MIc := fresh "MIc" in let STc := fresh "STc" in
  destruct PO as [E [MUc [WMc [MIc [STc PO]]]]];
  subst ms';
  lazymatch type of MUc with
  | munch _ ?mold ?m' =>
      repeat match goal with H : stk rsegs mold _ _ |- _ => clear H end;
      transport_after_call rsegs mold m' MUc WMc;
      clear MUc WMc;
      repeat match goal with
             | H : mem_inv rsegs mold |- _ => clear H
             | H : ov_read_bytes rsegs mold _ _ = _ |- _ => clear H
             | H : store_ok rsegs mold _ _ = _ |- _ => clear H
             end;
      clear mold; rename m' into mold
  end;
  rename STc into ST; rename MIc into MI;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac norm_m m :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => try (clear m; rename mm into m)
  end.

Ltac open_mf H :=
  destruct H as (BT & BU & PL & PU & GCl & GWd & RP & FR & MI & ST & MU & WM); unfold frame in FR.

Ltac close_mf := unfold mfacts, frame; repeat (split; [eassumption|]); eassumption.

Lemma wa_rp0 : wa (bv_unsigned rp + Z.of_nat 0) = rp.
Proof. unfold wa. cbn [Z.of_nat]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma rp_bytes : forall m v, rw_cells rsegs m (bv_unsigned rp) [C8 v] -> bytes_at rsegs m (bv_unsigned rp) (le8 v).
Proof. intros m v [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma epi : forall r m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x26 t3 t4 t5 t6,
  mfacts m dw v ->
  evt rsegs (POSTv r 0 v)
    (stL 0x13f5c m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 (Z_to_bv 64 r) x26 t3 t4 t5 t6).
Proof.
  intros r m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x26 t3 t4 t5 t6 MF.
  open_mf MF. unfold stL, POSTv.
  do 15 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep. finish.
  - reflexivity.
  - rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply rp_bytes. exact RP.
Qed.

Ltac weq := first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

Definition LoopAt (f : nat) : Prop :=
  forall (i d : nat) (m : word -> option byte)
         (dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 : word),
    (i <= TL)%nat -> (TL - i < f)%nat -> (d <= 16)%nat ->
    dw = Z_to_bv 64 (Z.of_nat d) -> x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat i) ->
    mfacts m dw v ->
    evt rsegs (POSTv (scan tz uz i d f) (readings tz uz i d f) v)
      (stL 0x13d44 m ra' t0 t1 t2 (Z_to_bv 64 64) a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).

Lemma cont9c : forall f k d m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  LoopAt f -> (k < TL)%nat -> (TL - S k < f)%nat -> (d <= 16)%nat -> dw = Z_to_bv 64 (Z.of_nat d) ->
  x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat k) -> mfacts m dw v ->
  evt rsegs (POSTv (scan tz uz (S k) d f) (readings tz uz (S k) d f) v)
    (stL 0x13e9c m ra' t0 t1 t2 (Z_to_bv 64 64) a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros f k d m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 LF Hk Hf Hd Hdw Hx MF.
  subst x21. unfold stL. zstep. zstep.
  eapply LF; [ | | exact Hd | exact Hdw | | exact MF]; [lia | lia | weq].
Qed.

Lemma cont98 : forall f k d m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  LoopAt f -> (k < TL)%nat -> (TL - S k < f)%nat -> (d <= 16)%nat -> dw = Z_to_bv 64 (Z.of_nat d) ->
  x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat k) -> mfacts m dw v ->
  evt rsegs (POSTv (scan tz uz (S k) d f) (readings tz uz (S k) d f) v)
    (stL 0x13e98 m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros f k d m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 LF Hk Hf Hd Hdw Hx MF.
  unfold stL. zstep. eapply cont9c; eassumption.
Qed.

Lemma sp1_loop : forall n Q m p ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  n = (TL - p)%nat -> (p <= TL)%nat ->
  bytes_at rsegs m (bv_unsigned txt) (tb ++ Z_to_bv 8 0 :: ts) ->
  a0 = Z_to_bv 64 (byte_at tz p) ->
  x22 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p) ->
  x24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p + 2) ->
  x8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p + 2) ->
  x25 = Z_to_bv 64 (bv_unsigned uri + -2 - (bv_unsigned txt + Z.of_nat p)) ->
  x26 = Z_to_bv 64 (bv_unsigned uri + -3 - (bv_unsigned txt + Z.of_nat p)) ->
  (forall q y8 y10 y11 y12 y22 y24 y25 y26,
     q = (p + count_while is_space (skipn p tz))%nat ->
     y10 = Z_to_bv 64 (byte_at tz q) ->
     y22 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q) ->
     y24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q + 2) ->
     y8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q + 2) ->
     y25 = Z_to_bv 64 (bv_unsigned uri + -2 - (bv_unsigned txt + Z.of_nat q)) ->
     y26 = Z_to_bv 64 (bv_unsigned uri + -3 - (bv_unsigned txt + Z.of_nat q)) ->
     evt rsegs Q (stL 0x13dfc m ra' t0 t1 t2 y8 y10 y11 y12 a3 a4 a5 a6 a7 x21 y22 x23 y24 y25 y26 t3 t4 t5 t6)) ->
  evt rsegs Q (stL 0x13dd0 m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros Q m p ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    Hn Hp BT H10 H22 H24 H8 H25 H26 K; subst a0 x22 x24 x8 x25 x26; unfold stL.
  pose proof (byte_range tb p) as Rc.
  destruct (is_space (byte_at tz p)) eqn:SP.
  - assert (Hlt : (p < TL)%nat).
    { destruct (Nat.eq_dec p TL) as [E|E]; [|lia]. subst p.
      rewrite byte_at_past in SP by (rewrite zbytes_length; lia). discriminate. }
    assert (Lz : (p < length tz)%nat) by (rewrite zbytes_length; exact Hlt).
    pose proof (rd_byte m (bv_unsigned txt) tb ts (S p) BT ltac:(lia)) as HR.
    zstep. rewrite (land255 _ Rc). zstep. zstep.
    if_cases HC1; rewrite (sp_lt _ Rc) in HC1.
    + zstep. if_cases HC2; rewrite beq_lit in HC2 by lia.
      * zstep. u8fix. do 6 zstep.
        eapply (IH (TL - S p)%nat ltac:(lia)); [reflexivity | lia | exact BT | reflexivity | weq | weq | weq | weq | weq |].
        intros q y8 y10 y11 y12 y22 y24 y25 y26 Hq. apply K. rewrite Hq, (cw_step _ _ _ Lz), SP. lia.
      * exfalso. unfold is_space in *. bcontra.
    + zstep. u8fix. do 6 zstep.
      eapply (IH (TL - S p)%nat ltac:(lia)); [reflexivity | lia | exact BT | reflexivity | weq | weq | weq | weq | weq |].
      intros q y8 y10 y11 y12 y22 y24 y25 y26 Hq. apply K. rewrite Hq, (cw_step _ _ _ Lz), SP. lia.
  - assert (Hq : (p + count_while is_space (skipn p tz))%nat = p).
    { destruct (Nat.lt_ge_cases p TL) as [L|L].
      - rewrite cw_step, SP by (rewrite zbytes_length; exact L). lia.
      - rewrite cw_end by (rewrite zbytes_length; exact L). lia. }
    zstep. rewrite (land255 _ Rc). zstep. zstep.
    if_cases HC1; rewrite (sp_lt _ Rc) in HC1.
    + zstep. if_cases HC2; rewrite beq_lit in HC2 by lia.
      * exfalso. unfold is_space in *. bcontra.
      * eapply K; rewrite ?Hq; reflexivity.
    + exfalso. unfold is_space in *. bcontra.
Qed.

Lemma name_loop : forall n Q m p p1 ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  n = (TL - p)%nat -> (p <= TL)%nat -> (p1 <= p)%nat ->
  bytes_at rsegs m (bv_unsigned txt) (tb ++ Z_to_bv 8 0 :: ts) ->
  a0 = Z_to_bv 64 (byte_at tz p) ->
  a1 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p) ->
  x23 = Z_to_bv 64 (Z.of_nat (p - p1)) ->
  x24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p + 2) ->
  x8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p + 2) ->
  x25 = Z_to_bv 64 (bv_unsigned uri + -2 - (bv_unsigned txt + Z.of_nat p)) ->
  x26 = Z_to_bv 64 (bv_unsigned uri + -3 - (bv_unsigned txt + Z.of_nat p)) ->
  (forall y8 y10 y11 y12 y23 y24 y25 y26,
     byte_at tz (p + count_while name_ok (skipn p tz)) <> 58 ->
     evt rsegs Q (stL 0x13e98 m ra' t0 t1 t2 y8 y10 y11 y12 a3 a4 a5 a6 a7 x21 x22 y23 y24 y25 y26 t3 t4 t5 t6)) ->
  (forall q y8 y10 y11 y12 y23 y24 y25 y26,
     q = (p + count_while name_ok (skipn p tz))%nat ->
     byte_at tz q = 58 ->
     y11 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q) ->
     y23 = Z_to_bv 64 (Z.of_nat (q - p1)) ->
     y24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q + 2) ->
     y8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q + 2) ->
     y25 = Z_to_bv 64 (bv_unsigned uri + -2 - (bv_unsigned txt + Z.of_nat q)) ->
     y26 = Z_to_bv 64 (bv_unsigned uri + -3 - (bv_unsigned txt + Z.of_nat q)) ->
     evt rsegs Q (stL 0x13e3c m ra' t0 t1 t2 y8 y10 y11 y12 a3 a4 a5 a6 a7 x21 x22 y23 y24 y25 y26 t3 t4 t5 t6)) ->
  evt rsegs Q (stL 0x13e04 m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros Q m p p1 ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    Hn Hp Hp1 BT H10 H11 H23 H24 H8 H25 H26 KF KC; subst a0 a1 x23 x24 x8 x25 x26; unfold stL.
  pose proof (byte_range tb p) as Rc.
  destruct (name_ok (byte_at tz p)) eqn:NO.
  - assert (Hlt : (p < TL)%nat).
    { destruct (Nat.eq_dec p TL) as [E|E]; [|lia]. subst p.
      rewrite byte_at_past in NO by (rewrite zbytes_length; lia). discriminate. }
    assert (Lz : (p < length tz)%nat) by (rewrite zbytes_length; exact Hlt).
    assert (Hcw : count_while name_ok (skipn p tz) = S (count_while name_ok (skipn (S p) tz)))
      by (rewrite (cw_step _ _ _ Lz), NO; reflexivity).
    pose proof (rd_byte m (bv_unsigned txt) tb ts (S p) BT ltac:(lia)) as HR.
    zstep. rewrite (land255 _ Rc). zstep.
    if_cases HC1; rewrite ltu_lit in HC1 by lia.
    + zstep. u8fix. do 7 zstep.
      eapply (IH (TL - S p)%nat ltac:(lia) Q m (S p) p1); [reflexivity | lia | lia | exact BT | reflexivity | weq | weq | weq | weq | weq | weq | |].
      * intros y8 y10 y11 y12 y23 y24 y25 y26 Hb. apply KF. rewrite Hcw. replace (p + S _)%nat with (S p + count_while name_ok (skipn (S p) tz))%nat by lia. exact Hb.
      * intros q y8 y10 y11 y12 y23 y24 y25 y26 Hq. apply KC. rewrite Hq, Hcw. lia.
    + zstep. zstep. zstep.
      if_cases HC2; rewrite nm_mask in HC2 by lia.
      * exfalso. unfold name_ok, is_space in *. bcontra.
      * zstep. if_cases HC3; rewrite beq_lit in HC3 by lia.
        -- exfalso. unfold name_ok, is_space in *. bcontra.
        -- zstep. u8fix. do 7 zstep.
           eapply (IH (TL - S p)%nat ltac:(lia) Q m (S p) p1); [reflexivity | lia | lia | exact BT | reflexivity | weq | weq | weq | weq | weq | weq | |].
           ++ intros y8 y10 y11 y12 y23 y24 y25 y26 Hb. apply KF. rewrite Hcw. replace (p + S _)%nat with (S p + count_while name_ok (skipn (S p) tz))%nat by lia. exact Hb.
           ++ intros q y8 y10 y11 y12 y23 y24 y25 y26 Hq. apply KC. rewrite Hq, Hcw. lia.
  - assert (Hq : (p + count_while name_ok (skipn p tz))%nat = p).
    { destruct (Nat.lt_ge_cases p TL) as [L|L].
      - rewrite cw_step, NO by (rewrite zbytes_length; exact L). lia.
      - rewrite cw_end by (rewrite zbytes_length; exact L). lia. }
    zstep. rewrite (land255 _ Rc). zstep.
    if_cases HC1; rewrite ltu_lit in HC1 by lia.
    + exfalso. unfold name_ok, is_space in *. bcontra.
    + zstep. zstep. zstep.
      if_cases HC2; rewrite nm_mask in HC2 by lia.
      * apply KF. rewrite Hq. unfold is_space in HC2. bcontra.
      * zstep. if_cases HC3; rewrite beq_lit in HC3 by lia.
        -- eapply KC; rewrite ?Hq; try reflexivity. bcontra.
        -- exfalso. unfold name_ok, is_space in *. bcontra.
Qed.

Lemma sp2_loop : forall n Q m p ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  n = (TL - p)%nat -> (p <= TL)%nat ->
  bytes_at rsegs m (bv_unsigned txt) (tb ++ Z_to_bv 8 0 :: ts) ->
  x24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p + 1) ->
  x8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p + 1) ->
  x25 = Z_to_bv 64 (bv_unsigned uri + -1 - (bv_unsigned txt + Z.of_nat p)) ->
  x26 = Z_to_bv 64 (bv_unsigned uri + -2 - (bv_unsigned txt + Z.of_nat p)) ->
  (forall q y8 y10 y11 y24 y25 y26,
     q = (p + count_while is_space (skipn p tz))%nat ->
     y10 = Z_to_bv 64 (byte_at tz q) ->
     y24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q + 1) ->
     y8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat q + 1) ->
     y25 = Z_to_bv 64 (bv_unsigned uri + -1 - (bv_unsigned txt + Z.of_nat q)) ->
     y26 = Z_to_bv 64 (bv_unsigned uri + -2 - (bv_unsigned txt + Z.of_nat q)) ->
     evt rsegs Q (stL 0x13e60 m ra' t0 t1 t2 y8 y10 y11 a2 a3 a4 a5 a6 a7 x21 x22 x23 y24 y25 y26 t3 t4 t5 t6)) ->
  evt rsegs Q (stL 0x13e3c m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros Q m p ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    Hn Hp BT H24 H8 H25 H26 K; subst x24 x8 x25 x26; unfold stL.
  pose proof (byte_range tb p) as Rc.
  pose proof (rd_byte m (bv_unsigned txt) tb ts p BT Hp) as HR.
  destruct (is_space (byte_at tz p)) eqn:SP.
  - assert (Hlt : (p < TL)%nat).
    { destruct (Nat.eq_dec p TL) as [E|E]; [|lia]. subst p.
      rewrite byte_at_past in SP by (rewrite zbytes_length; lia). discriminate. }
    assert (Lz : (p < length tz)%nat) by (rewrite zbytes_length; exact Hlt).
    zstep. u8fix. zstep. zstep.
    if_cases HC1; rewrite (sp_lt _ Rc) in HC1.
    + zstep. if_cases HC2; rewrite beq_lit in HC2 by lia.
      * do 5 zstep.
        eapply (IH (TL - S p)%nat ltac:(lia) Q m (S p)); [reflexivity | lia | exact BT | weq | weq | weq | weq |].
        intros q y8 y10 y11 y24 y25 y26 Hq. apply K. rewrite Hq, (cw_step _ _ _ Lz), SP. lia.
      * exfalso. unfold is_space in *. bcontra.
    + do 5 zstep.
      eapply (IH (TL - S p)%nat ltac:(lia) Q m (S p)); [reflexivity | lia | exact BT | weq | weq | weq | weq |].
      intros q y8 y10 y11 y24 y25 y26 Hq. apply K. rewrite Hq, (cw_step _ _ _ Lz), SP. lia.
  - assert (Hq : (p + count_while is_space (skipn p tz))%nat = p).
    { destruct (Nat.lt_ge_cases p TL) as [L|L].
      - rewrite cw_step, SP by (rewrite zbytes_length; exact L). lia.
      - rewrite cw_end by (rewrite zbytes_length; exact L). lia. }
    zstep. u8fix. zstep. zstep.
    if_cases HC1; rewrite (sp_lt _ Rc) in HC1.
    + zstep. if_cases HC2; rewrite beq_lit in HC2 by lia.
      * exfalso. unfold is_space in *. bcontra.
      * eapply K; rewrite ?Hq; reflexivity.
    + exfalso. unfold is_space in *. bcontra.
Qed.

Ltac pl_next IH KO KF Hfa PLc Q m k dw v :=
  zstep; zstep; zstep;
  let HC3 := fresh "HC3" in
  if_cases HC3; rewrite eqb0, unsigned_lit in HC3 by lia;
  [ eapply (IH (UL - S k)%nat ltac:(lia) Q m (S k) dw v);
    [ reflexivity | bcontra | close_mf | weq | weq
    | intros Hall; apply KO; rewrite Hfa, PLc, Hall; reflexivity
    | intros Hall; apply KF; rewrite Hfa, PLc, Hall; reflexivity ]
  | eapply KO; [ rewrite Hfa, PLc, skipn_all2 by (rewrite zbytes_length; bcontra); reflexivity | close_mf ] ].

Lemma plain_loop : forall n Q m k dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  n = (UL - k)%nat -> (k < UL)%nat ->
  mfacts m dw v ->
  x8 = Z_to_bv 64 (bv_unsigned uri + Z.of_nat k) ->
  x25 = Z_to_bv 64 (Z.of_nat (UL - k)) ->
  (forallb plain_ok (skipn k uz) = true ->
   forall m' ra'' u0 u1 u2 y8 b0 b1 b2 b3 b4 b5 b6 b7 y25 y26 u3 u4 u5 u6, mfacts m' dw v ->
   evt rsegs Q (stL 0x13f10 m' ra'' u0 u1 u2 y8 b0 b1 b2 b3 b4 b5 b6 b7 x21 x22 x23 x24 y25 y26 u3 u4 u5 u6)) ->
  (forallb plain_ok (skipn k uz) = false ->
   forall m' ra'' u0 u1 u2 y8 b0 b1 b2 b3 b4 b5 b6 b7 y25 y26 u3 u4 u5 u6, mfacts m' dw v ->
   evt rsegs Q (stL 0x13e98 m' ra'' u0 u1 u2 y8 b0 b1 b2 b3 b4 b5 b6 b7 x21 x22 x23 x24 y25 y26 u3 u4 u5 u6)) ->
  evt rsegs Q (stL 0x13ed8 m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros n. induction n as [n IH] using lt_wf_ind.
  intros Q m k dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    Hn Hk MF H8 H25 KO KF; subst x8 x25.
  pose proof MF as MF0. open_mf MF. unfold stL.
  pose proof (byte_range ub k) as Rc.
  pose proof (rd_byte m (bv_unsigned uri) ub us k BU ltac:(lia)) as HR.
  zstep. u8fix. zstep. zstep.
  eapply evt_cut.
  { eapply ALNUM; [ rewrite unsigned_lit by lia; lia | exact MI | rewrite u_sp1; exact ST ]. }
  clear MF0.
  kpost.
  rewrite unsigned_lit in PO by lia.
  assert (Lz : (k < length uz)%nat) by (rewrite zbytes_length; exact Hk).
  assert (Hfa : forallb plain_ok (skipn k uz) = plain_ok (byte_at uz k) && forallb plain_ok (skipn (S k) uz))
    by (rewrite (byte_at_skipn _ _ Lz); reflexivity).
  zstep.
  if_cases HC1; rewrite eqb0 in HC1.
  - assert (PLc : plain_ok (byte_at uz k) = true) by (apply pl_alnum, PO; bcontra).
    pl_next IH KO KF Hfa PLc Q m k dw v.
  - assert (ALc : is_alnum (byte_at uz k) = false)
      by (apply not_true_is_false; intros E; apply PO in E; bcontra).
    zstep. zstep. zstep.
    destruct (Z.ltb_spec (byte_at uz k) 45) as [L45|L45].
    + assert (PLc : plain_ok (byte_at uz k) = false) by (apply pl_low; assumption).
      if_cases HC2; rewrite (lt45 _ Rc L45) in HC2; [|discriminate].
      eapply KF; [rewrite Hfa, PLc; reflexivity | close_mf].
    + if_cases HC2; rewrite ltu_lit in HC2 by lia.
      * assert (PLc : plain_ok (byte_at uz k) = false) by (apply pl_high; [exact Rc | bcontra | exact ALc]).
        eapply KF; [rewrite Hfa, PLc; reflexivity | close_mf].
      * zstep. zstep. zstep. zstep.
        if_cases HC4; rewrite pl_mask in HC4 by (first [exact Rc | lia | bcontra | exact ALc]).
        -- assert (PLc : plain_ok (byte_at uz k) = false) by (destruct (plain_ok (byte_at uz k)); [discriminate|reflexivity]).
           eapply KF; [rewrite Hfa, PLc; reflexivity | close_mf].
        -- assert (PLc : plain_ok (byte_at uz k) = true) by (destruct (plain_ok (byte_at uz k)); [reflexivity|discriminate]).
           pl_next IH KO KF Hfa PLc Q m k dw v.
Qed.

Lemma POSTv_shift : forall r n v ms,
  evt rsegs (POSTv r n (Z_to_bv 64 (bv_unsigned v + 1))) ms -> evt rsegs (POSTv r (S n) v) ms.
Proof.
  intros r n v ms H. eapply evt_mono; [exact H|]. intros ms' Hp. unfold POSTv, kretm in *.
  destruct Hp as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MUp & WMp & MIp & STp & Ra & Rb).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MUp|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|].
  split; [exact Ra|].
  rewrite unsigned_Z_to_bv_add in Rb. replace (bv_unsigned v + Z.of_nat (S n)) with (bv_unsigned v + 1 + Z.of_nat n) by lia.
  exact Rb.
Qed.

Lemma cstr_txt : forall m, bytes_at rsegs m (bv_unsigned txt) (tb ++ Z_to_bv 8 0 :: ts) -> cstr_at m (bv_unsigned txt) tb ts.
Proof. intros m H. exact (conj H (conj NZT ALT)). Qed.

Lemma skipn_ne : forall k, (k < UL)%nat -> skipn k ub <> [].
Proof. intros k Hk E. apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn in E. lia. Qed.

Lemma ncase_path : forall Q i m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  (i < TL)%nat -> mfacts m dw v -> x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat i) ->
  (ci_eqb (firstn 6 (skipn i tz)) prefix_lc && match i with O => true | S i' => is_space (byte_at tz i') end = false ->
   forall m' ra'' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6, mfacts m' dw v ->
   evt rsegs Q (stL 0x13e9c m' ra'' u0 u1 u2 (Z_to_bv 64 64) b0 b1 b2 b3 b4 b5 b6 b7 x21 x22 x23 x24 x25 x26 u3 u4 u5 u6)) ->
  (ci_eqb (firstn 6 (skipn i tz)) prefix_lc && match i with O => true | S i' => is_space (byte_at tz i') end = true ->
   forall m' ra'' u0 u1 u2 b0 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6, mfacts m' dw v ->
   evt rsegs Q (stL 0x13da4 m' ra'' u0 u1 u2 (Z_to_bv 64 64) b0 (Z_to_bv 64 6) b2 b3 b4 b5 b6 b7 x21 x22 x23 x24 x25 x26 u3 u4 u5 u6)) ->
  evt rsegs Q (stL 0x13d68 m ra' t0 t1 t2 (Z_to_bv 64 64) a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros Q i m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 Hi MF H21 K1 K2.
  subst x21. pose proof MF as MF0. open_mf MF. unfold stL.
  do 5 zstep.
  eapply evt_cut.
  { eapply NCASE.
    - eapply (cstr0_w m _ (bv_unsigned txt) tb ts i BT NZT); [lia | rewrite unsigned_lit by lia; reflexivity].
    - replace (bv_unsigned (Z_to_bv 64 66442)) with 66442 by reflexivity. apply cstr0_pu. exact PU.
    - exact MI.
    - rewrite u_sp1. exact ST.
    - unfold STRNCASECMP_K. rewrite u_sp1. lia.
    - unfold off_stack, STRNCASECMP_K. rewrite u_sp1, unsigned_lit by lia. rewrite length_skipn. lia.
    - unfold off_stack, STRNCASECMP_K. rewrite u_sp1. replace (bv_unsigned (Z_to_bv 64 66442)) with 66442 by reflexivity.
      unfold PUB6. cbn [length]. lia. }
  clear MF0. kpost.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat in PO.
  rewrite pu_eq, zbytes_skipn in PO.
  pose proof (iff_trans PO (ncase6 _ (Forall_skipn_z _ _ i (zbytes_pos tb NZT)))) as PO'. clear PO.
  match type of PO' with (bv_unsigned ?r = 0 <-> _) => rename r into rr end.
  zstep.
  if_cases HC1; rewrite eqb0 in HC1.
  - assert (CI : ci_eqb (firstn 6 (skipn i tz)) prefix_lc = false)
      by (apply not_true_is_false; intro E; apply PO' in E; bcontra).
    eapply K1; [rewrite CI; reflexivity | close_mf].
  - assert (CI : ci_eqb (firstn 6 (skipn i tz)) prefix_lc = true) by (apply PO'; bcontra).
    zstep. zstep. zstep.
    if_cases HC2; unfold bv_eqb in HC2; rewrite unsigned_lit in HC2 by lia.
    + eapply K2; [|close_mf]. rewrite CI. destruct i as [|i']; [reflexivity|]. exfalso. bcontra.
    + destruct i as [|i']; [exfalso; bcontra|].
      pose proof (rd_byte m (bv_unsigned txt) tb ts i' BT ltac:(lia)) as HR.
      pose proof (byte_range tb i') as Rc.
      zstep. u8fix. zstep. zstep.
      if_cases HC3; rewrite (sp_lt _ Rc) in HC3.
      * eapply K2; [|close_mf]. rewrite CI. cbv beta iota. unfold is_space. rewrite HC3. apply orb_true_r.
      * zstep. if_cases HC4; rewrite beq_lit in HC4 by lia.
        -- eapply K2; [|close_mf]. rewrite CI. cbv beta iota. unfold is_space. rewrite HC4. reflexivity.
        -- zstep. eapply K1; [|close_mf]. rewrite CI. cbv beta iota. unfold is_space. rewrite HC4, HC3. reflexivity.
Qed.

Lemma match_part : forall f i d name nl ns nl2 close m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  LoopAt f -> (i < TL)%nat -> (TL - i < S f)%nat -> (d <= 16)%nat -> dw = Z_to_bv 64 (Z.of_nat d) ->
  decl tz i = DFound name nl ns nl2 close -> (name + nl <= TL)%nat -> (i < ns)%nat -> close = (ns + nl2)%nat ->
  (close < TL)%nat ->
  a0 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat close) -> x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat close) ->
  x8 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat ns) -> x22 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat name) ->
  x23 = Z_to_bv 64 (Z.of_nat nl) -> x24 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat ns) ->
  x25 = Z_to_bv 64 (bv_unsigned uri - (bv_unsigned txt + Z.of_nat ns)) ->
  x26 = Z_to_bv 64 (bv_unsigned uri + -1 - (bv_unsigned txt + Z.of_nat ns)) ->
  mfacts m dw v ->
  evt rsegs (POSTv (scan tz uz i d (S f)) (readings tz uz i d (S f)) v)
    (stL 0x13e7c m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros f i d name nl ns nl2 close m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    LF Hi Hf Hd Hdw Hdf Hnl Hns Hcl HclT H10 H21 H8 H22 H23 H24 H25 H26 MF.
  subst a0 x21 x8 x22 x23 x24 x25 x26 close dw. pose proof MF as MF0. open_mf MF. unfold stL.
  assert (Li : (i < length tz)%nat) by (rewrite zbytes_length; exact Hi).
  zstep. zstep. zstep.
  if_cases HC1; rewrite ltu_lit in HC1 by lia.
  - assert (NM : matches tz uz ns nl2 = false).
    { unfold matches. rewrite (proj2 (Nat.ltb_ge _ _)); [reflexivity|]. rewrite zbytes_length. bcontra. }
    destruct (sc_nomatch tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf NM) as [E1 E2]. rewrite E1, E2.
    eapply cont98; [exact LF | lia | lia | exact Hd | reflexivity | reflexivity | exact MF0].
  - assert (NL2 : (nl2 < UL)%nat) by bcontra.
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply NCMP.
      - exact (cstr0_full m (bv_unsigned uri) ub us BU NZU).
      - eapply (cstr0_w m _ (bv_unsigned txt) tb ts ns BT NZT); [lia | rewrite unsigned_lit by lia; reflexivity].
      - exact MI.
      - rewrite u_sp1. exact ST. }
    clear MF0. kpost.
    rewrite unsigned_lit in PO by lia.
    match type of PO with context [Z.to_nat ?e] => replace (Z.to_nat e) with nl2 in PO by lia end.
    rewrite !zbytes_skipn, !firstn_app_le in PO by (rewrite ?length_skipn, ?zbytes_length; lia).
    match type of PO with (bv_unsigned ?r = 0 <-> _) => rename r into rr end.
    zstep.
    if_cases HC2; rewrite eqb0 in HC2.
    + assert (HPF : firstn nl2 (skipn ns tz) = firstn nl2 uz) by (symmetry; apply PO; bcontra).
      clear PO.
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply LEN.
        - eapply (cstr_at_w m _ (bv_unsigned uri) ub us nl2 BU NZU ALU); [lia | rewrite unsigned_lit by lia; lia].
        - exact MI.
        - rewrite u_sp1. exact ST. }
      kpost.
      rewrite length_skipn in PO.
      match type of PO with ?r = _ => subst r end.
      zstep.
      if_cases HC3; rewrite eqb0, unsigned_lit in HC3 by lia; [exfalso; bcontra|].
      zstep. zstep. zstep.
      pose proof (rd_byte m (bv_unsigned uri) ub us (UL - 1) BU ltac:(lia)) as HR.
      pose proof (byte_range ub (UL - 1)) as Rl.
      zstep. u8fix. zstep. zstep.
      assert (PNE : plain_name (skipn nl2 uz) = negb (byte_at uz (UL - 1) =? 46) && forallb plain_ok (skipn nl2 uz)).
      { unfold plain_name. destruct (skipn nl2 uz) eqn:SK.
        - exfalso. apply (f_equal (@length _)) in SK. rewrite length_skipn, zbytes_length in SK. cbn in SK. lia.
        - rewrite <- SK, last_skipn by (rewrite zbytes_length; lia). rewrite zbytes_length. reflexivity. }
      assert (MEQ : matches tz uz ns nl2 = plain_name (skipn nl2 uz)).
      { unfold matches. rewrite (proj2 (Nat.ltb_lt _ _)) by (rewrite zbytes_length; exact NL2).
        rewrite HPF, zl_eqb_refl. reflexivity. }
      if_cases HC4; rewrite beq_lit in HC4 by lia.
      * assert (NM : matches tz uz ns nl2 = false) by (rewrite MEQ, PNE, HC4; reflexivity).
        destruct (sc_nomatch tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf NM) as [E1 E2]. rewrite E1, E2.
        eapply cont98; [exact LF | lia | lia | exact Hd | reflexivity | reflexivity | close_mf].
      * zstep.
        eapply (plain_loop (UL - nl2) _ m nl2 (Z_to_bv 64 (Z.of_nat d)) v); [reflexivity | exact NL2 | close_mf | weq | weq | |].
        -- intros Hall m' ra'' u0 u1 u2 y8 b0 b1 b2 b3 b4 b5 b6 b7 y25 y26 u3 u4 u5 u6 MF'.
           assert (MT : matches tz uz ns nl2 = true) by (rewrite MEQ, PNE, HC4, Hall; reflexivity).
           repeat match goal with H : context [m] |- _ => clear H end. clear m. rename m' into m.
           open_mf MF'. unfold stL.
           zstep. zstep. zstep. zstep.
           if_cases HC5; rewrite lts_lit in HC5 by lia.
           ++ destruct (sc_cnt tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf MT ltac:(bcontra)) as [E1 E2].
              rewrite E1, E2. eapply epi. close_mf.
           ++ assert (D15 : (d < 16)%nat) by bcontra.
              zstep. zstep. zstep.
              assert (TST : store_ok rsegs m rp 8 = true)
                by (apply (rw_cells_store_ok_at rsegs m (bv_unsigned rp) [C8 v] 0 (C8 v) 8 rp RP);
                    [reflexivity | reflexivity | addr_eq_tac]).
              zstep. clear TST.
              replace (write_to_mem m rp) with (write_to_mem m (wa (bv_unsigned rp + Z.of_nat 0))) by (rewrite wa_rp0; reflexivity).
              mem_after_store. norm_m m.
              zstep. zstep. zstep. zstep. zstep.
              pose proof HP as HP'. unfold has_prefixed_contract in HP'.
              eapply evt_cut.
              { eapply HP' with (q := Z.of_nat name).
                - exact (cstr_txt _ BT).
                - eapply (cstr_at_w _ _ (bv_unsigned uri) ub us nl2 BU NZU ALU); [lia | rewrite unsigned_lit by lia; lia].
                - apply skipn_ne. exact NL2.
                - exact GCl.
                - exists g. exact GWd.
                - unfold HAS_PREFIXED_K. rewrite u_sp1. lia.
                - unfold HAS_PREFIXED_K. rewrite u_sp1. lia.
                - exact T0.
                - exact TL63.
                - lia.
                - rewrite unsigned_lit by lia. lia.
                - rewrite unsigned_lit by lia. reflexivity.
                - exact MI.
                - rewrite u_sp1. exact ST.
                - unfold HAS_PREFIXED_K. rewrite u_sp1. lia.
                - unfold off_stack, HAS_PREFIXED_K. rewrite u_sp1. lia.
                - unfold off_stack, HAS_PREFIXED_K. rewrite u_sp1, unsigned_lit by lia. rewrite length_skipn. lia. }
              clear HP'. kpost.
              rewrite unsigned_lit, !Nat2Z.id, zbytes_skipn in PO by lia.
              match type of PO with ?r = _ => subst r end.
              destruct (token tz (firstn nl (skipn name tz)) (skipn nl2 uz)) eqn:TK.
              ** zstep. if_cases HC6; [|litbad HC6].
                 destruct (sc_tok tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf MT D15 TK) as [E1 E2].
                 rewrite E1, E2. apply POSTv_shift. eapply epi. close_mf.
              ** zstep. if_cases HC6; [litbad HC6|].
                 zstep. zstep.
                 rewrite (swrap_small_d (Z.of_nat d + 1)) by lia.
                 replace (Z.of_nat d + 1) with (Z.of_nat (S d)) by lia.
                 zstep. zstep.
                 destruct (sc_next tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf MT D15 TK) as [E1 E2].
                 rewrite E1, E2. apply POSTv_shift.
                 eapply cont98; [exact LF | lia | lia | lia | reflexivity | reflexivity | close_mf].
        -- intros Hall m' ra'' u0 u1 u2 y8 b0 b1 b2 b3 b4 b5 b6 b7 y25 y26 u3 u4 u5 u6 MF'.
           assert (NM : matches tz uz ns nl2 = false) by (rewrite MEQ, PNE, Hall, andb_false_r; reflexivity).
           destruct (sc_nomatch tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf NM) as [E1 E2]. rewrite E1, E2.
           eapply cont98; [exact LF | lia | lia | exact Hd | reflexivity | reflexivity | exact MF'].
    + assert (NM : matches tz uz ns nl2 = false).
      { unfold matches. rewrite (proj2 (Nat.ltb_lt _ _)) by (rewrite zbytes_length; exact NL2).
        destruct (zl_eqb (firstn nl2 (skipn ns tz)) (firstn nl2 uz)) eqn:Z; [|reflexivity].
        exfalso. apply zl_eqb_eq in Z. symmetry in Z. apply PO in Z. bcontra. }
      destruct (sc_nomatch tz uz i d f name nl ns nl2 (ns + nl2) Li Hdf NM) as [E1 E2]. rewrite E1, E2.
      eapply cont98; [exact LF | lia | lia | exact Hd | reflexivity | reflexivity | close_mf].
Qed.

Lemma from_sp : forall f i d p0 m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  LoopAt f -> (i < TL)%nat -> (TL - i < S f)%nat -> (d <= 16)%nat -> dw = Z_to_bv 64 (Z.of_nat d) ->
  decl tz i = dbody tz p0 -> (i < p0 <= TL)%nat -> is_space (byte_at tz p0) = true ->
  x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat i) -> a1 = Z_to_bv 64 (Z.of_nat (p0 - i)) ->
  a0 = Z_to_bv 64 (byte_at tz p0) -> x22 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat p0) ->
  mfacts m dw v ->
  evt rsegs (POSTv (scan tz uz i d (S f)) (readings tz uz i d (S f)) v)
    (stL 0x13db4 m ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros f i d p0 m dw v ra' t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    LF Hi Hf Hd Hdw Hdecl Hp0 SP H21 Ha1 Ha0 H22 MF.
  subst x21 a1 a0 x22. pose proof MF as MF0. open_mf MF. unfold stL.
  assert (Li : (i < length tz)%nat) by (rewrite zbytes_length; exact Hi).
  do 7 zstep.
  eapply (sp1_loop (TL - p0) _ m p0); [reflexivity | lia | exact BT | weq | weq | weq | weq | weq | weq |].
  intros q y8 y10 y11 y12 y22 y24 y25 y26 Hq H10 H22 H24 H8 H25 H26. subst y10 y22 y24 y8 y25 y26. unfold stL.
  assert (Q1 : (q <= TL)%nat).
  { pose proof (cw_le is_space (skipn p0 tz)) as C. rewrite length_skipn, zbytes_length in C. lia. }
  zstep. zstep.
  eapply (name_loop (TL - q) _ m q q); [reflexivity | lia | lia | exact BT | weq | weq | weq | weq | weq | weq | weq | |].
  - intros n8 n10 n11 n12 n23 n24 n25 n26 Hb.
    destruct (sc_none tz uz i d f Li (eq_trans Hdecl (db_ncolon _ _ _ _ SP Hq eq_refl Hb))) as [E1 E2].
    rewrite E1, E2. eapply cont98; [exact LF | lia | lia | exact Hd | exact Hdw | reflexivity | exact MF0].
  - intros q2 n8 n10 n11 n12 n23 n24 n25 n26 Hq2 Hc H11 H23 H24 H8 H25 H26.
    subst n11 n23 n24 n8 n25 n26. unfold stL.
    assert (Q2 : (q2 < TL)%nat).
    { destruct (Nat.lt_ge_cases q2 TL) as [L|L]; [exact L|].
      rewrite byte_at_past in Hc by (rewrite zbytes_length; exact L). discriminate. }
    assert (Q12 : (q <= q2)%nat) by lia.
    eapply (sp2_loop (TL - S q2) _ m (S q2)); [reflexivity | lia | exact BT | weq | weq | weq | weq |].
    intros q3 z8 z10 z11 z24 z25 z26 Hq3 H10 H24' H8' H25' H26'. subst z10 z24 z8 z25 z26. unfold stL.
    assert (Q3 : (q3 <= TL)%nat).
    { pose proof (cw_le is_space (skipn (S q2) tz)) as C. rewrite length_skipn, zbytes_length in C. lia. }
    assert (Q23 : (S q2 <= q3)%nat) by lia.
    pose proof (byte_range tb q3) as Rc3.
    zstep. zstep.
    if_cases HC1; rewrite beq_lit in HC1 by lia.
    + assert (Hl : byte_at tz q3 <> 60) by bcontra.
      destruct (sc_none tz uz i d f Li (eq_trans Hdecl (db_nlt _ _ _ _ _ SP Hq Hq2 Hc Hq3 Hl))) as [E1 E2].
      rewrite E1, E2. eapply cont98; [exact LF | lia | lia | exact Hd | exact Hdw | reflexivity | exact MF0].
    + assert (Hlt : byte_at tz q3 = 60) by bcontra.
      assert (Q3' : (q3 < TL)%nat).
      { destruct (Nat.lt_ge_cases q3 TL) as [L|L]; [exact L|].
        rewrite byte_at_past in Hlt by (rewrite zbytes_length; exact L). discriminate. }
      zstep. zstep. zstep.
      eapply evt_cut.
      { eapply CHR.
        - eapply (cstr_at_w m _ (bv_unsigned txt) tb ts (S q3) BT NZT ALT); [lia | rewrite unsigned_lit by lia; lia].
        - replace (bv_unsigned (Z_to_bv 64 62)) with 62 by reflexivity. lia.
        - exact MI.
        - rewrite u_sp1. exact ST.
        - unfold STRCHR_K. rewrite u_sp1. lia.
        - unfold off_stack, STRCHR_K. rewrite u_sp1, unsigned_lit by lia. rewrite length_skipn. lia. }
      clear MF0. kpost.
      replace (bv_unsigned (Z_to_bv 64 62)) with 62 in PO by reflexivity.
      rewrite zbytes_skipn in PO.
      rewrite (unsigned_lit (bv_unsigned txt + Z.of_nat q3 + 1)) in PO by lia.
      match type of PO with ?r = _ => rename r into rr end.
      destruct (find_idx (fun c => c =? 62) (skipn (S q3) tz)) as [o|] eqn:FI.
      * subst rr.
        pose proof (find_idx_lt _ _ _ FI) as Ho. rewrite length_skipn, zbytes_length in Ho.
        zstep. if_cases HC2; rewrite eqb0, unsigned_lit in HC2 by lia; [exfalso; bcontra|].
        zstep.
        assert (Hdf : decl tz i = DFound q (q2 - q) (S q3) o (S q3 + o)).
        { rewrite Hdecl, (db_res _ _ _ _ _ SP Hq Hq2 Hc Hq3 Hlt), FI. reflexivity. }
        eapply (match_part f i d q (q2 - q) (S q3) o (S q3 + o));
          [exact LF | lia | lia | exact Hd | exact Hdw | exact Hdf | lia | lia | reflexivity | lia
          | weq | weq | weq | weq | weq | weq | weq | weq | close_mf].
      * subst rr. zstep. if_cases HC2; [|litbad HC2].
        zstep.
        assert (Hdc : decl tz i = DCut) by (rewrite Hdecl, (db_res _ _ _ _ _ SP Hq Hq2 Hc Hq3 Hlt), FI; reflexivity).
        destruct (sc_cut tz uz i d f Li Hdc) as [E1 E2]. rewrite E1, E2.
        eapply epi. close_mf.
Qed.

Lemma from_p0 : forall f i d p0 m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  LoopAt f -> (i < TL)%nat -> (TL - i < S f)%nat -> (d <= 16)%nat -> dw = Z_to_bv 64 (Z.of_nat d) ->
  head tz i = Some p0 -> (i < p0 <= TL)%nat ->
  x21 = Z_to_bv 64 (bv_unsigned txt + Z.of_nat i) -> a1 = Z_to_bv 64 (Z.of_nat (p0 - i)) ->
  mfacts m dw v ->
  evt rsegs (POSTv (scan tz uz i d (S f)) (readings tz uz i d (S f)) v)
    (stL 0x13da4 m ra' t0 t1 t2 (Z_to_bv 64 64) a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros f i d p0 m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6
    LF Hi Hf Hd Hdw Hh Hp0 H21 Ha1 MF.
  subst x21 a1. pose proof MF as MF0. open_mf MF. unfold stL.
  pose proof (decl_some _ _ _ Hh) as Hdecl.
  assert (Li : (i < length tz)%nat) by (rewrite zbytes_length; exact Hi).
  pose proof (byte_range tb p0) as Rc.
  pose proof (rd_byte m (bv_unsigned txt) tb ts p0 BT ltac:(lia)) as HR.
  zstep. zstep. u8fix. zstep. zstep.
  if_cases HC1; rewrite (sp_lt _ Rc) in HC1.
  - zstep. if_cases HC2; rewrite beq_lit in HC2 by lia.
    + eapply (from_sp f i d p0); [exact LF | exact Hi | exact Hf | exact Hd | exact Hdw | exact Hdecl | exact Hp0
        | unfold is_space; rewrite HC2; reflexivity | reflexivity | reflexivity | reflexivity | weq | exact MF0].
    + zstep.
      assert (SP : is_space (byte_at tz p0) = false).
      { unfold is_space. rewrite HC2. destruct ((9 <=? byte_at tz p0) && (byte_at tz p0 <=? 13)); [discriminate HC1|reflexivity]. }
      destruct (sc_none tz uz i d f Li (eq_trans Hdecl (db_nsp _ _ SP))) as [E1 E2]. rewrite E1, E2.
      eapply cont9c; [exact LF | lia | lia | exact Hd | exact Hdw | reflexivity | exact MF0].
  - assert (H913 : (9 <=? byte_at tz p0) && (byte_at tz p0 <=? 13) = true)
      by (destruct ((9 <=? byte_at tz p0) && (byte_at tz p0 <=? 13)); [reflexivity | discriminate HC1]).
    eapply (from_sp f i d p0); [exact LF | exact Hi | exact Hf | exact Hd | exact Hdw | exact Hdecl | exact Hp0
      | unfold is_space; rewrite H913; apply orb_true_r | reflexivity | reflexivity | reflexivity | weq | exact MF0].
Qed.

Lemma iter : forall f, LoopAt f -> LoopAt (S f).
Proof.
  intros f LF. red.
  intros i d m dw v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6 Hi Hf Hd Hdw H21 MF.
  subst x21. pose proof MF as MF0. open_mf MF. unfold stL.
  pose proof (rd_byte m (bv_unsigned txt) tb ts i BT Hi) as HR.
  pose proof (byte_range tb i) as Rc.
  zstep. u8fix.
  destruct (Nat.eq_dec i TL) as [Ei|Ei].
  - assert (B0 : byte_at tz i = 0) by (apply byte_at_past; rewrite zbytes_length; lia).
    rewrite B0. zstep.
    if_cases HC1; [litbad HC1|].
    zstep. if_cases HC2; [|litbad HC2].
    zstep.
    destruct (sc_end tz uz i d f ltac:(rewrite zbytes_length; lia)) as [E1 E2]. rewrite E1, E2.
    eapply epi. exact MF0.
  - assert (Hlt : (i < TL)%nat) by lia.
    assert (Li : (i < length tz)%nat) by (rewrite zbytes_length; exact Hlt).
    pose proof (byte_nz tb i NZT Hlt) as Bnz.
    zstep.
    if_cases HC1; rewrite beq_lit in HC1 by lia.
    + assert (B64 : byte_at tz i = 64) by bcontra.
      do 4 zstep.
      eapply evt_cut.
      { eapply NCMP.
        - eapply (cstr0_w m _ (bv_unsigned txt) tb ts (S i) BT NZT); [lia | rewrite unsigned_lit by lia; lia].
        - replace (bv_unsigned (Z_to_bv 64 66582)) with 66582 by reflexivity. apply cstr0_pl. exact PL.
        - exact MI.
        - rewrite u_sp1. exact ST. }
      clear MF0. kpost.
      change (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) with 6%nat in PO.
      rewrite pl_eq, zbytes_skipn in PO.
      pose proof (iff_trans PO (ncmp6 _ (Forall_skipn_z _ _ (S i) (zbytes_nz tb NZT)))) as PO'. clear PO.
      match type of PO' with (bv_unsigned ?r = 0 <-> _) => rename r into rr end.
      zstep.
      if_cases HC2; rewrite eqb0 in HC2.
      * assert (ZL : zl_eqb (firstn 6 (skipn (S i) tz)) prefix_lc = true) by (apply PO'; bcontra).
        assert (Hh : head tz i = Some (i + 7)%nat) by (rewrite (head_at _ _ Li B64), ZL; reflexivity).
        assert (L7 : (i + 7 <= TL)%nat).
        { apply zl_eqb_eq in ZL. apply (f_equal (@length _)) in ZL.
          rewrite length_firstn, length_skipn, zbytes_length in ZL. change (length prefix_lc) with 6%nat in ZL. lia. }
        zstep.
        eapply (from_p0 f i d (i + 7)); [exact LF | exact Hlt | lia | exact Hd | exact Hdw | exact Hh | lia
          | reflexivity | weq | close_mf].
      * assert (ZL : zl_eqb (firstn 6 (skipn (S i) tz)) prefix_lc = false)
          by (apply not_true_is_false; intro E; apply PO' in E; bcontra).
        assert (Hh : head tz i = None) by (rewrite (head_at _ _ Li B64), ZL; reflexivity).
        eapply (ncase_path _ i m dw v); [exact Hlt | close_mf | reflexivity | |].
        -- intros _ m' ra'' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MF'.
           destruct (sc_none tz uz i d f Li (decl_none _ _ Hh)) as [E1 E2]. rewrite E1, E2.
           eapply cont9c; [exact LF | lia | lia | exact Hd | exact Hdw | reflexivity | exact MF'].
        -- intros Hc. exfalso. rewrite (ci_at64 _ _ Li B64) in Hc. discriminate.
    + zstep. if_cases HC2; rewrite beq_lit in HC2 by lia; [exfalso; bcontra|].
      zstep.
      eapply (ncase_path _ i m dw v); [exact Hlt | exact MF0 | reflexivity | |].
      * intros Hc m' ra'' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MF'.
        assert (Hh : head tz i = None) by (rewrite head_nat by bcontra; rewrite Hc; reflexivity).
        destruct (sc_none tz uz i d f Li (decl_none _ _ Hh)) as [E1 E2]. rewrite E1, E2.
        eapply cont9c; [exact LF | lia | lia | exact Hd | exact Hdw | reflexivity | exact MF'].
      * intros Hc m' ra'' u0 u1 u2 b0 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MF'.
        assert (Hh : head tz i = Some (i + 6)%nat) by (rewrite head_nat by bcontra; rewrite Hc; reflexivity).
        assert (L6 : (i + 6 <= TL)%nat).
        { apply andb_true_iff in Hc as [Hc _]. apply ci_len in Hc.
          rewrite length_firstn, length_skipn, zbytes_length in Hc. change (length prefix_lc) with 6%nat in Hc. lia. }
        eapply (from_p0 f i d (i + 6)); [exact LF | exact Hlt | lia | exact Hd | exact Hdw | exact Hh | lia
          | reflexivity | weq | exact MF'].
Qed.

Lemma scan_loop : forall f, LoopAt f.
Proof.
  induction f as [|f IH].
  - red. intros. exfalso. lia.
  - apply iter. exact IH.
Qed.

Lemma loop_start : forall m v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x26 t3 t4 t5 t6,
  mfacts m (Z_to_bv 64 0) v ->
  evt rsegs (POSTv (scan tz uz 0 0 (S TL)) (readings tz uz 0 0 (S TL)) v)
    (stL 0x13d44 m ra' t0 t1 t2 (Z_to_bv 64 64) a0 a1 a2 a3 a4 a5 a6 a7 txt x22 x23 x24 x25 x26 t3 t4 t5 t6).
Proof.
  intros m v ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 x25 x26 t3 t4 t5 t6 MF.
  eapply (scan_loop (S TL)); [lia | lia | lia | reflexivity | | exact MF].
  cbn [Z.of_nat]. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

End Scan.

Theorem readings_scan_holds : strlen_contract -> strncmp_contract -> strncasecmp_contract -> strchr_contract ->
  isalnum_contract -> has_prefixed_contract -> readings_scan_contract.
Proof.
  intros LEN NCMP NCASE CHR ALNUM HP. unfold readings_scan_contract, READINGS_SCAN.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 sp1 t0 t1 t2 rp uri a0 a1 a2 a3 a4 a5 a6 a7 txt un
    x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 v F fc m lo junk tb ts ub us
    Hsp1 FR MI ST LO CT CU UNE Hun T0 TL63 U0 RPB RPW PL PU GCl [g GWd] GW8 GC8 OT OU ORP OPL OPU DJ.
  unfold READINGS_K, READINGS_FRAME, HAS_PREFIXED_K, PREFIX_LC_AT, PREFIX_UC_AT in *.
  change (176 + (112 + 2256)) with 2544 in *. change (112 + 2256) with 2368 in *.
  replace (bv_unsigned sp - 176) with (bv_unsigned sp + -176) in * by lia.
  subst sp1 un.
  destruct CT as [BT [NZT ALT]]. destruct CU as [BU [NZU ALU]].
  unfold prefix_lc in PL. unfold prefix_uc in PU. cbn [map app] in PL, PU.
  unfold off_stack in OT, OU, ORP, OPL, OPU.
  cbn [disjoint_from] in DJ. destruct DJ as (DT & DU & DPL & DPU & DGC & DGW & _).
  pose proof (zr_word sp) as SPR. unfold inr64 in SPR. destruct SPR as [_ SPR].
  pose proof (proj1 ST) as LO0.
  assert (TXR : bv_unsigned txt + Z.of_nat (length tb + 1 + length ts) <= 2^64).
  { pose proof (bytes_at_bound _ _ _ _ BT) as B. rewrite length_app in B. cbn [length] in B. lia. }
  assert (URR : bv_unsigned uri + Z.of_nat (length ub + 1 + length us) <= 2^64).
  { pose proof (bytes_at_bound _ _ _ _ BU) as B. rewrite length_app in B. cbn [length] in B. lia. }
  assert (RPR : 0 <= bv_unsigned rp /\ bv_unsigned rp + 8 <= 2^64).
  { pose proof (bytes_at_bound _ _ _ _ RPB) as B. rewrite length_le8 in B. cbn in B. lia. }
  assert (RP : rw_cells rsegs m (bv_unsigned rp) [C8 v]).
  { split; [split; [split; [exact I | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact RPB] |].
    cbn [cells_size csize]. exact RPW. }
  clear RPB RPW.
  pose proof (munch_refl [(bv_unsigned sp - 2544, bv_unsigned sp); (bv_unsigned rp, bv_unsigned rp + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 25 zstep.
  eapply loop_start; try eassumption.
  unfold mfacts, frame. repeat (split; [eassumption|]). eassumption.
Qed.
