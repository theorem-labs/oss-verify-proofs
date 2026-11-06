From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocBound AllocPack AllocPackRoom.
Import ListNotations.
Local Open Scope Z_scope.

Definition zlen {A : Type} (l : list A) : Z := Z.of_nat (length l).

Definition sp_byte (d : list Z) (k : Z) : Z := nth (Z.to_nat k) d 0.

Definition sp_rd (d : list Z) (k : Z) : Z * Z := if k <? zlen d then (sp_byte d k, k + 1) else (0, k).

Definition sp_pick (op : Z) : bool := (op =? 1) || (op =? 2) || (op =? 3) || (op =? 4) || (op =? 6).

Record ck := CK { ck_op : Z; ck_at : Z; ck_data : list Z }.

Definition ck_end (c : ck) : Z := ck_at c + zlen (ck_data c).

Definition sp_take (d : list Z) (op k : Z) : Z * option ck :=
  let k1 := snd (sp_rd d k) in
  let k2 := snd (sp_rd d k1) in
  let m := Z.min (fst (sp_rd d k) + 256 * fst (sp_rd d k1)) (zlen d - k2) in
  (k2 + m, Some (CK op k2 (firstn (Z.to_nat m) (skipn (Z.to_nat k2) d)))).

Definition sp_pass (d : list Z) (k : Z) : Z * option ck :=
  let op := sp_byte d k mod 10 in
  if sp_pick op then
    if op =? 1 then sp_take d 1 (snd (sp_rd d (k + 1))) else (snd (sp_rd d (k + 1)), None)
  else if op =? 7 then sp_take d 7 (k + 1)
  else if op =? 0 then (k + 1, None)
  else (snd (sp_rd d (k + 1)), None).

Fixpoint sp_walk (d : list Z) (fuel : nat) (k : Z) : list ck :=
  match fuel with
  | O => []
  | S f =>
      if k <? zlen d then
        match snd (sp_pass d k) with
        | Some c => c :: sp_walk d f (fst (sp_pass d k))
        | None => sp_walk d f (fst (sp_pass d k))
        end
      else []
  end.

Definition plz (pl : list byte) : list Z := map (fun b => bv_unsigned b) pl.

Lemma pl_chunks_sig (pl : list byte) : { cs : list ck | cs = sp_walk (plz pl) 512 0 }.
Proof. exists (sp_walk (plz pl) 512 0). reflexivity. Qed.

Definition pl_chunks (pl : list byte) : list ck := proj1_sig (pl_chunks_sig pl).

Lemma pl_chunks_eq pl : pl_chunks pl = sp_walk (plz pl) 512 0.
Proof. unfold pl_chunks. exact (proj2_sig (pl_chunks_sig pl)). Qed.

Fixpoint zsegs (d : list Z) : list (list Z) :=
  match d with
  | [] => [[]]
  | b :: d' =>
      if b =? 0 then [] :: zsegs d'
      else match zsegs d' with
           | s :: ss => (b :: s) :: ss
           | [] => [[b]]
           end
  end.

Definition inner_segs (d : list Z) : list (list Z) := removelast (tl (zsegs d)).

Fixpoint nzlen (d : list Z) : nat :=
  match d with
  | [] => O
  | b :: d' => if b =? 0 then O else S (nzlen d')
  end.

Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && zl_eqb a' b'
  | _, _ => false
  end.

Definition GVERB : list Z := [112; 97; 114; 97; 109; 95; 103; 101; 115; 116; 117; 114; 101; 32].

Definition GBEGIN : list Z := [32; 98; 101; 103; 105; 110].

Definition begin_line (l : list Z) : bool :=
  (20 <=? zlen l) && zl_eqb (firstn 14 l) GVERB && zl_eqb (skipn (length l - 6) l) GBEGIN.

Definition LLIM : Z := 6000.

Definition line_copies (l : list Z) : list Z :=
  if zlen l <=? LLIM then (zlen l + 1) :: (if begin_line l then [zlen l - 5; zlen l - 5] else []) else [].

Definition ck_copies (c : ck) : list Z :=
  if ck_op c =? 7 then [Z.of_nat (nzlen (ck_data c)) + 1]
  else (zlen (ck_data c) + 1) :: flat_map line_copies (inner_segs (ck_data c)).

Definition xcount (c : Z) (cs : list ck) : Z := zlen (filter (fun r => band r =? c) (flat_map ck_copies cs)).

Definition x_c (c : Z) (pl : list byte) : Z := xcount c (pl_chunks pl).

Definition band_lo (c : Z) : Z :=
  if c =? 0 then 0 else if c =? 48 then MMAP_THRESHOLD else UNIT * znth (c - 1) size_classes - (IB - 1).

Definition BTEXT : Z := 512 * 65535.

Lemma band_units n : 0 <= n < MMAP_THRESHOLD ->
  band n = class_of_units (Z.shiftr (n + IB - 1) 4) /\ 0 <= Z.shiftr (n + IB - 1) 4 < 8191 /\
  16 * Z.shiftr (n + IB - 1) 4 <= n + 3 < 16 * Z.shiftr (n + IB - 1) 4 + 16.
Proof.
  intros Hn. unfold band. destruct (Z.leb_spec MMAP_THRESHOLD n) as [H|H]; [lia|].
  unfold size_to_class. split; [reflexivity|].
  rewrite Z.shiftr_div_pow2 by lia. unfold MMAP_THRESHOLD, IB in *. change (2 ^ 4) with 16.
  pose proof (Z.mul_div_le (n + 4 - 1) 16 ltac:(lia)).
  pose proof (Z.mul_succ_div_gt (n + 4 - 1) 16 ltac:(lia)).
  split; [split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]|]. lia.
Qed.

Lemma band_lo_le n : 0 <= n -> band_lo (band n) <= n.
Proof.
  intros Hn. destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hs|Hs].
  - destruct (band_units n (conj Hn Hs)) as (Eb & Hk & Hr). rewrite Eb.
    set (k := Z.shiftr (n + IB - 1) 4) in *.
    pose proof class_of_units_ok as HT. rewrite forallb_forall in HT.
    specialize (HT k (proj2 (In_zseq 0 8191 k) ltac:(lia))). cbv beta zeta in HT.
    set (c := class_of_units k) in *.
    apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (Z.eq_dec c 0) as [E|E]; [rewrite E; change (band_lo 0) with 0; lia|].
    assert (Hm : band_lo c = UNIT * znth (c - 1) size_classes - (IB - 1)).
    { unfold band_lo. rewrite (proj2 (Z.eqb_neq c 0) E), (proj2 (Z.eqb_neq c 48) ltac:(lia)). reflexivity. }
    rewrite Hm. rewrite (proj2 (Z.ltb_lt 0 c) ltac:(lia)) in H4. cbn [implb] in H4. apply Z.leb_le in H4.
    unfold UNIT, IB. lia.
  - unfold band. destruct (Z.leb_spec MMAP_THRESHOLD n) as [H|H]; [|lia].
    change (band_lo 48) with MMAP_THRESHOLD. lia.
Qed.

Lemma band0_le n : 0 <= n -> band n = 0 -> n <= 12.
Proof.
  intros Hn Hb. destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hs|Hs].
  - destruct (band_units n (conj Hn Hs)) as (Eb & Hk & Hr). rewrite Hb in Eb.
    set (k := Z.shiftr (n + IB - 1) 4) in *.
    pose proof class_of_units_ok as HT. rewrite forallb_forall in HT.
    specialize (HT k (proj2 (In_zseq 0 8191 k) ltac:(lia))). cbv beta zeta in HT.
    rewrite <- Eb in HT.
    apply andb_prop in HT as [HT _]. apply andb_prop in HT as [_ H3]. apply Z.ltb_lt in H3.
    change (znth 0 size_classes) with 1 in H3. lia.
  - revert Hb. unfold band. destruct (Z.leb_spec MMAP_THRESHOLD n); intros Hb; [discriminate|lia].
Qed.

Lemma band_lo_band c : 0 <= c < 49 -> band (band_lo c) = c.
Proof.
  intros Hc. assert (T : forallb (fun c => band (band_lo c) =? c) (zseq 0 49) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in T. apply Z.eqb_eq. apply T. apply In_zseq. lia.
Qed.

Lemma zsum_le' {A : Type} (f g : A -> Z) l : (forall x, In x l -> f x <= g x) -> zsum f l <= zsum g l.
Proof.
  induction l as [|x l IH]; intros H; [cbn; lia|]. rewrite !zsum_cons.
  pose proof (H x (or_introl eq_refl)).
  assert (zsum f l <= zsum g l) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsum_scale {A : Type} (a : Z) (f : A -> Z) l : zsum (fun x => a * f x) l = a * zsum f l.
Proof. induction l as [|x l IH]; [cbn; lia|]. rewrite !zsum_cons, IH. cbv beta. ring. Qed.

Lemma zsum_ffm {A : Type} (g : A -> list Z) (f : Z -> Z) l : zsum f (flat_map g l) = zsum (fun x => zsum f (g x)) l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [flat_map]. rewrite zsum_app, zsum_cons, IH. reflexivity. Qed.

Lemma zlen_ffm {A B : Type} (P : B -> bool) (g : A -> list B) l :
  zlen (filter P (flat_map g l)) = zsum (fun x => zlen (filter P (g x))) l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. change (flat_map g (x :: l)) with (g x ++ flat_map g l).
  rewrite zsum_cons, <- IH. cbv beta. unfold zlen. rewrite List.filter_app, length_app. lia.
Qed.

Lemma zsum_removelast_le {A : Type} (f : A -> Z) l : (forall x, 0 <= f x) -> zsum f (removelast l) <= zsum f l.
Proof.
  intros Hf. induction l as [|x l IH]; [cbn; lia|].
  destruct l as [|y l].
  - cbn [removelast]. rewrite zsum_cons, zsum_nil. pose proof (Hf x). lia.
  - change (removelast (x :: y :: l)) with (x :: removelast (y :: l)). rewrite !zsum_cons.
    rewrite zsum_cons in IH. lia.
Qed.

Lemma zsum_tl_le {A : Type} (f : A -> Z) l : (forall x, 0 <= f x) -> zsum f (tl l) <= zsum f l.
Proof. intros Hf. destruct l as [|x l]; cbn [tl]; [lia|]. rewrite zsum_cons. pose proof (Hf x). lia. Qed.

Lemma filter_len_le {A : Type} (f : A -> bool) l : (length (filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; [cbn; lia|]. cbn [filter]. destruct (f x); cbn [length]; lia. Qed.

Lemma firstn_len_le {A : Type} (n : nat) (l : list A) : (length (firstn n l) <= n)%nat.
Proof. revert l. induction n as [|n IH]; intros [|x l]; cbn [firstn length]; try lia. specialize (IH l). lia. Qed.

Lemma zsegs_ne d : zsegs d <> [].
Proof.
  destruct d as [|b d]; cbn; [discriminate|]. destruct (b =? 0); [discriminate|]. destruct (zsegs d); discriminate.
Qed.

Lemma zsegs_mass d : zsum (fun s => zlen s + 1) (zsegs d) = zlen d + 1.
Proof.
  induction d as [|b d IH]; [reflexivity|]. cbn [zsegs]. destruct (b =? 0).
  - rewrite zsum_cons, IH. unfold zlen. cbn [length]. lia.
  - revert IH. destruct (zsegs d) as [|s ss] eqn:E; intros IH; [exfalso; exact (zsegs_ne d E)|].
    rewrite zsum_cons in IH |- *. cbv beta in *. unfold zlen in *. cbn [length] in *. lia.
Qed.

Lemma zsegs_nozero d : forall s, In s (zsegs d) -> Forall (fun b => b <> 0) s.
Proof.
  induction d as [|b d IH]; intros s Hs.
  - destruct Hs as [<-|[]]. constructor.
  - revert Hs. cbn [zsegs]. destruct (b =? 0) eqn:Eb; intros Hs.
    + destruct Hs as [<-|Hs]; [constructor|exact (IH s Hs)].
    + apply Z.eqb_neq in Eb. revert IH Hs. destruct (zsegs d) as [|s0 ss]; intros IH Hs.
      * destruct Hs as [<-|[]]. constructor; [exact Eb|constructor].
      * destruct Hs as [<-|Hs].
        -- constructor; [exact Eb|]. apply IH. left. reflexivity.
        -- apply IH. right. exact Hs.
Qed.

Lemma nozero_zsegs p : Forall (fun b => b <> 0) p -> zsegs p = [p].
Proof.
  induction p as [|b p IH]; intros H; [reflexivity|].
  inversion H as [|b' p' Hb Hp]; subst. cbn [zsegs].
  rewrite (proj2 (Z.eqb_neq b 0) Hb), (IH Hp). reflexivity.
Qed.

Lemma tl_zsegs_nil r : tl (zsegs r) = [] -> Forall (fun b => b <> 0) r.
Proof.
  induction r as [|b r IH]; intros H; [constructor|].
  revert H. cbn [zsegs]. destruct (b =? 0) eqn:Eb; intros H.
  - cbn [tl] in H. exfalso. exact (zsegs_ne r H).
  - constructor; [apply Z.eqb_neq; exact Eb|]. apply IH.
    revert H. destruct (zsegs r) as [|s ss]; cbn [tl]; intros H; [reflexivity|exact H].
Qed.

Lemma last_in (s : list Z) (ss : list (list Z)) : In (last (s :: ss) []) (s :: ss).
Proof.
  revert s. induction ss as [|s' ss IH]; intros s; [left; reflexivity|].
  right. change (last (s :: s' :: ss) []) with (last (s' :: ss) []). apply IH.
Qed.

Lemma zsegs_app a b :
  zsegs (a ++ b) = removelast (zsegs a) ++ (last (zsegs a) [] ++ hd [] (zsegs b)) :: tl (zsegs b).
Proof.
  induction a as [|x a IH].
  - cbn [app zsegs removelast last]. destruct (zsegs b) as [|s ss] eqn:E; [exfalso; exact (zsegs_ne b E)|].
    reflexivity.
  - cbn [app zsegs]. destruct (x =? 0).
    + rewrite IH. destruct (zsegs a) as [|s ss] eqn:E; [exfalso; exact (zsegs_ne a E)|]. reflexivity.
    + rewrite IH. destruct (zsegs a) as [|s ss] eqn:E; [exfalso; exact (zsegs_ne a E)|].
      destruct ss as [|s2 ss]; reflexivity.
Qed.

Lemma inner_le (f : list Z -> Z) d : (forall s, 0 <= f s) -> zsum f (inner_segs d) <= zsum f (zsegs d).
Proof.
  intros Hf. unfold inner_segs. eapply Z.le_trans; [apply zsum_removelast_le; exact Hf|].
  apply zsum_tl_le; exact Hf.
Qed.

Lemma nzlen_le d : (nzlen d <= length d)%nat.
Proof. induction d as [|b d IH]; [cbn; lia|]. cbn [nzlen length]. destruct (b =? 0); lia. Qed.

Lemma begin_line_len l : begin_line l = true -> 20 <= zlen l.
Proof.
  unfold begin_line. intros H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply Z.leb_le. exact H.
Qed.

Lemma lc_req l r : In r (line_copies l) ->
  zlen l <= LLIM /\ (r = zlen l + 1 \/ (begin_line l = true /\ r = zlen l - 5)).
Proof.
  unfold line_copies. destruct (Z.leb_spec (zlen l) LLIM) as [HL|HL]; [|intros []].
  destruct (begin_line l) eqn:Eb.
  - intros [<-|[<-|[<-|[]]]].
    + split; [exact HL|left; reflexivity].
    + split; [exact HL|right; split; reflexivity].
    + split; [exact HL|right; split; reflexivity].
  - intros [<-|[]]. split; [exact HL|left; reflexivity].
Qed.

Lemma lc_mass l : zsum (fun r => r) (line_copies l) <= 3 * (zlen l + 1).
Proof.
  unfold line_copies. destruct (zlen l <=? LLIM); [|unfold zsum; cbn [fold_right]; unfold zlen; lia].
  destruct (begin_line l) eqn:Eb.
  - pose proof (begin_line_len l Eb). unfold zsum. cbn [fold_right]. unfold zlen in *. lia.
  - unfold zsum. cbn [fold_right]. unfold zlen. lia.
Qed.

Lemma lc_mass_le l : 0 <= zsum (fun r => r) (line_copies l) <= 3 * (LLIM + 1).
Proof.
  unfold line_copies. destruct (Z.leb_spec (zlen l) LLIM) as [HL|HL];
    [|unfold zsum; cbn [fold_right]; unfold LLIM; lia].
  destruct (begin_line l) eqn:Eb.
  - pose proof (begin_line_len l Eb). unfold zsum. cbn [fold_right]. unfold LLIM in *. lia.
  - unfold zsum. cbn [fold_right]. unfold zlen, LLIM in *. lia.
Qed.

Lemma lc_band0 l : zlen (filter (fun r => band r =? 0) (line_copies l)) <= 1.
Proof.
  unfold line_copies. destruct (zlen l <=? LLIM); [|unfold zlen; cbn [filter length]; lia].
  destruct (begin_line l) eqn:Eb.
  - pose proof (begin_line_len l Eb) as HL.
    assert (Hk : (band (zlen l - 5) =? 0) = false).
    { apply Z.eqb_neq. intros H0. pose proof (band0_le (zlen l - 5) ltac:(lia) H0). lia. }
    cbn [filter]. rewrite Hk. destruct (band (zlen l + 1) =? 0); unfold zlen; cbn [length]; lia.
  - cbn [filter]. destruct (band (zlen l + 1) =? 0); unfold zlen; cbn [length]; lia.
Qed.

Lemma ck_req c r : In r (ck_copies c) -> 0 <= r.
Proof.
  unfold ck_copies. destruct (ck_op c =? 7).
  - intros [<-|[]]. lia.
  - intros [<-|H]; [unfold zlen; lia|]. apply in_flat_map in H as (l & _ & Hl).
    destruct (lc_req l r Hl) as [_ [->|[Eb ->]]]; [unfold zlen; lia|]. pose proof (begin_line_len l Eb). lia.
Qed.

Lemma ck_mass c : zsum (fun r => r) (ck_copies c) <= 4 * (zlen (ck_data c) + 1).
Proof.
  unfold ck_copies. destruct (ck_op c =? 7).
  - unfold zsum. cbn [fold_right]. pose proof (nzlen_le (ck_data c)). unfold zlen. lia.
  - rewrite zsum_cons, zsum_ffm. cbv beta.
    assert (H1 : zsum (fun l => zsum (fun r => r) (line_copies l)) (inner_segs (ck_data c)) <=
                 zsum (fun l => 3 * (zlen l + 1)) (inner_segs (ck_data c))).
    { apply zsum_le'. intros l _. apply lc_mass. }
    rewrite zsum_scale in H1.
    pose proof (inner_le (fun l => zlen l + 1) (ck_data c) ltac:(intros s; cbv beta; unfold zlen; lia)) as H2.
    rewrite zsegs_mass in H2. lia.
Qed.

Lemma ck_band0 c : zlen (filter (fun r => band r =? 0) (ck_copies c)) <= zlen (ck_data c) + 2.
Proof.
  assert (E : forall x l, zlen (filter (fun r => band r =? 0) (x :: l)) <= 1 + zlen (filter (fun r => band r =? 0) l)).
  { intros x l. cbn [filter]. destruct (band x =? 0); unfold zlen; cbn [length]; lia. }
  unfold ck_copies. destruct (ck_op c =? 7).
  - eapply Z.le_trans; [apply E|]. cbn [filter]. unfold zlen. cbn [length]. lia.
  - eapply Z.le_trans; [apply E|]. rewrite zlen_ffm.
    assert (H1 : zsum (fun l => zlen (filter (fun r => band r =? 0) (line_copies l))) (inner_segs (ck_data c)) <=
                 zsum (fun l => zlen l + 1) (inner_segs (ck_data c))).
    { apply zsum_le'. intros l _. cbv beta. pose proof (lc_band0 l). unfold zlen in *. lia. }
    pose proof (inner_le (fun l => zlen l + 1) (ck_data c) ltac:(intros s; cbv beta; unfold zlen; lia)) as H2.
    rewrite zsegs_mass in H2. lia.
Qed.

Definition byte_ok (d : list Z) : Prop := Forall (fun v => 0 <= v < 256) d.

Lemma sp_byte_ok d k : byte_ok d -> 0 <= sp_byte d k < 256.
Proof.
  intros H. unfold sp_byte. destruct (Nat.lt_ge_cases (Z.to_nat k) (length d)) as [L|L].
  - unfold byte_ok in H. rewrite Forall_forall in H. apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma sp_rd_ok d k : byte_ok d -> 0 <= fst (sp_rd d k) < 256.
Proof. intros H. unfold sp_rd. destruct (k <? zlen d); cbn [fst]; [apply sp_byte_ok; exact H|lia]. Qed.

Lemma firstn_bound (n : Z) (l : list Z) : n <= 65535 -> zlen (firstn (Z.to_nat n) l) <= 65535.
Proof.
  intros Hn. pose proof (firstn_len_le (Z.to_nat n) l) as R. apply Nat2Z.inj_le in R. unfold zlen.
  destruct (Z_le_gt_dec 0 n) as [P|P].
  - rewrite (Z2Nat.id n P) in R. lia.
  - assert (E : Z.to_nat n = 0%nat) by (destruct n; [reflexivity|lia|reflexivity]).
    rewrite E. cbn [firstn length Z.of_nat]. apply Z.leb_le. reflexivity.
Qed.

Lemma sp_take_len d op k c' : byte_ok d -> snd (sp_take d op k) = Some c' -> zlen (ck_data c') <= 65535.
Proof.
  intros H E. unfold sp_take in E. cbv zeta in E. cbn [snd] in E. injection E as E. subst c'. cbn [ck_data].
  pose proof (sp_rd_ok d k H) as R1. pose proof (sp_rd_ok d (snd (sp_rd d k)) H) as R2.
  apply firstn_bound. eapply Z.le_trans; [apply Z.le_min_l|]. lia.
Qed.

Lemma sp_pass_len d k c' : byte_ok d -> snd (sp_pass d k) = Some c' -> zlen (ck_data c') <= 65535.
Proof.
  intros H. unfold sp_pass. cbv zeta.
  destruct (sp_pick (sp_byte d k mod 10));
    [destruct (sp_byte d k mod 10 =? 1)|destruct (sp_byte d k mod 10 =? 7); [|destruct (sp_byte d k mod 10 =? 0)]];
    intros E; cbn [snd] in E; first [discriminate E | exact (sp_take_len _ _ _ _ H E)].
Qed.

Lemma sp_walk_len d f k : (length (sp_walk d f k) <= f)%nat.
Proof.
  revert k. induction f as [|f IH]; intros k; [cbn; lia|]. cbn [sp_walk].
  destruct (k <? zlen d); [|cbn; lia]. specialize (IH (fst (sp_pass d k))).
  destruct (snd (sp_pass d k)); cbn [length]; lia.
Qed.

Lemma sp_walk_data d f k c : byte_ok d -> In c (sp_walk d f k) -> zlen (ck_data c) <= 65535.
Proof.
  intros H. revert k. induction f as [|f IH]; intros k Hin; [destruct Hin|]. revert Hin. cbn [sp_walk].
  destruct (k <? zlen d); [|intros []].
  destruct (snd (sp_pass d k)) as [c0|] eqn:E; intros Hin.
  - destruct Hin as [<-|Hin]; [exact (sp_pass_len d k c0 H E)|exact (IH _ Hin)].
  - exact (IH _ Hin).
Qed.

Lemma plz_ok pl : byte_ok (plz pl).
Proof.
  unfold byte_ok, plz. apply Forall_forall. intros v Hv. apply in_map_iff in Hv as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma pl_chunks_len pl : (length (pl_chunks pl) <= 512)%nat.
Proof. rewrite pl_chunks_eq. apply sp_walk_len. Qed.

Lemma pl_chunks_data pl c : In c (pl_chunks pl) -> zlen (ck_data c) <= 65535.
Proof. rewrite pl_chunks_eq. apply sp_walk_data. apply plz_ok. Qed.

Lemma mass_chunks cs : (forall c, In c cs -> zlen (ck_data c) <= 65535) ->
  zsum (fun r => r) (flat_map ck_copies cs) <= zlen cs * (4 * 65536).
Proof.
  rewrite zsum_ffm. induction cs as [|c cs IH]; intros H; [apply Z.le_refl|].
  rewrite zsum_cons. cbv beta. pose proof (ck_mass c). pose proof (H c (or_introl eq_refl)).
  assert (zsum (fun x => zsum (fun r => r) (ck_copies x)) cs <= zlen cs * (4 * 65536))
    by (apply IH; intros; apply H; right; assumption).
  unfold zlen in *. cbn [length]. lia.
Qed.

Lemma band0_chunks cs : (forall c, In c cs -> zlen (ck_data c) <= 65535) -> xcount 0 cs <= zlen cs * 65537.
Proof.
  unfold xcount. rewrite zlen_ffm. induction cs as [|c cs IH]; intros H; [apply Z.le_refl|].
  rewrite zsum_cons. cbv beta. pose proof (ck_band0 c). pose proof (H c (or_introl eq_refl)).
  assert (zsum (fun x => zlen (filter (fun r => band r =? 0) (ck_copies x))) cs <= zlen cs * 65537)
    by (apply IH; intros; apply H; right; assumption).
  unfold zlen in *. cbn [length]. lia.
Qed.

Definition wlo (r : Z) : Z := if (1 <=? band r) && (band r <=? 48) then band_lo (band r) else 0.

Lemma wsum_swap R : zsumZ (fun c => band_lo c * zlen (filter (fun r => band r =? c) R)) (zseq 1 48) = zsum wlo R.
Proof.
  induction R as [|r R IH].
  - apply zsumZ_zero. intros c _. cbv beta. unfold zlen. cbn [filter length]. change (Z.of_nat 0) with 0. ring.
  - rewrite zsum_cons, <- IH.
    transitivity (zsumZ (fun c => (if c =? band r then band_lo c else 0) +
      band_lo c * zlen (filter (fun r0 => band r0 =? c) R)) (zseq 1 48)).
    + apply zsumZ_ext. intros c _. cbv beta.
      assert (F : zlen (filter (fun r0 => band r0 =? c) (r :: R)) =
                  (if band r =? c then 1 else 0) + zlen (filter (fun r0 => band r0 =? c) R)).
      { cbn [filter]. destruct (band r =? c); cbv beta iota; unfold zlen; cbn [length]; lia. }
      rewrite F. destruct (Z.eqb_spec (band r) c) as [E|E].
      * subst c. rewrite Z.eqb_refl. cbv beta iota. ring.
      * rewrite (proj2 (Z.eqb_neq c (band r)) (fun X => E (eq_sym X))). cbv beta iota. ring.
    + rewrite zsumZ_add. apply (f_equal2 Z.add); [|reflexivity]. unfold wlo.
      destruct ((1 <=? band r) && (band r <=? 48)) eqn:Bd.
      * apply andb_prop in Bd as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
        apply (zsumZ_single band_lo (band r)); [apply zseq_NoDup|apply In_zseq; lia].
      * apply zsumZ_zero. intros c Hc. apply In_zseq in Hc. cbv beta.
        destruct (Z.eqb_spec c (band r)) as [Ec|_]; [|reflexivity]. exfalso.
        rewrite (proj2 (Z.leb_le 1 (band r)) ltac:(lia)), (proj2 (Z.leb_le (band r) 48) ltac:(lia)) in Bd.
        cbn in Bd. discriminate Bd.
Qed.

Lemma wlo_le r : 0 <= r -> wlo r <= r.
Proof. intros Hr. unfold wlo. destruct ((1 <=? band r) && (band r <=? 48)); [apply band_lo_le; exact Hr|lia]. Qed.

Theorem x_weighted pl : zsumZ (fun c => band_lo c * x_c c pl) (zseq 1 48) <= 4 * BTEXT + 2 ^ 20.
Proof.
  unfold x_c, xcount. rewrite wsum_swap.
  assert (H1 : zsum wlo (flat_map ck_copies (pl_chunks pl)) <= zsum (fun r => r) (flat_map ck_copies (pl_chunks pl))).
  { apply zsum_le'. intros r Hr. apply wlo_le. apply in_flat_map in Hr as (c & _ & Hc). exact (ck_req c r Hc). }
  pose proof (mass_chunks (pl_chunks pl) (pl_chunks_data pl)) as H2. pose proof (pl_chunks_len pl).
  unfold zlen in H2. unfold BTEXT. change (2 ^ 20) with 1048576. lia.
Qed.

Theorem x0_bound pl : x_c 0 pl <= BTEXT + 1024.
Proof.
  unfold x_c. pose proof (band0_chunks (pl_chunks pl) (pl_chunks_data pl)) as H. pose proof (pl_chunks_len pl).
  unfold zlen in H. unfold BTEXT. lia.
Qed.

Lemma x_nonneg c pl : 0 <= x_c c pl.
Proof. unfold x_c, xcount, zlen. lia. Qed.

Lemma xcount_nonneg c cs : 0 <= xcount c cs.
Proof. unfold xcount, zlen. lia. Qed.

Lemma xcount_filter_le c p cs : xcount c (filter p cs) <= xcount c cs.
Proof.
  unfold xcount. rewrite !zlen_ffm. induction cs as [|x cs IH]; [apply Z.le_refl|].
  cbn [filter]. destruct (p x); cbv beta iota; rewrite !zsum_cons; cbv beta; unfold zlen in *; lia.
Qed.

Lemma xcount_filter_mono c (p q : ck -> bool) cs : (forall x, p x = true -> q x = true) ->
  xcount c (filter p cs) <= xcount c (filter q cs).
Proof.
  intros H. unfold xcount. rewrite !zlen_ffm. induction cs as [|x cs IH]; [apply Z.le_refl|].
  cbn [filter]. destruct (p x) eqn:Ep; cbv beta iota.
  - rewrite (H x Ep). cbv beta iota. rewrite !zsum_cons. cbv beta. lia.
  - destruct (q x); cbv beta iota; [rewrite zsum_cons; cbv beta; unfold zlen in *; lia|exact IH].
Qed.

Fixpoint feed_recs (p : list Z) (rs : list (list Z)) : list (list Z) * list Z :=
  match rs with
  | [] => ([], p)
  | r :: rs' =>
      match tl (zsegs r) with
      | [] => feed_recs (p ++ r) rs'
      | ss => ((p ++ hd [] (zsegs r)) :: removelast ss ++ fst (feed_recs (last ss []) rs'),
               snd (feed_recs (last ss []) rs'))
      end
  end.

Lemma drain_lines rs : forall p, Forall (fun b => b <> 0) p ->
  zsegs (p ++ concat rs) = fst (feed_recs p rs) ++ [snd (feed_recs p rs)].
Proof.
  induction rs as [|r rs IH]; intros p Hp.
  - cbn [concat feed_recs fst snd app]. rewrite app_nil_r. exact (nozero_zsegs p Hp).
  - cbn [concat feed_recs]. destruct (tl (zsegs r)) as [|s ss] eqn:Et.
    + rewrite app_assoc. apply IH. apply Forall_app. split; [exact Hp|exact (tl_zsegs_nil r Et)].
    + cbn [fst snd]. revert Et. destruct (zsegs r) as [|h t] eqn:Er; intros Et; [discriminate Et|].
      cbn [tl] in Et. subst t.
      set (q := last (s :: ss) []).
      assert (Hq : Forall (fun b => b <> 0) q).
      { apply (zsegs_nozero r). rewrite Er. right. apply last_in. }
      assert (L1 : zsegs (p ++ r ++ concat rs) = (p ++ h) :: removelast (s :: ss) ++ zsegs (q ++ concat rs)).
      { rewrite (zsegs_app p), (nozero_zsegs p Hp), (zsegs_app r), Er, (zsegs_app q), (nozero_zsegs q Hq).
        reflexivity. }
      rewrite L1, (IH q Hq). change (hd [] (h :: s :: ss)) with h.
      rewrite <- app_comm_cons, <- app_assoc. reflexivity.
Qed.

Lemma stream_lines rs p : Forall (fun b => b <> 0) p ->
  removelast (zsegs (p ++ concat rs)) = fst (feed_recs p rs).
Proof. intros H. rewrite (drain_lines rs p H). apply removelast_last. Qed.

Lemma drain_cases rs : forall p l, In l (fst (feed_recs p rs)) ->
  (exists r, In r rs /\ In l (inner_segs r)) \/ (exists r q, In r rs /\ l = q ++ hd [] (zsegs r)).
Proof.
  induction rs as [|r rs IH]; intros p l Hl; [destruct Hl|].
  cbn [feed_recs] in Hl. revert Hl. destruct (tl (zsegs r)) as [|s ss] eqn:Et; intros Hl.
  - destruct (IH (p ++ r) l Hl) as [(r' & H1 & H2)|(r' & q & H1 & H2)].
    + left. exists r'. split; [right; exact H1|exact H2].
    + right. exists r', q. split; [right; exact H1|exact H2].
  - cbn [fst] in Hl. destruct Hl as [<-|Hl].
    + right. exists r, p. split; [left; reflexivity|reflexivity].
    + apply in_app_or in Hl as [Hl|Hl].
      * left. exists r. split; [left; reflexivity|]. unfold inner_segs. rewrite Et. exact Hl.
      * destruct (IH _ l Hl) as [(r' & H1 & H2)|(r' & q & H1 & H2)].
        -- left. exists r'. split; [right; exact H1|exact H2].
        -- right. exists r', q. split; [right; exact H1|exact H2].
Qed.

Lemma drain_weight (w : list Z -> Z) (Wb : Z) rs : (forall l, 0 <= w l <= Wb) -> forall p,
  zsum w (fst (feed_recs p rs)) <= zsum (fun r => zsum w (inner_segs r) + Wb) rs.
Proof.
  intros Hw. induction rs as [|r rs IH]; intros p; [apply Z.le_refl|].
  cbn [feed_recs]. rewrite zsum_cons. cbv beta.
  assert (N : 0 <= zsum w (inner_segs r)) by (apply zsum_nonneg; intros x _; exact (proj1 (Hw x))).
  pose proof (Hw []) as W0.
  destruct (tl (zsegs r)) as [|s ss] eqn:Et.
  - cbn [fst]. pose proof (IH (p ++ r)). lia.
  - cbn [fst]. rewrite zsum_cons, zsum_app.
    pose proof (Hw (p ++ hd [] (zsegs r))) as H3.
    assert (E : inner_segs r = removelast (s :: ss)) by (unfold inner_segs; rewrite Et; reflexivity).
    rewrite E in N |- *. pose proof (IH (last (s :: ss) [])). lia.
Qed.

Definition lc_count (P : Z -> bool) (l : list Z) : Z := zlen (filter P (line_copies l)).

Lemma lc_le3 P l : 0 <= lc_count P l <= 3.
Proof.
  unfold lc_count, zlen. pose proof (filter_len_le P (line_copies l)).
  assert (length (line_copies l) <= 3)%nat
    by (unfold line_copies; destruct (zlen l <=? LLIM); [destruct (begin_line l)|]; cbn [length]; lia).
  lia.
Qed.

Lemma drain_copies rs p (P : Z -> bool) :
  zsum (lc_count P) (fst (feed_recs p rs)) <= zsum (fun r => zsum (lc_count P) (inner_segs r) + 3) rs.
Proof. apply drain_weight. intros l. apply lc_le3. Qed.

Definition lmass (l : list Z) : Z := zsum (fun r => r) (line_copies l).

Theorem drain_mass rs p : Forall (fun b => b <> 0) p ->
  zsum lmass (removelast (zsegs (p ++ concat rs))) <= zsum (fun r => zsum lmass (inner_segs r) + 3 * (LLIM + 1)) rs.
Proof. intros Hp. rewrite (stream_lines rs p Hp). apply drain_weight. intros l. apply lc_mass_le. Qed.

Theorem drain_band rs p c : Forall (fun b => b <> 0) p ->
  zlen (filter (fun r => band r =? c) (flat_map line_copies (removelast (zsegs (p ++ concat rs))))) <=
  zsum (fun r => zlen (filter (fun r0 => band r0 =? c) (flat_map line_copies (inner_segs r))) + 3) rs.
Proof.
  intros Hp. rewrite (stream_lines rs p Hp), zlen_ffm.
  eapply Z.le_trans; [exact (drain_copies rs p (fun r => band r =? c))|].
  apply zsum_le'. intros r _. cbv beta. rewrite zlen_ffm. apply Z.le_refl.
Qed.
