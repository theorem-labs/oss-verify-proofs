From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require RelayRep HarnessRep op_add_c relay_add_b_c.
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition RI_BASE : Z := 4.

Definition NC_MAX : nat := 26.

Definition WILD_B : Z := 3 * (LLIM + 1).

Definition CONSB_MAX : Z := 512 * (4 * 65536) + 512 * WILD_B.

Definition ALSUM_MAX : Z := BTEXT + 1024 + 49 * 1536.

Definition PB3_MAX : Z := PDRV_BYTES + NC_FIX + NC_PER * ALSUM_MAX + DATA_PER * BTEXT + CONSB_MAX.

Definition CF_MAX : Z := 4131000000.

Definition done_ck (k : Z) (x : ck) : bool := ck_end x <=? k.

Definition done1 (k : Z) (x : ck) : bool := done_ck k x && (ck_op x =? 1).

Definition cmass (x : ck) : Z := zsum (fun r => r) (ck_copies x).

Definition cons_c (pl : list byte) (k c : Z) : Z :=
  xcount c (filter (done_ck k) (pl_chunks pl)) + 3 * zlen (filter (done1 k) (pl_chunks pl)).

Definition consb (pl : list byte) (k : Z) : Z :=
  zsum cmass (filter (done_ck k) (pl_chunks pl)) + WILD_B * zlen (filter (done1 k) (pl_chunks pl)).

Definition cdat (pl : list byte) (k : Z) : Z := zsum (fun x => zlen (ck_data x)) (filter (done1 k) (pl_chunks pl)).

Definition alsum (al : list Z) : Z := zsumZ (fun c => znth c al) (zseq 0 49).

Definition rec_cred (c : Z) (r : list byte) : Z :=
  zlen (filter (fun q => band q =? c) (flat_map line_copies (inner_segs (plz r)))) + 3.

Definition rec_credb (r : list byte) : Z := zsum lmass (inner_segs (plz r)) + WILD_B.

Definition prom_c (P : list (list (list byte))) (c : Z) : Z := zsum (fun rs => zsum (rec_cred c) rs) P.

Definition promb (P : list (list (list byte))) : Z := zsum (fun rs => zsum rec_credb rs) P.

Definition nc_has (L : layout) (A : astate) (c q : Z) : bool :=
  existsb (fun t => (fst t =? q) && (band (snd t) =? c)) (blocks L A).

Definition nc_cnt (V : rview) (L : layout) (A : astate) (c : Z) : Z := zlen (filter (nc_has L A c) (rv_nc V)).

Definition nc_sz (L : layout) (A : astate) (q : Z) : Z := zsum snd (filter (fun t => fst t =? q) (blocks L A)).

Definition ncs (V : rview) (L : layout) (A : astate) : Z := zsum (nc_sz L A) (rv_nc V).

Definition mis_addrs (L : layout) (M : list (sptr * Z)) : list Z := map (fun e => ptr_addr L (fst e)) M.

Definition mis_nc (V : rview) (L : layout) (M : list (sptr * Z)) : Prop :=
  incl (mis_addrs L M) (rv_nc V) /\ List.NoDup (mis_addrs L M).

Definition one_if (c d : Z) : Z := if c =? d then 1 else 0.

Definition ek_c (V : rview) (c : Z) : Z := zsum (fun n => one_if c (band n)) (rv_ek V).

Definition ek_b (V : rview) : Z := zsum (fun n => n) (rv_ek V).

Definition RI3_ledger (NW : rview -> Z) (pl : list byte) (k : Z) (V : rview) (L : layout) (A : astate) (b : pbound3)
    (al : list Z) (alb : Z) : Prop :=
  p3_cap b = CS_reply pl /\ p3_mcap b = MC_reply /\ (length (rv_nc V) <= NC_MAX)%nat /\
  length (p3_live b) = 49%nat /\ length al = 49%nat /\ 0 <= alb /\ Forall (fun n => 0 <= n) (rv_ek V) /\
  p3_bytes b <= PDRV_BYTES + ncs V L A + alb /\ ncs V L A <= NW V /\
  NW V <= NC_FIX + NC_PER * alsum al + DATA_PER * cdat pl k /\
  alb + ek_b V + promb (rv_pend V) <= consb pl k /\
  mis_nc V L (p3_mis b) /\
  forall c, 0 <= c < 49 ->
    znth c (p3_live b) <= RI_BASE + nc_cnt V L A c + znth c al /\ 0 <= znth c al /\
    znth c al + ek_c V c + prom_c (rv_pend V) c <= cons_c pl k c.

Definition RI3_reply : res_inv := fun E k V L A =>
  exists b al alb, res_ok_pack3 A b /\ RI3_ledger rv_wt (ss_pl E) k V L A b al alb.

Definition copy_step (NW : rview -> Z) (pl : list byte) (k' : Z) (V : rview) (L : layout) (A : astate) (V' : rview)
    (L' : layout) (A' : astate) (al : list Z) (alb n : Z) : Prop :=
  (length (rv_nc V') <= NC_MAX)%nat /\
  (forall c, 0 <= c < 49 -> nc_cnt V L A c <= nc_cnt V' L' A' c) /\ ncs V L A <= ncs V' L' A' /\
  ncs V' L' A' <= NW V' /\ NW V' <= NC_FIX + NC_PER * (alsum al + 1) + DATA_PER * cdat pl k' /\
  (forall c, 0 <= c < 49 -> znth c al + one_if c (band n) + ek_c V' c + prom_c (rv_pend V') c <= cons_c pl k' c) /\
  alb + n + ek_b V' + promb (rv_pend V') <= consb pl k' /\ Forall (fun n => 0 <= n) (rv_ek V').

Definition nc_step (NW : rview -> Z) (pl : list byte) (k' : Z) (V : rview) (L : layout) (A : astate) (V' : rview)
    (L' : layout) (A' : astate) (al : list Z) (alb : Z) (dl : Z -> Z) (db : Z) : Prop :=
  (length (rv_nc V') <= NC_MAX)%nat /\
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + dl c <= nc_cnt V' L' A' c) /\ ncs V L A + db <= ncs V' L' A' /\
  ncs V' L' A' <= NW V' /\ NW V' <= NC_FIX + NC_PER * alsum al + DATA_PER * cdat pl k' /\
  (forall c, 0 <= c < 49 -> znth c al + ek_c V' c + prom_c (rv_pend V') c <= cons_c pl k' c) /\
  alb + ek_b V' + promb (rv_pend V') <= consb pl k' /\ Forall (fun n => 0 <= n) (rv_ek V').

Lemma nc_wt_nil : nc_wt [] [] = NC_FIX.
Proof. unfold nc_wt, NC_FIX. cbn [length Z.of_nat]. rewrite !zsum_nil. lia. Qed.

Lemma nw_src_new fd q pj : nw_src (op_add_c.new_src fd q pj) = NW_SRC0.
Proof. reflexivity. Qed.

Lemma nw_list_size l : 16 * HarnessRep.hl_cap l <= nw_list l.
Proof. unfold nw_list. lia. Qed.

Lemma nw_list_push l l' : HarnessRep.hl_cap l' = HarnessRep.hl_cap l ->
  HarnessRep.hl_n l' = HarnessRep.hl_n l + 1 -> nw_list l' <= nw_list l + NC_PER.
Proof. intros H1 H2. unfold nw_list, NC_PER. rewrite H1, H2. lia. Qed.

Lemma nw_list_grow l l' : HarnessRep.hl_n l = HarnessRep.hl_cap l -> 0 <= HarnessRep.hl_cap l ->
  HarnessRep.hl_n l' = HarnessRep.hl_n l ->
  HarnessRep.hl_cap l' = (if HarnessRep.hl_cap l =? 0 then 8 else 2 * HarnessRep.hl_cap l) -> nw_list l' <= nw_list l.
Proof.
  intros H1 H0 H2 H3. unfold nw_list, NC_PER. rewrite H2, H3, H1.
  destruct (Z.eqb_spec (HarnessRep.hl_cap l) 0); lia.
Qed.

Lemma nw_list_drop l l' : HarnessRep.hl_cap l' = HarnessRep.hl_cap l ->
  HarnessRep.hl_n l' <= HarnessRep.hl_n l -> nw_list l' <= nw_list l.
Proof. intros H1 H2. unfold nw_list, NC_PER. rewrite H1. lia. Qed.

Lemma zlen_filter_mono {X : Type} (p q : X -> bool) l : (forall x, p x = true -> q x = true) ->
  zlen (filter p l) <= zlen (filter q l).
Proof.
  intros H. induction l as [|x l IH]; [apply Z.le_refl|]. cbn [filter]. destruct (p x) eqn:Ep.
  - rewrite (H x Ep). cbv beta iota. unfold zlen in *. cbn [length]. lia.
  - destruct (q x); cbv beta iota; unfold zlen in *; cbn [length]; lia.
Qed.

Lemma zsum_filter_mono {X : Type} (f : X -> Z) (p q : X -> bool) l : (forall x, p x = true -> q x = true) ->
  (forall x, 0 <= f x) -> zsum f (filter p l) <= zsum f (filter q l).
Proof.
  intros H Hf. induction l as [|x l IH]; [apply Z.le_refl|]. cbn [filter]. destruct (p x) eqn:Ep.
  - rewrite (H x Ep). cbv beta iota. rewrite !zsum_cons. lia.
  - destruct (q x); cbv beta iota; [rewrite zsum_cons; pose proof (Hf x); lia|exact IH].
Qed.

Lemma zsum_le_bound {X : Type} (f : X -> Z) (a : Z) l : (forall x, In x l -> f x <= a) ->
  zsum f l <= a * Z.of_nat (length l).
Proof.
  induction l as [|x l IH]; intros H.
  - rewrite zsum_nil. cbn [length]. change (Z.of_nat 0) with 0. rewrite Z.mul_0_r. lia.
  - rewrite zsum_cons. cbn [length]. rewrite Nat2Z.inj_succ, Z.mul_succ_r.
    pose proof (H x (or_introl eq_refl)).
    assert (zsum f l <= a * Z.of_nat (length l)) by (apply IH; intros y Hy; apply H; right; exact Hy). lia.
Qed.

Lemma zsumZ_in_le (f : Z -> Z) c l : (forall x, In x l -> 0 <= f x) -> In c l -> f c <= zsumZ f l.
Proof.
  induction l as [|x l IH]; intros H Hin; [destruct Hin|]. rewrite zsumZ_cons.
  destruct Hin as [<-|Hin].
  - assert (0 <= zsumZ f l) by (apply zsumZ_nonneg; intros y Hy; apply H; right; exact Hy). lia.
  - pose proof (H x (or_introl eq_refl)).
    assert (f c <= zsumZ f l) by (apply IH; [intros y Hy; apply H; right; exact Hy|exact Hin]). lia.
Qed.

Lemma znth_lv_add_eq L d x j : 0 <= d -> 0 <= j ->
  znth j (lv_add L d x) = znth j L + (if (j =? d) && (d <? Z.of_nat (length L)) then x else 0).
Proof.
  intros Hd Hj. unfold lv_add. rewrite znth_zset by lia.
  destruct (Z.eqb_spec j d) as [E|E]; destruct (d <? Z.of_nat (length L)); cbn [andb]; subst; lia.
Qed.

Lemma one_if_b c d : 0 <= one_if c d <= 1.
Proof. unfold one_if. destruct (c =? d); cbv beta iota; lia. Qed.

Lemma ek_c_nonneg V c : 0 <= ek_c V c.
Proof. unfold ek_c. apply zsum_nonneg. intros n _. cbv beta. pose proof (one_if_b c (band n)). lia. Qed.

Lemma ek_b_nonneg V : Forall (fun n => 0 <= n) (rv_ek V) -> 0 <= ek_b V.
Proof. intros H. unfold ek_b. apply zsum_nonneg. intros n Hn. exact (proj1 (Forall_forall _ _) H n Hn). Qed.

Lemma znth_lv_add_d L d x c : length L = 49%nat -> 0 <= d < 49 -> 0 <= c ->
  znth c (lv_add L d x) = znth c L + x * one_if c d.
Proof.
  intros Hl Hd Hc. rewrite znth_lv_add by (try rewrite Hl; lia). unfold one_if.
  destruct (Z.eqb_spec c d) as [E|E]; cbv beta iota; [subst c; lia|lia].
Qed.

Lemma one_if_sum d : 0 <= d < 49 -> zsumZ (fun c => one_if c d) (zseq 0 49) = 1.
Proof.
  intros Hd. unfold one_if.
  exact (zsumZ_single (fun _ : Z => 1) d (zseq 0 49) (YO0s.zseq_NoDup 0 49) (proj2 (In_zseq 0 49 d) ltac:(lia))).
Qed.

Lemma alsum_repeat0 : alsum (repeat 0 49) = 0.
Proof. vm_compute. reflexivity. Qed.

Lemma alsum_lv_add al d x : length al = 49%nat -> 0 <= d < 49 -> alsum (lv_add al d x) = alsum al + x.
Proof.
  intros Hl Hd. unfold alsum.
  rewrite (zsumZ_ext _ (fun c => znth c al + x * one_if c d)).
  2: { intros c Hc. apply In_zseq in Hc. apply znth_lv_add_d; [exact Hl|exact Hd|lia]. }
  rewrite zsumZ_add, zsumZ_mul_l, one_if_sum by exact Hd. lia.
Qed.

Lemma live_fold_le T : forall L c, 0 <= c -> (forall t, In t T -> 0 <= snd t) ->
  znth c L <= znth c (lv_fold 1 T L) <= znth c L + Z.of_nat (length T).
Proof.
  induction T as [|t T IH]; intros L c Hc HT.
  - change (lv_fold 1 [] L) with L. cbn [length]. change (Z.of_nat 0) with 0. lia.
  - change (lv_fold 1 (t :: T) L) with (lv_fold 1 T (lv_add L (band (snd t)) 1)).
    pose proof (band_range (snd t) (HT t (or_introl eq_refl))) as Bn.
    destruct (IH (lv_add L (band (snd t)) 1) c Hc (fun u Hu => HT u (or_intror Hu))) as [H1 H2].
    rewrite znth_lv_add_eq in H1, H2 by lia. cbn [length]. rewrite Nat2Z.inj_succ. revert H1 H2.
    destruct ((c =? band (snd t)) && (band (snd t) <? Z.of_nat (length L))); cbv beta iota; intros H1 H2; lia.
Qed.

Lemma lv_fold_length x T : forall L, length (lv_fold x T L) = length L.
Proof.
  induction T as [|t T IH]; intros L; [reflexivity|].
  change (lv_fold x (t :: T) L) with (lv_fold x T (lv_add L (band (snd t)) x)). rewrite IH. apply lv_add_length.
Qed.

Lemma tsum_bounds T a : (forall t, In t T -> 0 <= snd t <= a) -> 0 <= tsum T <= a * Z.of_nat (length T).
Proof.
  induction T as [|t T IH]; intros H.
  - change (tsum []) with 0. cbn [length]. change (Z.of_nat 0) with 0. rewrite Z.mul_0_r. lia.
  - change (tsum (t :: T)) with (snd t + tsum T). cbn [length]. rewrite Nat2Z.inj_succ, Z.mul_succ_r.
    pose proof (H t (or_introl eq_refl)).
    assert (0 <= tsum T <= a * Z.of_nat (length T)) by (apply IH; intros u Hu; apply H; right; exact Hu). lia.
Qed.

Lemma rec_cred_ge c r : 3 <= rec_cred c r.
Proof. unfold rec_cred, zlen. lia. Qed.

Lemma rec_credb_ge r : WILD_B <= rec_credb r.
Proof.
  unfold rec_credb. assert (0 <= zsum lmass (inner_segs (plz r))); [|lia].
  apply zsum_nonneg. intros l _. exact (proj1 (lc_mass_le l)).
Qed.

Lemma prom_c_nonneg P c : 0 <= prom_c P c.
Proof.
  unfold prom_c. apply zsum_nonneg. intros rs _. apply zsum_nonneg. intros r _. pose proof (rec_cred_ge c r). lia.
Qed.

Lemma promb_nonneg P : 0 <= promb P.
Proof.
  unfold promb. apply zsum_nonneg. intros rs _. apply zsum_nonneg. intros r _. pose proof (rec_credb_ge r).
  unfold WILD_B, LLIM in *. lia.
Qed.

Lemma cmass_nonneg x : 0 <= cmass x.
Proof. unfold cmass. apply zsum_nonneg. intros r Hr. exact (ck_req x r Hr). Qed.

Lemma cons_nonneg pl k c : 0 <= cons_c pl k c.
Proof. unfold cons_c. pose proof (xcount_nonneg c (filter (done_ck k) (pl_chunks pl))). unfold zlen. lia. Qed.

Lemma consb_nonneg pl k : 0 <= consb pl k.
Proof.
  unfold consb. assert (0 <= zsum cmass (filter (done_ck k) (pl_chunks pl)))
    by (apply zsum_nonneg; intros x _; apply cmass_nonneg).
  unfold zlen, WILD_B, LLIM. lia.
Qed.

Lemma cons_le pl k c : cons_c pl k c <= x_c c pl + 1536.
Proof.
  unfold cons_c, x_c. pose proof (xcount_filter_le c (done_ck k) (pl_chunks pl)).
  pose proof (filter_len_le (done1 k) (pl_chunks pl)). pose proof (pl_chunks_len pl). unfold zlen. lia.
Qed.

Lemma consb_le pl k : consb pl k <= CONSB_MAX.
Proof.
  unfold consb, CONSB_MAX.
  pose proof (pk_zsum_filter cmass (done_ck k) (pl_chunks pl) (fun x _ => cmass_nonneg x)) as H1.
  assert (H2 : zsum cmass (pl_chunks pl) <= zlen (pl_chunks pl) * (4 * 65536)).
  { unfold cmass. rewrite <- zsum_ffm. apply mass_chunks. apply pl_chunks_data. }
  pose proof (filter_len_le (done1 k) (pl_chunks pl)). pose proof (pl_chunks_len pl).
  unfold zlen, WILD_B, LLIM in *. lia.
Qed.

Lemma cons_mono pl k k' c : k <= k' -> cons_c pl k c <= cons_c pl k' c.
Proof.
  intros Hk. unfold cons_c.
  assert (D : forall x, done_ck k x = true -> done_ck k' x = true).
  { intros x. unfold done_ck. intros H. apply Z.leb_le in H. apply Z.leb_le. lia. }
  pose proof (xcount_filter_mono c (done_ck k) (done_ck k') (pl_chunks pl) D).
  assert (zlen (filter (done1 k) (pl_chunks pl)) <= zlen (filter (done1 k') (pl_chunks pl))).
  { apply zlen_filter_mono. intros x Hx. unfold done1 in *. apply andb_prop in Hx as [Hx1 Hx2].
    rewrite (D x Hx1), Hx2. reflexivity. }
  lia.
Qed.

Lemma consb_mono pl k k' : k <= k' -> consb pl k <= consb pl k'.
Proof.
  intros Hk. unfold consb.
  assert (D : forall x, done_ck k x = true -> done_ck k' x = true).
  { intros x. unfold done_ck. intros H. apply Z.leb_le in H. apply Z.leb_le. lia. }
  pose proof (zsum_filter_mono cmass (done_ck k) (done_ck k') (pl_chunks pl) D cmass_nonneg).
  assert (zlen (filter (done1 k) (pl_chunks pl)) <= zlen (filter (done1 k') (pl_chunks pl))).
  { apply zlen_filter_mono. intros x Hx. unfold done1 in *. apply andb_prop in Hx as [Hx1 Hx2].
    rewrite (D x Hx1), Hx2. reflexivity. }
  unfold WILD_B, LLIM. lia.
Qed.

Lemma cdat_nonneg pl k : 0 <= cdat pl k.
Proof. unfold cdat. apply zsum_nonneg. intros x _. unfold zlen. lia. Qed.

Lemma cdat_le pl k : cdat pl k <= BTEXT.
Proof.
  unfold cdat, BTEXT.
  assert (F : forall x, In x (pl_chunks pl) -> 0 <= zlen (ck_data x)) by (intros x _; unfold zlen; lia).
  pose proof (pk_zsum_filter (fun x => zlen (ck_data x)) (done1 k) (pl_chunks pl) F) as H1.
  assert (H2 : zsum (fun x => zlen (ck_data x)) (pl_chunks pl) <= 65535 * Z.of_nat (length (pl_chunks pl))).
  { apply zsum_le_bound. intros x Hx. exact (pl_chunks_data pl x Hx). }
  pose proof (pl_chunks_len pl). lia.
Qed.

Lemma cdat_mono pl k k' : k <= k' -> cdat pl k <= cdat pl k'.
Proof.
  intros Hk. unfold cdat. apply zsum_filter_mono; [|intros x; unfold zlen; lia].
  intros x Hx. unfold done1, done_ck in *. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1.
  rewrite (proj2 (Z.leb_le (ck_end x) k') ltac:(lia)), H2. reflexivity.
Qed.

Lemma zlen_flat_map {X Y : Type} (g : X -> list Y) l : zlen (flat_map g l) = zsum (fun x => zlen (g x)) l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. change (flat_map g (x :: l)) with (g x ++ flat_map g l).
  rewrite zsum_cons, <- IH. unfold zlen. rewrite length_app. lia.
Qed.

Lemma lc_count l : zlen (line_copies l) <= zlen l + 1.
Proof.
  unfold line_copies. destruct (zlen l <=? LLIM); [|unfold zlen; cbn [length]; lia].
  destruct (begin_line l) eqn:Eb.
  - pose proof (begin_line_len l Eb). unfold zlen in *. cbn [length]. lia.
  - unfold zlen. cbn [length]. lia.
Qed.

Lemma ck_count c : zlen (ck_copies c) <= zlen (ck_data c) + 2.
Proof.
  unfold ck_copies. destruct (ck_op c =? 7).
  - unfold zlen. cbn [length]. lia.
  - pose proof (zlen_flat_map line_copies (inner_segs (ck_data c))) as H0.
    assert (H1 : zsum (fun l => zlen (line_copies l)) (inner_segs (ck_data c)) <=
                 zsum (fun l => zlen l + 1) (inner_segs (ck_data c))).
    { apply zsum_le'. intros l _. apply lc_count. }
    pose proof (inner_le (fun l => zlen l + 1) (ck_data c) ltac:(intros s; cbv beta; unfold zlen; lia)) as H2.
    rewrite zsegs_mass in H2. unfold zlen in *. cbn [length]. lia.
Qed.

Lemma copies_le cs : (forall c, In c cs -> zlen (ck_data c) <= 65535) ->
  zlen (flat_map ck_copies cs) <= 65537 * zlen cs.
Proof.
  intros H. rewrite zlen_flat_map. eapply Z.le_trans; [apply (zsum_le_bound _ 65537)|unfold zlen; lia].
  intros x Hx. cbv beta. pose proof (ck_count x). pose proof (H x Hx). lia.
Qed.

Lemma xsum_le (l : list Z) : (forall r, In r l -> 0 <= r) ->
  zsumZ (fun c => zlen (filter (fun r => band r =? c) l)) (zseq 0 49) <= zlen l.
Proof.
  induction l as [|x l IH]; intros H.
  - rewrite zsumZ_zero; [unfold zlen; cbn [length]; lia|]. intros c _. reflexivity.
  - transitivity (zsumZ (fun c => one_if c (band x) + zlen (filter (fun r => band r =? c) l)) (zseq 0 49)).
    + apply Z.eq_le_incl. apply zsumZ_ext. intros c _. unfold one_if. cbn [filter].
      rewrite (Z.eqb_sym c (band x)). destruct (band x =? c); unfold zlen; cbn [length]; lia.
    + rewrite zsumZ_add, one_if_sum by (apply band_range; apply H; left; reflexivity).
      pose proof (IH (fun r Hr => H r (or_intror Hr))). unfold zlen in *. cbn [length]. lia.
Qed.

Lemma cons_sum pl k : zsumZ (fun c => cons_c pl k c) (zseq 0 49) <= ALSUM_MAX.
Proof.
  unfold cons_c. rewrite zsumZ_add.
  assert (H1 : zsumZ (fun c => xcount c (filter (done_ck k) (pl_chunks pl))) (zseq 0 49) <= BTEXT + 1024).
  { unfold xcount. eapply Z.le_trans; [apply xsum_le|].
    - intros r Hr. apply in_flat_map in Hr as (x & _ & Hx). exact (ck_req x r Hx).
    - eapply Z.le_trans; [apply copies_le|].
      + intros x Hx. apply filter_In in Hx as [Hx _]. exact (pl_chunks_data pl x Hx).
      + pose proof (filter_len_le (done_ck k) (pl_chunks pl)). pose proof (pl_chunks_len pl).
        unfold zlen, BTEXT. lia. }
  assert (H2 : zsumZ (fun c => 3 * zlen (filter (done1 k) (pl_chunks pl))) (zseq 0 49) <= 49 * 1536).
  { eapply Z.le_trans; [apply (zsumZ_le _ (fun _ => 1536))|].
    - intros c _. pose proof (filter_len_le (done1 k) (pl_chunks pl)). pose proof (pl_chunks_len pl).
      unfold zlen. lia.
    - apply Z.eq_le_incl. vm_compute. reflexivity. }
  unfold ALSUM_MAX. lia.
Qed.

Lemma nc_cnt_bounds V L A c : 0 <= nc_cnt V L A c <= Z.of_nat (length (rv_nc V)).
Proof. unfold nc_cnt, zlen. pose proof (filter_len_le (nc_has L A c) (rv_nc V)). lia. Qed.

Lemma drain_cred (rs : list (list byte)) (p : list Z) c : Forall (fun b => b <> 0) p ->
  zlen (filter (fun q => band q =? c) (flat_map line_copies (removelast (zsegs (p ++ concat (map plz rs)))))) <=
  zsum (rec_cred c) rs.
Proof.
  intros Hp. eapply Z.le_trans; [exact (drain_band (map plz rs) p c Hp)|].
  rewrite zsum_map. apply Z.le_refl.
Qed.

Lemma drain_credb (rs : list (list byte)) (p : list Z) : Forall (fun b => b <> 0) p ->
  zsum lmass (removelast (zsegs (p ++ concat (map plz rs)))) <= zsum rec_credb rs.
Proof.
  intros Hp. eapply Z.le_trans; [exact (drain_mass (map plz rs) p Hp)|].
  rewrite zsum_map. apply Z.le_refl.
Qed.

Lemma nodup_map_filter {X Y : Type} (f : X -> Y) (p : X -> bool) l :
  List.NoDup (map f l) -> List.NoDup (map f (filter p l)).
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [map] in H. apply NoDup_cons_iff in H as [Hx H].
  cbn [filter]. destruct (p x); [|exact (IH H)]. cbn [map]. constructor; [|exact (IH H)].
  intros Hin. apply Hx. apply in_map_iff in Hin as (y & Ey & Hy). apply filter_In in Hy as [Hy _].
  rewrite <- Ey. apply in_map. exact Hy.
Qed.

Lemma nodup_map_eq {X Y : Type} (f : X -> Y) l x y : List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros H Hx Hy Hf; [destruct Hx|]. cbn [map] in H. apply NoDup_cons_iff in H as [Ha H].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Ha. rewrite Hf. apply in_map. exact Hy.
  - exfalso. apply Ha. rewrite <- Hf. apply in_map. exact Hx.
  - exact (IH H Hx Hy Hf).
Qed.

Lemma mis_count V L M c : mis_nc V L M -> (length (rv_nc V) <= NC_MAX)%nat -> count_mis M c + 1 <= MC_ONE.
Proof.
  intros (HI & HN) HL. unfold count_mis.
  pose proof (filter_len_le (fun e : sptr * Z => snd e =? c) M) as F.
  assert (G : (length (mis_addrs L M) <= length (rv_nc V))%nat) by (apply NoDup_incl_length; assumption).
  unfold mis_addrs in G. rewrite length_map in G. unfold NC_MAX in HL. unfold MC_ONE. lia.
Qed.

Lemma mis_nc_nil V L : mis_nc V L [].
Proof. split; [intros a []|constructor]. Qed.

Lemma mis_nc_del V L M p : mis_nc V L M -> mis_nc V L (mis_del M p).
Proof.
  unfold mis_nc, mis_del, mis_addrs. intros (HI & HN). split.
  - intros a Ha. apply HI. apply in_map_iff in Ha as (e & <- & He). apply filter_In in He as [He _].
    apply (in_map (fun e => ptr_addr L (fst e))). exact He.
  - apply nodup_map_filter. exact HN.
Qed.

Lemma mis_nc_realloc V L M k n p q :
  mis_nc V L (mis_del M p) -> In (ptr_addr L p) (rv_nc V) -> ~ In (ptr_addr L p) (mis_addrs L (mis_del M p)) ->
  mis_nc V L (mis_realloc M k n p q).
Proof.
  intros (HI & HN) Hp Hn. unfold mis_realloc.
  match goal with |- mis_nc _ _ (if ?b then _ else _) => destruct b end; [|split; assumption].
  unfold mis_nc, mis_addrs in *. cbn [map fst]. split.
  - intros a [<-|Ha]; [exact Hp|exact (HI a Ha)].
  - constructor; [exact Hn|exact HN].
Qed.

Lemma mis_nodup L A M mc : List.NoDup (map fst (blocks L A)) -> MIS A M mc -> List.NoDup (mis_addrs L M).
Proof.
  intros HB (HN & HU & _). unfold mis_addrs. revert HN HU.
  induction M as [|e M IH]; intros HN HU; [constructor|]. cbn [map] in HN |- *.
  apply NoDup_cons_iff in HN as [He HN]. constructor.
  - intros Hin. apply in_map_iff in Hin as (e' & Ee & He').
    destruct (HU e (or_introl eq_refl)) as (_ & n & Hn).
    destruct (HU e' (or_intror He')) as (_ & n' & Hn').
    assert (Eq : (fst e', n') = (fst e, n)).
    { apply (nodup_map_eq (fun b => ptr_addr L (fst b)) (user_blocks A)); [|exact Hn'|exact Hn|exact Ee].
      unfold blocks in HB. rewrite map_map in HB. exact HB. }
    apply He. injection Eq as E1 E2. rewrite <- E1. apply in_map. exact He'.
  - apply IH; [exact HN|]. intros x Hx. apply HU. right. exact Hx.
Qed.

Lemma ledger3_room NW pl k V L A b al alb c : RI3_ledger NW pl k V L A b al alb -> 0 <= c < 49 ->
  znth c (p3_live b) + 1 <= znth c (p3_cap b).
Proof.
  intros (HC & _ & HN & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) Hc. destruct (H c Hc) as (H1 & H2 & H3).
  pose proof (cons_le pl k c). pose proof (prom_c_nonneg (rv_pend V) c). pose proof (nc_cnt_bounds V L A c).
  pose proof (ek_c_nonneg V c).
  assert (Z.of_nat (length (rv_nc V)) <= 26) by (unfold NC_MAX in HN; lia).
  rewrite HC, CS_reply_at by exact Hc.
  unfold cs_band. destruct (Z.eqb_spec c 0) as [E|E]; cbv beta iota.
  - subst c. pose proof (x0_bound pl). unfold CAPS0, RI_BASE, BTEXT in *. lia.
  - unfold CBASE, RI_BASE in *. lia.
Qed.

Lemma ledger3_alsum NW pl k V L A b al alb : RI3_ledger NW pl k V L A b al alb -> alsum al <= ALSUM_MAX.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). unfold alsum.
  eapply Z.le_trans; [|apply (cons_sum pl k)]. apply zsumZ_le. intros c Hc. apply In_zseq in Hc. cbv beta.
  destruct (H c ltac:(lia)) as (_ & _ & H3). pose proof (prom_c_nonneg (rv_pend V) c). pose proof (ek_c_nonneg V c).
  lia.
Qed.

Lemma ledger3_bytes NW pl k V L A b al alb : RI3_ledger NW pl k V L A b al alb -> p3_bytes b <= PB3_MAX.
Proof.
  intros HL. pose proof (ledger3_alsum _ _ _ _ _ _ _ _ _ HL) as HS.
  destruct HL as (_ & _ & _ & _ & _ & _ & HE & HB & HW1 & HW2 & HP & _).
  pose proof (consb_le pl k). pose proof (promb_nonneg (rv_pend V)). pose proof (cdat_le pl k).
  pose proof (ek_b_nonneg V HE).
  unfold PB3_MAX, NC_PER, DATA_PER in *. lia.
Qed.

Lemma PB3_MAX_val : PB3_MAX = 2092075360.
Proof. vm_compute. reflexivity. Qed.

Theorem ledger3_cf NW pl k V L A b al alb n : RI3_ledger NW pl k V L A b al alb -> 0 <= n <= NMAX ->
  p3_bytes b + n <= CF_MAX.
Proof.
  intros HL Hn. pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL).
  assert (X : PB3_MAX + NMAX <= CF_MAX) by (apply Z.leb_le; vm_compute; reflexivity). lia.
Qed.

Lemma ledger3_mis NW pl k V L A b al alb c : RI3_ledger NW pl k V L A b al alb -> 0 <= c < 49 ->
  count_mis (p3_mis b) c + 1 <= znth c (p3_mcap b).
Proof.
  intros (_ & HM & HN & _ & _ & _ & _ & _ & _ & _ & _ & HMis & _) Hc. rewrite HM, MC_reply_at by exact Hc.
  exact (mis_count V L (p3_mis b) c HMis HN).
Qed.

Theorem room3_ledger NW pl k V L A b al alb n : RI3_ledger NW pl k V L A b al alb -> 0 <= n <= NMAX ->
  room_pack3 b n.
Proof.
  intros HL Hn. pose proof (band_range n ltac:(lia)) as Bn. pose proof HL as (HC & HM & _).
  apply (room_pack3_of b n BMAX NMAX).
  - rewrite HC, HM. apply CS_reply_capok3.
  - lia.
  - pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL).
    assert (X : PB3_MAX + NMAX <= BMAX) by (apply Z.leb_le; vm_compute; reflexivity). lia.
  - exact (ledger3_room _ _ _ _ _ _ _ _ _ _ HL Bn).
  - intros Hb. apply (ledger3_mis _ _ _ _ _ _ _ _ _ _ HL). lia.
Qed.

Lemma ledger3_mono NW pl k k' V L A b al alb : RI3_ledger NW pl k V L A b al alb -> k <= k' ->
  RI3_ledger NW pl k' V L A b al alb.
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H) Hk.
  pose proof (cdat_mono pl k k' Hk) as CD. pose proof (consb_mono pl k k' Hk) as CB.
  split; [exact HC|]. split; [exact HM|]. split; [exact HN|]. split; [exact HlL|]. split; [exact HL|].
  split; [exact Ha|]. split; [exact HE|]. split; [exact HB|]. split; [exact HW1|].
  split; [unfold DATA_PER in *; lia|].
  split; [lia|]. split; [exact HMis|].
  intros c Hc. destruct (H c Hc) as (H1 & H2 & H3). pose proof (cons_mono pl k k' c Hk). lia.
Qed.

Lemma nw_copy_local NW pl k V L A b al alb k' V' : RI3_ledger NW pl k V L A b al alb ->
  NW V' <= NW V + NC_PER + DATA_PER * (cdat pl k' - cdat pl k) ->
  NW V' <= NC_FIX + NC_PER * (alsum al + 1) + DATA_PER * cdat pl k'.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & HW2 & _) H. unfold NC_PER, DATA_PER in *. lia. Qed.

Lemma nw_nc_local NW pl k V L A b al alb k' V' : RI3_ledger NW pl k V L A b al alb ->
  NW V' <= NW V + DATA_PER * (cdat pl k' - cdat pl k) ->
  NW V' <= NC_FIX + NC_PER * alsum al + DATA_PER * cdat pl k'.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & HW2 & _) H. unfold NC_PER, DATA_PER in *. lia. Qed.

Lemma live3_malloc b n c : 0 <= n -> 0 <= c ->
  znth c (p3_live (pb3_malloc b n)) <= znth c (p3_live b) + one_if c (band n).
Proof.
  intros Hn Hc. pose proof (band_range n Hn) as Bn. unfold pb3_malloc, one_if. cbn [p3_live].
  rewrite znth_lv_add_eq by lia.
  destruct (c =? band n); destruct (band n <? Z.of_nat (length (p3_live b))); cbn [andb]; lia.
Qed.

Lemma live3_free b n p c : length (p3_live b) = 49%nat -> 0 <= n -> 0 <= c < 49 ->
  znth c (p3_live (pb3_free b n p)) <= znth c (p3_live b) - one_if c (band n).
Proof.
  intros Hl Hn Hc. pose proof (band_range n Hn) as Bn. unfold pb3_free. cbn [p3_live].
  rewrite znth_lv_add_d by (first [exact Hl | lia]). lia.
Qed.

Lemma live3_realloc b k n p q c : length (p3_live b) = 49%nat -> 0 <= k -> 0 <= n -> 0 <= c < 49 ->
  znth c (p3_live (pb3_realloc b k n p q)) <= znth c (p3_live b) + (one_if c (band n) - one_if c (band k)).
Proof.
  intros Hl Hk Hn Hc. pose proof (band_range n Hn) as Bn. pose proof (band_range k Hk) as Bk.
  unfold pb3_realloc. cbn [p3_live].
  rewrite znth_lv_add_d by (first [rewrite lv_add_length; exact Hl | lia]).
  rewrite znth_lv_add_d by (first [exact Hl | lia]). lia.
Qed.

Lemma ledger3_copy NW pl k V L A b al alb n k' V' L' A' : RI3_ledger NW pl k V L A b al alb -> 0 <= n ->
  copy_step NW pl k' V L A V' L' A' al alb n -> mis_nc V' L' (p3_mis b) ->
  RI3_ledger NW pl k' V' L' A' (pb3_malloc b n) (lv_add al (band n) 1) (alb + n).
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H) Hn
    (HN' & HC' & HB' & HW1' & HW2' & HP' & HQ' & HE') HMis'.
  pose proof (band_range n Hn) as Bn.
  split; [exact HC|]. split; [exact HM|]. split; [exact HN'|].
  split; [unfold pb3_malloc; cbn [p3_live]; rewrite lv_add_length; exact HlL|].
  split; [rewrite lv_add_length; exact HL|]. split; [lia|]. split; [exact HE'|].
  split; [unfold pb3_malloc; cbn [p3_bytes]; lia|]. split; [exact HW1'|].
  split; [rewrite alsum_lv_add by (first [exact HL | lia]); exact HW2'|].
  split; [exact HQ'|]. split; [exact HMis'|].
  intros c Hc. destruct (H c Hc) as (H1 & H2 & H3).
  pose proof (live3_malloc b n c Hn ltac:(lia)) as M. pose proof (HP' c Hc) as P. pose proof (HC' c Hc) as Q.
  pose proof (one_if_b c (band n)). rewrite znth_lv_add_d by (first [exact HL | lia]). lia.
Qed.

Lemma ledger3_nc NW pl k V L A b al alb k' V' L' A' b' dl db : RI3_ledger NW pl k V L A b al alb ->
  nc_step NW pl k' V L A V' L' A' al alb dl db -> p3_cap b' = p3_cap b -> p3_mcap b' = p3_mcap b ->
  length (p3_live b') = 49%nat ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b') <= znth c (p3_live b) + dl c) -> p3_bytes b' <= p3_bytes b + db ->
  mis_nc V' L' (p3_mis b') -> RI3_ledger NW pl k' V' L' A' b' al alb.
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H)
    (HN' & HC' & HB' & HW1' & HW2' & HP' & HQ' & HE')
    Hcap Hmc Hl Hlive Hby HMis'.
  split; [rewrite Hcap; exact HC|]. split; [rewrite Hmc; exact HM|]. split; [exact HN'|]. split; [exact Hl|].
  split; [exact HL|]. split; [exact Ha|]. split; [exact HE'|]. split; [lia|]. split; [exact HW1'|].
  split; [exact HW2'|].
  split; [exact HQ'|]. split; [exact HMis'|].
  intros c Hc. destruct (H c Hc) as (H1 & H2 & H3). pose proof (Hlive c Hc). pose proof (HC' c Hc).
  pose proof (HP' c Hc). lia.
Qed.

Theorem room3_copy E k V L A b al alb n k' :
  RI3_ledger rv_wt (ss_pl E) k V L A b al alb -> 0 <= n <= NMAX ->
  room_pack3 b n /\ p3_bytes b + n <= CF_MAX /\
  forall L' A' V', res_ok_pack3 A' (pb3_malloc b n) -> copy_step rv_wt (ss_pl E) k' V L A V' L' A' al alb n ->
    mis_nc V' L' (p3_mis b) -> RI3_reply E k' V' L' A'.
Proof.
  intros HL Hn. split; [exact (room3_ledger _ _ _ _ _ _ _ _ _ _ HL Hn)|].
  split; [exact (ledger3_cf _ _ _ _ _ _ _ _ _ _ HL Hn)|].
  intros L' A' V' HA' HS HM'. hnf. exists (pb3_malloc b n), (lv_add al (band n) 1), (alb + n).
  split; [exact HA'|]. exact (ledger3_copy rv_wt (ss_pl E) k V L A b al alb n k' V' L' A' HL ltac:(lia) HS HM').
Qed.

Theorem room3_nc E k V L A b al alb n k' :
  RI3_ledger rv_wt (ss_pl E) k V L A b al alb -> 0 <= n <= NMAX ->
  room_pack3 b n /\ p3_bytes b + n <= CF_MAX /\
  forall L' A' V', res_ok_pack3 A' (pb3_malloc b n) ->
    nc_step rv_wt (ss_pl E) k' V L A V' L' A' al alb (fun c => one_if c (band n)) n ->
    mis_nc V' L' (p3_mis b) -> RI3_reply E k' V' L' A'.
Proof.
  intros HL Hn. pose proof HL as (_ & _ & _ & HlL & _). split; [exact (room3_ledger _ _ _ _ _ _ _ _ _ _ HL Hn)|].
  split; [exact (ledger3_cf _ _ _ _ _ _ _ _ _ _ HL Hn)|].
  intros L' A' V' HA' HS HM'. hnf. exists (pb3_malloc b n), al, alb. split; [exact HA'|].
  apply (ledger3_nc rv_wt (ss_pl E) k V L A b al alb k' V' L' A' (pb3_malloc b n) (fun c => one_if c (band n)) n HL
    HS);
    [reflexivity|reflexivity| | | |exact HM'].
  - unfold pb3_malloc. cbn [p3_live]. rewrite lv_add_length. exact HlL.
  - intros c Hc. cbv beta. apply live3_malloc; lia.
  - unfold pb3_malloc. cbn [p3_bytes]. lia.
Qed.

Theorem room3_free E k V L A b al alb n p k' :
  RI3_ledger rv_wt (ss_pl E) k V L A b al alb -> 0 <= n ->
  forall L' A' V', res_ok_pack3 A' (pb3_free b n p) ->
    nc_step rv_wt (ss_pl E) k' V L A V' L' A' al alb (fun c => - one_if c (band n)) (- n) ->
    mis_nc V' L' (mis_del (p3_mis b) p) -> RI3_reply E k' V' L' A'.
Proof.
  intros HL Hn L' A' V' HA' HS HM'. pose proof HL as (_ & _ & _ & HlL & _). hnf.
  exists (pb3_free b n p), al, alb. split; [exact HA'|].
  apply (ledger3_nc rv_wt (ss_pl E) k V L A b al alb k' V' L' A' (pb3_free b n p) (fun c => - one_if c (band n))
    (- n)
    HL HS); [reflexivity|reflexivity| | | |exact HM'].
  - unfold pb3_free. cbn [p3_live]. rewrite lv_add_length. exact HlL.
  - intros c Hc. cbv beta. pose proof (live3_free b n p c HlL Hn Hc). lia.
  - unfold pb3_free. cbn [p3_bytes]. lia.
Qed.

Theorem room3_realloc E k V L A b al alb m n p k' :
  RI3_ledger rv_wt (ss_pl E) k V L A b al alb -> 0 <= m -> 0 <= n <= NMAX ->
  room_pack3 b n /\ p3_bytes b + n <= CF_MAX /\
  forall q L' A' V', res_ok_pack3 A' (pb3_realloc b m n p q) ->
    nc_step rv_wt (ss_pl E) k' V L A V' L' A' al alb (fun c => one_if c (band n) - one_if c (band m)) (n - m) ->
    mis_nc V' L' (mis_realloc (p3_mis b) m n p q) -> RI3_reply E k' V' L' A'.
Proof.
  intros HL Hm Hn. pose proof HL as (_ & _ & _ & HlL & _).
  split; [exact (room3_ledger _ _ _ _ _ _ _ _ _ _ HL Hn)|].
  split; [exact (ledger3_cf _ _ _ _ _ _ _ _ _ _ HL Hn)|].
  intros q L' A' V' HA' HS HM'. hnf. exists (pb3_realloc b m n p q), al, alb. split; [exact HA'|].
  apply (ledger3_nc rv_wt (ss_pl E) k V L A b al alb k' V' L' A' (pb3_realloc b m n p q)
    (fun c => one_if c (band n) - one_if c (band m)) (n - m) HL HS); [reflexivity|reflexivity| | | |exact HM'].
  - unfold pb3_realloc. cbn [p3_live]. rewrite !lv_add_length. exact HlL.
  - intros c Hc. cbv beta. apply live3_realloc; [exact HlL|lia|lia|lia].
  - unfold pb3_realloc. cbn [p3_bytes]. lia.
Qed.

Theorem room3_inplace E k V L A b al alb m n p k' :
  RI3_ledger rv_wt (ss_pl E) k V L A b al alb -> 0 <= m -> 0 <= n <= NMAX ->
  room_pack3 b n /\ p3_bytes b + n <= CF_MAX /\
  forall L' A' V', res_ok_pack3 A' (pb3_realloc b m n p p) ->
    nc_step rv_wt (ss_pl E) k' V L A V' L' A' al alb (fun c => one_if c (band n) - one_if c (band m)) (n - m) ->
    In (ptr_addr L' p) (rv_nc V') -> mis_nc V' L' (mis_del (p3_mis b) p) ->
    ~ In (ptr_addr L' p) (mis_addrs L' (mis_del (p3_mis b) p)) -> RI3_reply E k' V' L' A'.
Proof.
  intros HL Hm Hn. destruct (room3_realloc E k V L A b al alb m n p k' HL Hm Hn) as (R & C & K).
  split; [exact R|]. split; [exact C|]. intros L' A' V' HA' HS Hp HD HN. apply (K p L' A' V' HA' HS).
  apply mis_nc_realloc; assumption.
Qed.

Theorem RI3_mono : RI_mono RI3_reply.
Proof.
  intros E k k' V L A (b & al & alb & HR & HL) Hk. hnf. exists b, al, alb. split; [exact HR|].
  eapply ledger3_mono; [exact HL|lia].
Qed.

Lemma drv_live_le d c : drv_pb d -> 0 <= c < 49 -> 0 <= znth c (pb_live d) <= 2.
Proof.
  intros (_ & D0 & DS & _) Hc. split; [exact (D0 c Hc)|].
  assert (znth c (pb_live d) <= zsumZ (fun k => znth k (pb_live d)) (zseq 0 49)).
  { apply (zsumZ_in_le (fun k => znth k (pb_live d))); [|apply In_zseq; lia].
    intros x Hx. apply In_zseq in Hx. exact (D0 x ltac:(lia)). }
  unfold PDRV_LIVE in DS. lia.
Qed.

Lemma T_sizes (T : list (Z * Z)) : (forall t k, In (t, k) T -> 0 < k <= TBBYTES) ->
  forall t, In t T -> 0 <= snd t <= TBBYTES.
Proof. intros H [t k] Hin. cbn [snd]. pose proof (H t k Hin). lia. Qed.

Theorem RI3_start E b T G OUT :
  res_ok_pack3 (ss_A E) b -> pack_entry CS_reply (ss_pl E) T (PB (p3_live b) (p3_bytes b) (p3_cap b)) ->
  p3_mcap b = MC_reply -> p3_mis b = [] ->
  (length T <= TBMAX)%nat -> (forall t k, In (t, k) T -> 0 < k <= TBBYTES) ->
  tsum T <= ncs (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E) ->
  ncs (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E) <= NC_FIX ->
  RI3_reply E 0 (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E).
Proof.
  intros HR HPE HMC HMS HTl HTk HS1 HS2.
  destruct HPE as (_ & HcB & d & Hd & HLv & HBy). cbn [pb_cap pb_live pb_bytes] in HcB, HLv, HBy.
  pose proof (T_sizes _ HTk) as HTs.
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HlL & _ & HlM & _).
  hnf. exists (PB3 (p3_live b) (p3_bytes b) (CS_reply (ss_pl E)) (p3_mis b) (p3_mcap b)), (repeat 0 49), 0.
  split.
  { apply res_ok_pack3_raise; [exact HR|apply CS_reply_len|exact HlM| |].
    - intros k Hk. exact (proj2 (HcB k Hk)).
    - intros k Hk. lia. }
  assert (Z0 : forall c, znth c (repeat 0 49) = 0) by (intros c; unfold znth; apply nth_repeat).
  pose proof (consb_nonneg (ss_pl E) 0) as CB. pose proof (cdat_nonneg (ss_pl E) 0) as CD.
  unfold TBMAX in HTl. assert (HT2 : Z.of_nat (length T) <= 2) by lia.
  split; [reflexivity|]. split; [exact HMC|]. split; [unfold NC_MAX; cbn [rv_nc length]; lia|].
  split; [exact HlL|]. split; [apply repeat_length|]. split; [lia|]. split; [cbn [rv_ek]; constructor|].
  split.
  { cbn [p3_bytes]. rewrite HBy, TDP_bytes. change (tsum []) with 0.
    pose proof Hd as (_ & _ & _ & DB). lia. }
  split; [exact HS2|].
  split; [cbn [rv_wt]; rewrite alsum_repeat0; unfold NC_PER, DATA_PER; lia|].
  split; [change (ek_b (RV [] [G; OUT] NC_FIX [])) with 0;
    change (promb (rv_pend (RV [] [G; OUT] NC_FIX []))) with 0; lia|].
  split; [cbn [p3_mis]; rewrite HMS; apply mis_nc_nil|].
  intros c Hc. rewrite Z0. split; [|split; [lia|]].
  - cbn [p3_live]. rewrite HLv, TDP_live. change (lv_fold (-1) [] (pb_live d)) with (pb_live d).
    pose proof (live_fold_le T (pb_live d) c ltac:(lia) (fun t Ht => proj1 (HTs t Ht))) as (_ & F).
    pose proof (drv_live_le d c Hd Hc). pose proof (nc_cnt_bounds (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E) c).
    unfold RI_BASE. lia.
  - change (ek_c (RV [] [G; OUT] NC_FIX []) c) with 0.
    change (prom_c (rv_pend (RV [] [G; OUT] NC_FIX [])) c) with 0. pose proof (cons_nonneg (ss_pl E) 0 c). lia.
Qed.

Definition xf_dec (x y : Z * Z) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma xf_incl_sum (f : Z * Z -> Z) : forall l m, List.NoDup l -> incl l m -> (forall x, In x m -> 0 <= f x) ->
  zsum f l <= zsum f m.
Proof.
  induction l as [|x l IH]; intros m Hnd Hin Hf.
  - rewrite zsum_nil. apply zsum_nonneg. exact Hf.
  - apply NoDup_cons_iff in Hnd as [Hx Hnd]. rewrite zsum_cons.
    assert (Hm : In x m) by (apply Hin; left; reflexivity).
    assert (IH' : zsum f l <= zsum f (remove xf_dec x m)).
    { apply IH; [exact Hnd| |].
      - intros y Hy. apply in_in_remove; [intros E; subst y; exact (Hx Hy)|apply Hin; right; exact Hy].
      - intros y Hy. apply Hf. apply (in_remove xf_dec) in Hy. exact (proj1 Hy). }
    pose proof (zsum_remove xf_dec f x m Hm Hf). lia.
Qed.

Lemma zsum_filter_or {X : Type} (f : X -> Z) (p q : X -> bool) l : (forall x, In x l -> 0 <= f x) ->
  zsum f (filter (fun x => p x || q x) l) <= zsum f (filter p l) + zsum f (filter q l).
Proof.
  induction l as [|x l IH]; intros H; [cbn [filter]; rewrite !zsum_nil; lia|]. cbn [filter].
  pose proof (IH (fun y Hy => H y (or_intror Hy))) as IH'. pose proof (H x (or_introl eq_refl)).
  destruct (p x), (q x); cbn [orb]; rewrite ?zsum_cons; lia.
Qed.

Lemma filt_R (X : list (Z * Z)) R : (forall t, In t X -> 0 <= snd t) ->
  zsum snd (filter (fun t => existsb (Z.eqb (fst t)) R) X) <=
  zsum (fun q => zsum snd (filter (fun t => fst t =? q) X)) R.
Proof.
  intros HX. induction R as [|q R IH].
  - assert (E : forall l : list (Z * Z), filter (fun t => existsb (Z.eqb (fst t)) []) l = [])
      by (intros l; induction l as [|a l IHl]; [reflexivity|exact IHl]).
    rewrite E, !zsum_nil. lia.
  - rewrite zsum_cons.
    pose proof (zsum_filter_or snd (fun t => fst t =? q) (fun t => existsb (Z.eqb (fst t)) R) X HX) as H1.
    cbv beta in H1.
    change (fun t : Z * Z => existsb (Z.eqb (fst t)) (q :: R))
      with (fun t : Z * Z => (fst t =? q) || existsb (Z.eqb (fst t)) R).
    lia.
Qed.

Lemma ncs_ge_tsum L A R T : List.NoDup T -> incl T (blocks L A) -> (forall t, In t (blocks L A) -> 0 <= snd t) ->
  (forall t, In t T -> In (fst t) R) -> tsum T <= zsum (nc_sz L A) R.
Proof.
  intros HT HI HX HR. change (tsum T) with (zsum snd T).
  eapply Z.le_trans; [|exact (filt_R (blocks L A) R HX)].
  apply xf_incl_sum; [exact HT| |intros x Hx; apply filter_In in Hx as [Hx _]; exact (HX x Hx)].
  intros t Ht. apply filter_In. split; [exact (HI t Ht)|]. apply existsb_exists. exists (fst t).
  split; [exact (HR t Ht)|apply Z.eqb_refl].
Qed.

Lemma xf_split {X : Type} (p : X -> bool) (f : X -> Z) l :
  zsum f l = zsum f (filter p l) + zsum f (filter (fun x => negb (p x)) l).
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [filter]. destruct (p x); cbn [negb]; rewrite ?zsum_cons, IH; lia.
Qed.

Lemma xf_app {X : Type} (l1 l2 : list X) : List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
  List.NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; intros H1 H2 HD; [exact H2|].
  apply NoDup_cons_iff in H1 as [Hx H1]. cbn [app]. constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hx Hin)|exact (HD x (or_introl eq_refl) Hin)].
  - apply IH; [exact H1|exact H2|]. intros y Hy. apply HD. right. exact Hy.
Qed.

Lemma xf_sum (f : Z * Z -> Z) (X S T T' : list (Z * Z)) :
  List.NoDup X -> List.NoDup T -> incl T S -> (forall t, In t S -> 0 <= f t) -> (forall t, In t T' -> 0 <= f t) ->
  (forall t, In t X -> (In t S /\ ~ In t T) \/ In t T') ->
  zsum f X + zsum f T <= zsum f S + zsum f T'.
Proof.
  intros HX HT HTS HS HT' HP.
  rewrite (xf_split (fun t => if in_dec xf_dec t T' then true else false) f X).
  assert (E2 : zsum f (filter (fun t => if in_dec xf_dec t T' then true else false) X) <= zsum f T').
  { apply xf_incl_sum; [apply NoDup_filter; exact HX| |exact HT'].
    intros t Ht. apply filter_In in Ht as [_ Ht]. destruct (in_dec xf_dec t T') as [Y|Y]; [exact Y|discriminate Ht]. }
  assert (E1 : zsum f (filter (fun x => negb (if in_dec xf_dec x T' then true else false)) X ++ T) <= zsum f S).
  { apply xf_incl_sum; [| |exact HS].
    - apply xf_app; [apply NoDup_filter; exact HX|exact HT|].
      intros t Ht. apply filter_In in Ht as [Hx Hn]. destruct (in_dec xf_dec t T') as [Y|Y]; [discriminate Hn|].
      destruct (HP t Hx) as [[_ Z]|Z]; [exact Z|contradiction].
    - intros t Ht. apply in_app_or in Ht as [Ht|Ht]; [|exact (HTS t Ht)].
      apply filter_In in Ht as [Hx Hn]. destruct (in_dec xf_dec t T') as [Y|Y]; [discriminate Hn|].
      destruct (HP t Hx) as [[Z _]|Z]; [exact Z|contradiction]. }
  rewrite zsum_app in E1. lia.
Qed.

Lemma xf_len {X : Type} (p : X -> bool) l : Z.of_nat (length (filter p l)) = zsum (fun x => if p x then 1 else 0) l.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [filter]. rewrite zsum_cons. cbv beta.
  destruct (p x); cbn [length]; lia.
Qed.

Lemma xf_bcount L s c : bcount s c = zsum (fun t : Z * Z => if band (snd t) =? c then 1 else 0) (blocks L s).
Proof. unfold bcount, blocks. rewrite xf_len, zsum_map. reflexivity. Qed.

Lemma xf_ubytes L s : ubytes s = zsum snd (blocks L s).
Proof. unfold blocks. rewrite zsum_map. reflexivity. Qed.

Lemma xf_lv T : forall L c, length L = 49%nat -> 0 <= c -> (forall t, In t T -> 0 <= snd t) ->
  znth c (lv_fold 1 T L) = znth c L + zsum (fun t : Z * Z => if band (snd t) =? c then 1 else 0) T.
Proof.
  induction T as [|t T IH]; intros L c HL Hc HT.
  - change (lv_fold 1 [] L) with L. rewrite zsum_nil. lia.
  - change (lv_fold 1 (t :: T) L) with (lv_fold 1 T (lv_add L (band (snd t)) 1)).
    pose proof (band_range (snd t) (HT t (or_introl eq_refl))) as Bn.
    rewrite (IH (lv_add L (band (snd t)) 1) c ltac:(rewrite lv_add_length; exact HL) Hc
      (fun u Hu => HT u (or_intror Hu))).
    rewrite znth_lv_add_eq by lia. rewrite zsum_cons, HL. cbv beta. rewrite (Z.eqb_sym c (band (snd t))).
    replace (band (snd t) <? Z.of_nat 49) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (band (snd t) =? c); cbn [andb]; lia.
Qed.

Lemma xf_cnt c (T : list (Z * Z)) :
  0 <= zsum (fun t : Z * Z => if band (snd t) =? c then 1 else 0) T <= Z.of_nat (length T).
Proof.
  induction T as [|t T IH]; [rewrite zsum_nil; cbn [length]; lia|].
  rewrite zsum_cons. cbv beta. cbn [length]. destruct (band (snd t) =? c); cbv iota; lia.
Qed.

Lemma xf_ff {X Y : Type} (P : X -> bool) (F : X -> list Y) (p : Y -> bool) l :
  (length (filter p (flat_map (fun x => if P x then F x else []) l)) <= length (filter p (flat_map F l)))%nat.
Proof.
  induction l as [|x l IH]; [cbn; lia|]. cbn [flat_map]. cbv beta. rewrite !filter_app, !length_app.
  destruct (P x); cbn [filter length]; lia.
Qed.

Lemma xf_upc s c : upc s c <= bcount s (c - 1).
Proof.
  unfold upc, bcount. apply Nat2Z.inj_le.
  exact (xf_ff (fun gm : sptr * ameta => (am_sc (snd gm) =? c) && (1 <=? am_last (snd gm)))
    (fun gm : sptr * ameta => YO0s.blocks_of0 (snd gm)) (fun b : sptr * Z => band (snd b) =? c - 1) (used_metas s)).
Qed.

Lemma res_ok_pack3_exit A b L' y : res_ok_pack3 A b -> UPB3 A L' [] -> length L' = 49%nat ->
  (forall k, 0 <= k < 49 -> 0 <= znth k L' <= znth k (p3_cap b)) -> ubytes A <= y -> 0 <= y ->
  res_ok_pack3 A (PB3 L' y (p3_cap b) [] (p3_mcap b)).
Proof.
  intros (HII & HSI & HGS & HNL & HNR & HMB & HPK & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hbd & Hby & Hh)
    HU HL HB Hy Hy0.
  unfold res_ok_pack3. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj HII (conj HSI (conj HGS (conj HNL (conj HNR (conj HMB (conj HPK (conj HPC (conj HU _))))))))).
  split.
  { split; [cbn [map]; constructor|]. split; [intros e []|].
    intros c Hc. unfold count_mis. cbn [filter length]. pose proof (proj2 (Hbd c ltac:(lia))). lia. }
  split; [exact Hy|]. split; [exact HL|]. split; [exact HlC|]. split; [exact HlM|].
  split; [intros k Hk; split; [exact (HB k Hk)|exact (proj2 (Hbd k Hk))]|]. split; [exact Hy0|exact Hh].
Qed.

Theorem RI3_end_x E b0 k V L A T' :
  WF (ss_A E) -> res_ok_pack3 (ss_A E) b0 ->
  pack_entry CS_reply (ss_pl E) (ss_T E) (PB (p3_live b0) (p3_bytes b0) (p3_cap b0)) ->
  tb_live (ss_L E) (ss_A E) (ss_T E) ->
  RI3_reply E k V L A -> List.NoDup (map fst (blocks L A)) ->
  (forall t, In t (blocks L A) -> (In t (blocks (ss_L E) (ss_A E)) /\ ~ In t (ss_T E)) \/ In t T') ->
  (length T' <= 2)%nat -> (forall t, In t T' -> 0 < snd t <= TBBYTES) ->
  res_ok_pack3 A (PB3 (pb_live (TDP (ss_T E) T' (PB (p3_live b0) (p3_bytes b0) (p3_cap b0))))
    (pb_bytes (TDP (ss_T E) T' (PB (p3_live b0) (p3_bytes b0) (p3_cap b0)))) (CS_reply (ss_pl E)) [] MC_reply).
Proof.
  intros HW HR0 HPE HTL0 HRI HND HPV HT'l HT's.
  destruct HRI as (b & al & alb & HR & HC & HMC & _).
  destruct HPE as (_ & _ & d & Hd & HLv & HBy). pose proof Hd as (DL & D0 & DS & DB).
  destruct HTL0 as (NDT & INT). first [apply NoDup_ListNoDup in NDT|idtac].
  destruct (TDP_chain (ss_T E) T' (PB (p3_live b0) (p3_bytes b0) (p3_cap b0)) d HLv HBy) as [E1 E2].
  cbn [pb_live pb_bytes] in HLv, HBy.
  destruct HR0 as (_ & _ & _ & _ & _ & _ & _ & _ & (U1 & _) & _ & UB0 & _).
  rewrite HLv, TDP_live in U1. change (lv_fold (-1) [] (pb_live d)) with (pb_live d) in U1.
  rewrite HBy, TDP_bytes in UB0. change (tsum []) with 0 in UB0.
  rewrite E1, E2. rewrite <- HC, <- HMC.
  assert (HNX : List.NoDup (blocks L A)) by exact (NoDup_map_inv _ _ HND).
  assert (HT0 : forall t, In t T' -> 0 <= snd t) by (intros t Ht; pose proof (HT's t Ht); lia).
  assert (HS0 : forall t, In t (blocks (ss_L E) (ss_A E)) -> 0 <= snd t).
  { intros t Ht. unfold blocks in Ht. apply in_map_iff in Ht as (bk & <- & Hb). exact (ub_nonneg _ HW bk Hb). }
  assert (HTT : forall t, In t (ss_T E) -> 0 <= snd t) by (intros t Ht; exact (HS0 t (INT t Ht))).
  assert (CNT : forall c, 0 <= c < 49 -> bcount A c <= znth c (lv_fold 1 T' (pb_live d))).
  { intros c Hc. rewrite (xf_lv T' (pb_live d) c DL ltac:(lia) HT0).
    pose proof (U1 c Hc) as U. rewrite (xf_lv (ss_T E) (pb_live d) c DL ltac:(lia) HTT) in U.
    rewrite (xf_bcount (ss_L E)) in U. rewrite (xf_bcount L).
    pose proof (xf_sum (fun t : Z * Z => if band (snd t) =? c then 1 else 0) (blocks L A)
      (blocks (ss_L E) (ss_A E)) (ss_T E) T' HNX NDT INT
      ltac:(intros t _; cbv beta; destruct (band (snd t) =? c); cbv iota; lia)
      ltac:(intros t _; cbv beta; destruct (band (snd t) =? c); cbv iota; lia) HPV).
    lia. }
  apply res_ok_pack3_exit; [exact HR| | | | |].
  - rewrite TDP_live. change (lv_fold (-1) [] (pb_live d)) with (pb_live d).
    split; [exact CNT|]. intros c Hc. unfold mis_in. cbn [filter length].
    pose proof (xf_upc A c) as UP. pose proof (CNT c ltac:(lia)) as C1. pose proof (CNT (c - 1) ltac:(lia)) as C2.
    rewrite (xf_lv T' (pb_live d) (c - 1) DL ltac:(lia) HT0) in C2.
    pose proof (drv_live_le d (c - 1) Hd ltac:(lia)). pose proof (xf_cnt (c - 1) T').
    unfold COARSE. lia.
  - rewrite TDP_live. change (lv_fold (-1) [] (pb_live d)) with (pb_live d). rewrite lv_fold_length. exact DL.
  - intros c Hc. rewrite TDP_live. change (lv_fold (-1) [] (pb_live d)) with (pb_live d).
    pose proof (live_fold_le T' (pb_live d) c ltac:(lia) HT0) as (F1 & F2).
    pose proof (drv_live_le d c Hd Hc). rewrite HC, CS_reply_at by exact Hc. pose proof (cs_band_ge (ss_pl E) c).
    unfold PCAP0 in *. lia.
  - rewrite TDP_bytes. change (tsum []) with 0.
    rewrite (xf_ubytes (ss_L E)) in UB0. rewrite (xf_ubytes L).
    pose proof (xf_sum snd (blocks L A) (blocks (ss_L E) (ss_A E)) (ss_T E) T' HNX NDT INT HS0 HT0 HPV).
    change (tsum T') with (zsum snd T'). change (tsum (ss_T E)) with (zsum snd (ss_T E)) in UB0. lia.
  - rewrite TDP_bytes. change (tsum []) with 0.
    assert (HTs' : forall t, In t T' -> 0 <= snd t <= TBBYTES) by (intros t Ht; pose proof (HT's t Ht); lia).
    pose proof (tsum_bounds T' TBBYTES HTs'). lia.
Qed.

Lemma ncsz_none (l : list (Z * Z)) q : ~ In q (map fst l) -> zsum snd (filter (fun t => fst t =? q) l) = 0.
Proof.
  induction l as [|[a m] l IH]; intros H; [reflexivity|]. cbn [map fst filter] in *.
  destruct (Z.eqb_spec a q) as [->|Hne]; [exfalso; apply H; left; reflexivity|].
  cbv beta iota. apply IH. intros X. apply H. right. exact X.
Qed.

Lemma ncsz_le (l : list (Z * Z)) q X : List.NoDup (map fst l) -> 0 <= X -> (forall m, In (q, m) l -> m <= X) ->
  zsum snd (filter (fun t => fst t =? q) l) <= X.
Proof.
  induction l as [|[a m] l IH]; intros HN HX H; [exact HX|].
  cbn [map fst] in HN. apply NoDup_cons_iff in HN as [Ha HN]. cbn [filter fst].
  destruct (Z.eqb_spec a q) as [->|Hne]; cbv beta iota.
  - rewrite zsum_cons, (ncsz_none l q Ha). cbn [snd]. pose proof (H m (or_introl eq_refl)). lia.
  - apply IH; [exact HN|exact HX|]. intros m' Hm. apply H. right. exact Hm.
Qed.

Lemma nc_sz_le L A q X : List.NoDup (map fst (blocks L A)) -> 0 <= X ->
  (forall m, In (q, m) (blocks L A) -> m <= X) -> nc_sz L A q <= X.
Proof. intros HN HX H. unfold nc_sz. exact (ncsz_le _ q X HN HX H). Qed.

Theorem RI3_start_ok : RI_start RI3_reply CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E (FF & _ & HP & _) C G CAP OUT HT HC HCAP HOUT.
  destruct HP as (PRE & HR & (HPE & HMC) & HMS & HGI & HTL & _).
  destruct PRE as ((HM & HW & _) & _).
  destruct (GI_t_bound _ _ _ HGI) as (HTl & HTk).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (ND : List.NoDup (map fst (blocks (ss_L E) (ss_A E)))).
  { assert (X : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
    exact (proj1 (NoDup_ListNoDup _) (X _ _ _ _ HM)). }
  destruct HTL as (NDT & INT). first [apply NoDup_ListNoDup in NDT|idtac].
  assert (HS0 : forall t, In t (blocks (ss_L E) (ss_A E)) -> 0 <= snd t).
  { intros t Ht. unfold blocks in Ht. apply in_map_iff in Ht as (bk & <- & Hb). exact (ub_nonneg _ HW bk Hb). }
  assert (NZ : forall m, ~ In (0, m) (blocks (ss_L E) (ss_A E))).
  { intros m Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & Ep & Hp). cbn [fst snd] in Ep.
    inversion Ep as [[E0 E1]]. pose proof (mr_blocks_range _ _ (aa_laws (API rc)) _ _ _ _ p n HM Hp) as [R _].
    lia. }
  assert (HTs : forall t, In t (ss_T E) -> In (fst t) [G; OUT]).
  { intros t Ht. rewrite HT in Ht. unfold kept_blocks in Ht. apply in_app_or in Ht as [Ht|Ht].
    - destruct (C =? 16); cbn in Ht; [destruct Ht as [<-|[]]; left; reflexivity|destruct Ht].
    - destruct (CAP =? 0); cbn in Ht; [destruct Ht|destruct Ht as [<-|[]]; right; left; reflexivity]. }
  pose proof (ncs_ge_tsum (ss_L E) (ss_A E) [G; OUT] (ss_T E) NDT INT HS0 HTs) as S1.
  assert (XG : nc_sz (ss_L E) (ss_A E) G <= SRC_TABLE_BYTES).
  { apply nc_sz_le; [exact ND|unfold SRC_TABLE_BYTES; lia|]. intros m Hm.
    destruct HC as [(_ & HG0)|HC16]; [rewrite HG0 in Hm; destruct (NZ m Hm)|].
    assert (IG : In (G, SRC_TABLE_BYTES) (ss_T E)).
    { rewrite HT, HC16. unfold kept_blocks. apply in_or_app. left. left. reflexivity. }
    pose proof (nodup_map_eq fst _ (G, m) (G, SRC_TABLE_BYTES) ND Hm (INT _ IG) eq_refl) as EQ.
    pose proof (f_equal snd EQ) as EQ2. cbn [snd] in EQ2. lia. }
  assert (XO : nc_sz (ss_L E) (ss_A E) OUT <= TBBYTES).
  { apply nc_sz_le; [exact ND|apply Z.leb_le; vm_compute; reflexivity|]. intros m Hm.
    destruct (Z.eqb_spec CAP 0) as [C0|C0]; [rewrite (HOUT C0) in Hm; destruct (NZ m Hm)|].
    assert (IO : In (OUT, CAP) (ss_T E)).
    { rewrite HT. unfold kept_blocks. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq CAP 0) C0).
      left. reflexivity. }
    pose proof (nodup_map_eq fst _ (OUT, m) (OUT, CAP) ND Hm (INT _ IO) eq_refl) as EQ.
    pose proof (f_equal snd EQ) as EQ2. cbn [snd] in EQ2. lia. }
  assert (S2 : ncs (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E) <= NC_FIX).
  { assert (NCF : SRC_TABLE_BYTES + TBBYTES <= NC_FIX) by (apply Z.leb_le; vm_compute; reflexivity).
    unfold ncs. cbn [rv_nc]. rewrite !zsum_cons, zsum_nil. lia. }
  exact (RI3_start E (ss_b E) (ss_T E) G OUT HR HPE HMC HMS HTl HTk S1 S2).
Qed.

Theorem RI3_end_ok : RI_end RI3_reply CS_reply.
Proof.
  intros B API LS SH SK ra empty rc fx j E (_ & _ & HP & _) k V L A T' HRI HND HPV HT'l HT's.
  destruct HP as (PRE & HR0 & (HPE & _) & _ & _ & HTL0 & _).
  destruct PRE as ((_ & HW & _) & _).
  exact (RI3_end_x E (ss_b E) k V L A T' HW HR0 HPE HTL0 HRI HND HPV HT'l HT's).
Qed.
