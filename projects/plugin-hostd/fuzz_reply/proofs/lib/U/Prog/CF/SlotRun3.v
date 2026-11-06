From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF ListTr.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Abbreviation run3 qs b j tr := (run_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc qs b j tr).

Abbreviation room3 qs b j tr := (room_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc room_pack3 qs b j tr).

Definition ev_dl (e : tev) (c : Z) : Z :=
  match e with
  | RMalloc n => one_if c (band n)
  | RFree n _ => - one_if c (band n)
  | RRealloc k n _ => one_if c (band n) - one_if c (band k)
  end.

Definition ev_db (e : tev) : Z :=
  match e with
  | RMalloc n => n
  | RFree n _ => - n
  | RRealloc k n _ => n - k
  end.

Definition ev_ok (e : tev) : Prop :=
  match e with
  | RMalloc n => 0 <= n
  | RFree n _ => 0 <= n
  | RRealloc k n _ => 0 <= k /\ 0 <= n
  end.

Definition ev_grow (e : tev) : Prop := match e with RRealloc k n _ => k <= n | _ => True end.

Definition ev_free (e : tev) : Prop := match e with RFree _ _ => True | _ => False end.

Definition tr_dl (tr : list tev) (c : Z) : Z := zsum (fun e => ev_dl e c) tr.

Definition tr_db (tr : list tev) : Z := zsum ev_db tr.

Definition bcnt (c : Z) (ks : list Z) : Z := zsum (fun n => one_if c (band n)) ks.

Definition al_add (al ks : list Z) : list Z := fold_left (fun a n => lv_add a (band n) 1) ks al.

Definition call_step (NW : rview -> Z) (pl : list byte) (k' : Z) (V : rview) (L : layout) (A : astate) (V' : rview)
    (L' : layout) (A' : astate) (al : list Z) (alb : Z) (ks : list Z) (dl : Z -> Z) (db : Z) : Prop :=
  (length (rv_nc V') <= NC_MAX)%nat /\
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + dl c <= nc_cnt V' L' A' c) /\ ncs V L A + db <= ncs V' L' A' /\
  ncs V' L' A' <= NW V' /\ NW V' <= NC_FIX + NC_PER * (alsum al + zlen ks) + DATA_PER * cdat pl k' /\
  (forall c, 0 <= c < 49 -> znth c al + bcnt c ks + ek_c V' c + prom_c (rv_pend V') c <= cons_c pl k' c) /\
  alb + zsum (fun n => n) ks + ek_b V' + promb (rv_pend V') <= consb pl k' /\ Forall (fun n => 0 <= n) (rv_ek V').

Lemma runF3 qs b tr : runF pack3_form qs b tr = run3 qs b 0 tr.
Proof. reflexivity. Qed.

Lemma roomF3 qs b tr : roomF pack3_form qs b tr = room3 qs b 0 tr.
Proof. reflexivity. Qed.

Lemma run3_cap qs b j tr : p3_cap (run3 qs b j tr) = p3_cap b.
Proof.
  revert b j. induction tr as [|e tr IH]; intros b j; [reflexivity|].
  destruct e; cbn [run_from]; rewrite IH; reflexivity.
Qed.

Lemma run3_mcap qs b j tr : p3_mcap (run3 qs b j tr) = p3_mcap b.
Proof.
  revert b j. induction tr as [|e tr IH]; intros b j; [reflexivity|].
  destruct e; cbn [run_from]; rewrite IH; reflexivity.
Qed.

Lemma run3_len qs b j tr : length (p3_live (run3 qs b j tr)) = length (p3_live b).
Proof.
  revert b j. induction tr as [|e tr IH]; intros b j; [reflexivity|].
  destruct e; cbn [run_from]; rewrite IH; unfold pb3_malloc, pb3_free, pb3_realloc; cbn [p3_live];
    rewrite ?lv_add_length; reflexivity.
Qed.

Lemma run3_bytes qs b j tr : p3_bytes (run3 qs b j tr) = p3_bytes b + tr_db tr.
Proof.
  unfold tr_db. revert b j. induction tr as [|e tr IH]; intros b j.
  - cbn [run_from]. rewrite zsum_nil. lia.
  - rewrite zsum_cons. destruct e; cbn [run_from]; rewrite IH; unfold pb3_malloc, pb3_free, pb3_realloc;
      cbn [p3_bytes ev_db]; lia.
Qed.

Lemma run3_live qs b j tr c : length (p3_live b) = 49%nat -> Forall ev_ok tr -> 0 <= c < 49 ->
  znth c (p3_live (run3 qs b j tr)) = znth c (p3_live b) + tr_dl tr c.
Proof.
  unfold tr_dl. revert b j. induction tr as [|e tr IH]; intros b j Hl Hok Hc.
  - cbn [run_from]. rewrite zsum_nil. lia.
  - apply Forall_cons_iff in Hok as [He Hok]. rewrite zsum_cons.
    destruct e as [n|n a|k n a]; cbn [run_from ev_dl]; cbn [ev_ok] in He.
    + pose proof (band_range n He) as Bn.
      rewrite IH; [|unfold pb3_malloc; cbn [p3_live]; rewrite lv_add_length; exact Hl|exact Hok|exact Hc].
      unfold pb3_malloc. cbn [p3_live]. rewrite znth_lv_add_d by (first [exact Hl|lia]). lia.
    + pose proof (band_range n He) as Bn.
      rewrite IH; [|unfold pb3_free; cbn [p3_live]; rewrite lv_add_length; exact Hl|exact Hok|exact Hc].
      unfold pb3_free. cbn [p3_live]. rewrite znth_lv_add_d by (first [exact Hl|lia]). lia.
    + pose proof (band_range n (proj2 He)) as Bn. pose proof (band_range k (proj1 He)) as Bk.
      rewrite IH; [|unfold pb3_realloc; cbn [p3_live]; rewrite !lv_add_length; exact Hl|exact Hok|exact Hc].
      unfold pb3_realloc. cbn [p3_live].
      rewrite znth_lv_add_d by (first [rewrite lv_add_length; exact Hl|lia]).
      rewrite znth_lv_add_d by (first [exact Hl|lia]). lia.
Qed.

Lemma cou_step3 : forallb (fun k => class_of_units k <=? class_of_units (k + 1)) (zseq 0 8190) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cou_mono3 a b : 0 <= a <= b -> b < 8191 -> class_of_units a <= class_of_units b.
Proof.
  intros Hab Hb. pose proof cou_step3 as T. rewrite forallb_forall in T.
  assert (G : forall n : nat, forall x, 0 <= x -> x + Z.of_nat n < 8191 ->
                class_of_units x <= class_of_units (x + Z.of_nat n)).
  { induction n as [|n IH]; intros x Hx Hn.
    - rewrite Z.add_0_r. lia.
    - specialize (IH x Hx ltac:(lia)).
      specialize (T (x + Z.of_nat n) (proj2 (In_zseq 0 8190 (x + Z.of_nat n)) ltac:(lia))).
      apply Z.leb_le in T. replace (x + Z.of_nat (S n)) with (x + Z.of_nat n + 1) by lia. lia. }
  replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia. apply G; lia.
Qed.

Lemma band_mono3 m n : 0 <= m <= n -> band m <= band n.
Proof.
  intros H. destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hs|Hs].
  - destruct (band_units m ltac:(lia)) as (Em & Hkm & Hrm).
    destruct (band_units n ltac:(lia)) as (En & Hkn & Hrn).
    rewrite Em, En. apply cou_mono3; lia.
  - pose proof (band_range m ltac:(lia)). unfold band at 2. rewrite (proj2 (Z.leb_le _ _) Hs). lia.
Qed.

Lemma count_mis_filter (M : list (sptr * Z)) f c : count_mis (filter f M) c <= count_mis M c.
Proof.
  unfold count_mis. induction M as [|e M IH]; [cbn; lia|]. cbn [filter].
  destruct (f e); cbn [filter]; destruct (snd e =? c); cbn [length]; lia.
Qed.

Lemma filter_split_len {X} (f g : X -> bool) (l : list X) :
  (length (filter f (filter g l)) + length (filter (fun x => f x && negb (g x)) l) = length (filter f l))%nat.
Proof.
  induction l as [|x l IH]; [reflexivity|]. cbn [filter].
  destruct (g x) eqn:Eg; destruct (f x) eqn:Ef; cbn [filter andb negb length]; rewrite ?Ef; cbn [length]; lia.
Qed.

Lemma count_mis_realloc M k n p q c : 0 <= k <= n -> count_mis (mis_realloc M k n p q) c <= count_mis M c.
Proof.
  intros Hkn. pose proof (band_mono3 k n Hkn) as Bm. unfold mis_realloc.
  match goal with |- context [if ?t then _ else _] => destruct t eqn:E end; [|apply count_mis_filter].
  apply andb_true_iff in E as [_ E]. apply orb_true_iff in E as [E|E]; [apply Z.eqb_eq in E; lia|].
  destruct (mis_lookup M p) as [c0|] eqn:Hl; [|discriminate]. apply Z.eqb_eq in E. subst c0.
  unfold mis_lookup in Hl. destruct (find (fun e => sptr_eqb (fst e) p) M) as [e|] eqn:Hf; [|discriminate].
  cbn [option_map] in Hl. injection Hl as He. apply find_some in Hf as [Hin Hp]. cbv beta in Hp.
  unfold count_mis, mis_del. cbn [filter snd].
  pose proof (filter_split_len (fun e0 : sptr * Z => snd e0 =? c) (fun e0 => negb (sptr_eqb (fst e0) p)) M) as S.
  cbv beta in S.
  destruct (Z.eqb_spec (band n + 1) c) as [Ec|Ec]; cbn [length]; [|lia].
  assert (L1 : (1 <= length (filter (fun x => Z.eqb (snd x) c && negb (negb (sptr_eqb (fst x) p))) M))%nat).
  { destruct (filter (fun x => (snd x =? c) && negb (negb (sptr_eqb (fst x) p))) M) as [|y ys] eqn:EF;
      [|cbn [length]; lia].
    exfalso. assert (X : In e (filter (fun x => (snd x =? c) && negb (negb (sptr_eqb (fst x) p))) M)).
    { apply filter_In. split; [exact Hin|]. cbv beta. rewrite He, Ec, Z.eqb_refl, Hp. reflexivity. }
    rewrite EF in X. destruct X. }
  lia.
Qed.

Lemma run3_mis qs b j tr c : Forall ev_ok tr -> Forall ev_grow tr ->
  count_mis (p3_mis (run3 qs b j tr)) c <= count_mis (p3_mis b) c.
Proof.
  revert b j. induction tr as [|e tr IH]; intros b j Hok Hg; [cbn [run_from]; lia|].
  apply Forall_cons_iff in Hok as [He Hok]. apply Forall_cons_iff in Hg as [Hge Hg].
  destruct e as [n|n a|k n a]; cbn [run_from ev_ok ev_grow] in *.
  - exact (IH _ _ Hok Hg).
  - eapply Z.le_trans; [exact (IH _ _ Hok Hg)|]. unfold pb3_free. cbn [p3_mis]. apply count_mis_filter.
  - eapply Z.le_trans; [exact (IH _ _ Hok Hg)|]. unfold pb3_realloc. cbn [p3_mis]. apply count_mis_realloc. lia.
Qed.

Lemma room3_inv (Iv : pbound3 -> Prop) qs tr :
  (forall b n, Iv b -> In (RMalloc n) tr -> room_pack3 b n /\ Iv (pb3_malloc b n)) ->
  (forall b n a p, Iv b -> In (RFree n a) tr -> Iv (pb3_free b n p)) ->
  (forall b k n a p q, Iv b -> In (RRealloc k n a) tr -> room_pack3 b n /\ Iv (pb3_realloc b k n p q)) ->
  forall b j, Iv b -> room3 qs b j tr.
Proof.
  induction tr as [|e tr IH]; intros HM HF HR b j Hb; [exact I|].
  assert (IH' : forall b j, Iv b -> room3 qs b j tr).
  { apply IH.
    - intros b' n Hb' Hin. exact (HM b' n Hb' (or_intror Hin)).
    - intros b' n a p Hb' Hin. exact (HF b' n a p Hb' (or_intror Hin)).
    - intros b' k n a p q Hb' Hin. exact (HR b' k n a p q Hb' (or_intror Hin)). }
  destruct e as [n|n a|k n a]; cbn [room_from].
  - destruct (HM b n Hb (or_introl eq_refl)) as [R1 R2]. split; [exact R1|exact (IH' _ _ R2)].
  - exact (IH' _ _ (HF b n a _ Hb (or_introl eq_refl))).
  - destruct (HR b k n a (resolve sptr (SP 0 0) qs a) (nth j qs (SP 0 0)) Hb (or_introl eq_refl)) as [R1 R2].
    split; [exact R1|exact (IH' _ _ R2)].
Qed.

Lemma roomF_frees F qs b tr : Forall ev_free tr -> roomF F qs b tr.
Proof.
  unfold roomF, room_run. generalize 0%nat. revert b. induction tr as [|e tr IH]; intros b j H; [exact I|].
  apply Forall_cons_iff in H as [He H]. destruct e; cbn [ev_free] in He; [contradiction| |contradiction].
  cbn [room_from]. apply IH, H.
Qed.

Lemma recs_drop_free rs : Forall ev_free (recs_drop_tr rs).
Proof.
  induction rs as [|r rs IH]; [constructor|]. unfold recs_drop_tr in *. cbn [map concat].
  apply Forall_app. split; [|exact IH]. constructor; [exact I|constructor].
Qed.

Lemma recs_drop_ok rs : Forall ev_ok (recs_drop_tr rs) /\ Forall ev_grow (recs_drop_tr rs).
Proof.
  induction rs as [|r rs [IH1 IH2]]; [split; constructor|]. unfold recs_drop_tr in *. cbn [map concat].
  change (rec_drop_tr r) with [RFree (rec_len r) (fst r)]. cbn [app].
  split; constructor; [cbn [ev_ok]; unfold rec_len; lia|exact IH1|exact I|exact IH2].
Qed.

Lemma tr_dl_app t1 t2 c : tr_dl (t1 ++ t2) c = tr_dl t1 c + tr_dl t2 c.
Proof. unfold tr_dl. apply zsum_app. Qed.

Lemma tr_db_app t1 t2 : tr_db (t1 ++ t2) = tr_db t1 + tr_db t2.
Proof. unfold tr_db. apply zsum_app. Qed.

Lemma bcnt_app c k1 k2 : bcnt c (k1 ++ k2) = bcnt c k1 + bcnt c k2.
Proof. unfold bcnt. apply zsum_app. Qed.

Lemma bcnt_cons c n ks : bcnt c (n :: ks) = one_if c (band n) + bcnt c ks.
Proof. unfold bcnt. rewrite zsum_cons. reflexivity. Qed.

Lemma tr_dl_one e c : tr_dl [e] c = ev_dl e c.
Proof. unfold tr_dl, zsum. cbn [fold_right]. lia. Qed.

Lemma tr_db_one e : tr_db [e] = ev_db e.
Proof. unfold tr_db, zsum. cbn [fold_right]. lia. Qed.

Lemma recs_drop_dl rs c : tr_dl (recs_drop_tr rs) c = - bcnt c (map rec_len rs).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. unfold recs_drop_tr in *. cbn [map concat].
  change (rec_drop_tr r) with [RFree (rec_len r) (fst r)].
  rewrite tr_dl_app, IH, tr_dl_one, bcnt_cons. cbn [ev_dl]. lia.
Qed.

Lemma recs_drop_db rs : tr_db (recs_drop_tr rs) = - zsum (fun n => n) (map rec_len rs).
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. unfold recs_drop_tr in *. cbn [map concat].
  change (rec_drop_tr r) with [RFree (rec_len r) (fst r)].
  rewrite tr_db_app, IH, tr_db_one, zsum_cons. cbn [ev_db]. lia.
Qed.

Lemma bcnt_nonneg c ks : 0 <= bcnt c ks.
Proof. apply zsum_nonneg. intros n _. exact (proj1 (one_if_b c (band n))). Qed.

Lemma bcnt_le c ks : bcnt c ks <= zlen ks.
Proof.
  unfold bcnt, zlen. induction ks as [|n ks IH]; [cbn; lia|]. rewrite zsum_cons. cbn [length].
  pose proof (one_if_b c (band n)). lia.
Qed.

Lemma zsum_id_nonneg ks : Forall (fun n => 0 <= n) ks -> 0 <= zsum (fun n => n) ks.
Proof. intros H. apply zsum_nonneg. intros n Hn. rewrite Forall_forall in H. exact (H n Hn). Qed.

Lemma al_add_len al ks : length (al_add al ks) = length al.
Proof.
  revert al. induction ks as [|n ks IH]; intros al; [reflexivity|].
  change (al_add al (n :: ks)) with (al_add (lv_add al (band n) 1) ks). rewrite IH. apply lv_add_length.
Qed.

Lemma al_add_at al ks c : length al = 49%nat -> Forall (fun n => 0 <= n) ks -> 0 <= c ->
  znth c (al_add al ks) = znth c al + bcnt c ks.
Proof.
  unfold bcnt. revert al. induction ks as [|n ks IH]; intros al Hl Hks Hc;
    [change (al_add al []) with al; rewrite zsum_nil; lia|].
  apply Forall_cons_iff in Hks as [Hn Hks]. pose proof (band_range n Hn) as Bn.
  change (al_add al (n :: ks)) with (al_add (lv_add al (band n) 1) ks).
  rewrite IH by (first [rewrite lv_add_length; exact Hl|exact Hks|exact Hc]).
  rewrite znth_lv_add_d by (first [exact Hl|lia]). rewrite zsum_cons. lia.
Qed.

Lemma al_add_sum al ks : length al = 49%nat -> Forall (fun n => 0 <= n) ks -> alsum (al_add al ks) = alsum al + zlen ks.
Proof.
  unfold zlen. revert al. induction ks as [|n ks IH]; intros al Hl Hks;
    [change (al_add al []) with al; cbn [length]; lia|].
  apply Forall_cons_iff in Hks as [Hn Hks]. pose proof (band_range n Hn) as Bn.
  change (al_add al (n :: ks)) with (al_add (lv_add al (band n) 1) ks).
  rewrite IH by (first [rewrite lv_add_length; exact Hl|exact Hks]).
  rewrite alsum_lv_add by (first [exact Hl|lia]). cbn [length]. lia.
Qed.

Theorem ledger3_call NW pl k V L A b al alb k' V' L' A' b' ks dl db :
  RI3_ledger NW pl k V L A b al alb -> Forall (fun n => 0 <= n) ks ->
  call_step NW pl k' V L A V' L' A' al alb ks dl db ->
  p3_cap b' = p3_cap b -> p3_mcap b' = p3_mcap b -> length (p3_live b') = 49%nat ->
  (forall c, 0 <= c < 49 -> znth c (p3_live b') <= znth c (p3_live b) + bcnt c ks + dl c) ->
  p3_bytes b' <= p3_bytes b + zsum (fun n => n) ks + db -> mis_nc V' L' (p3_mis b') ->
  RI3_ledger NW pl k' V' L' A' b' (al_add al ks) (alb + zsum (fun n => n) ks).
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H) Hks
    (HN' & HC' & HB' & HW1' & HW2' & HP' & HQ' & HE') Hcap Hmc Hl Hlive Hby HMis'.
  pose proof (zsum_id_nonneg ks Hks) as Z0.
  split; [rewrite Hcap; exact HC|]. split; [rewrite Hmc; exact HM|]. split; [exact HN'|]. split; [exact Hl|].
  split; [rewrite al_add_len; exact HL|]. split; [lia|]. split; [exact HE'|]. split; [lia|]. split; [exact HW1'|].
  split; [rewrite al_add_sum by (first [exact HL|exact Hks]); exact HW2'|].
  split; [lia|]. split; [exact HMis'|].
  intros c Hc. destruct (H c Hc) as (H1 & H2 & H3). pose proof (Hlive c Hc). pose proof (HC' c Hc).
  pose proof (HP' c Hc). pose proof (bcnt_nonneg c ks).
  rewrite al_add_at by (first [exact HL|exact Hks|lia]). lia.
Qed.

Lemma ledger3_margin NW pl k V L A b al alb c d : RI3_ledger NW pl k V L A b al alb -> 0 <= c < 49 ->
  znth c al + d + prom_c (rv_pend V) c <= cons_c pl k c -> znth c (p3_live b) + d + 100 <= znth c (p3_cap b).
Proof.
  intros (HC & _ & HN & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) Hc Hd. destruct (H c Hc) as (H1 & H2 & H3).
  pose proof (cons_le pl k c). pose proof (prom_c_nonneg (rv_pend V) c). pose proof (nc_cnt_bounds V L A c).
  assert (Z.of_nat (length (rv_nc V)) <= 26) by (unfold NC_MAX in HN; lia).
  rewrite HC, CS_reply_at by exact Hc.
  unfold cs_band. destruct (Z.eqb_spec c 0) as [E|E]; cbv beta iota.
  - subst c. pose proof (x0_bound pl). unfold CAPS0, RI_BASE, BTEXT in *. lia.
  - unfold CBASE, RI_BASE in *. lia.
Qed.

Lemma room3_at pl b n : p3_cap b = CS_reply pl -> p3_mcap b = MC_reply -> 0 <= n <= NMAX -> p3_bytes b + n <= BMAX ->
  znth (band n) (p3_live b) + 1 <= znth (band n) (p3_cap b) ->
  (forall c, 0 <= c < 49 -> count_mis (p3_mis b) c + 1 <= MC_ONE) -> room_pack3 b n.
Proof.
  intros HC HM Hn HB HL HMis. pose proof (band_range n ltac:(lia)) as Bn.
  apply (room_pack3_of b n BMAX NMAX); [rewrite HC, HM; apply CS_reply_capok3|lia|exact HB|exact HL|].
  intros Hb. rewrite HM, MC_reply_at by lia. apply HMis. lia.
Qed.

Lemma ledger3_credit NW pl k V L A b al alb c : RI3_ledger NW pl k V L A b al alb -> 0 <= c < 49 ->
  znth c al + ek_c V c + prom_c (rv_pend V) c <= cons_c pl k c.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) Hc. exact (proj2 (proj2 (H c Hc))). Qed.

Lemma ledger3_creditb NW pl k V L A b al alb : RI3_ledger NW pl k V L A b al alb ->
  alb + ek_b V + promb (rv_pend V) <= consb pl k.
Proof. intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ek_c_view G OUT es hj c : ek_c (view_of G OUT es hj) c = bcnt c (ek_view hj).
Proof. reflexivity. Qed.

Lemma ek_b_view G OUT es hj : ek_b (view_of G OUT es hj) = zsum (fun n => n) (ek_view hj).
Proof. reflexivity. Qed.

Lemma ek_view_app hj1 p hj2 :
  ek_view (hj1 ++ p :: hj2) = ek_view hj1 ++ ekeys_hl (HarnessRep.hs_expected (fst p)) ++ ek_view hj2.
Proof. unfold ek_view. rewrite map_app, concat_app. reflexivity. Qed.

Lemma ek_view_in G OUT es hj p c : In p hj ->
  bcnt c (ekeys_hl (HarnessRep.hs_expected (fst p))) <= ek_c (view_of G OUT es hj) c.
Proof.
  intros Hin. apply in_split in Hin as (hj1 & hj2 & ->). rewrite ek_c_view, ek_view_app, !bcnt_app.
  pose proof (bcnt_nonneg c (ek_view hj1)). pose proof (bcnt_nonneg c (ek_view hj2)). lia.
Qed.

Lemma ek_view_in_b G OUT es hj p : In p hj ->
  zsum (fun n => n) (ekeys_hl (HarnessRep.hs_expected (fst p))) <= ek_b (view_of G OUT es hj).
Proof.
  intros Hin. apply in_split in Hin as (hj1 & hj2 & ->). rewrite ek_b_view, ek_view_app, !zsum_app.
  pose proof (zsum_id_nonneg _ (ek_view_nonneg hj1)). pose proof (zsum_id_nonneg _ (ek_view_nonneg hj2)). lia.
Qed.

Lemma ekeys_hl_nil l : HarnessRep.hl_recs l = [] -> ekeys_hl l = [].
Proof. intros H. unfold ekeys_hl. rewrite H. reflexivity. Qed.

Lemma ek_view_clear G OUT es G' OUT' es' hj1 p p' hj2 c :
  HarnessRep.hl_recs (HarnessRep.hs_expected (fst p')) = [] ->
  ek_c (view_of G' OUT' es' (hj1 ++ p' :: hj2)) c + bcnt c (ekeys_hl (HarnessRep.hs_expected (fst p))) =
  ek_c (view_of G OUT es (hj1 ++ p :: hj2)) c.
Proof.
  intros H0. rewrite !ek_c_view, !ek_view_app, (ekeys_hl_nil _ H0). cbn [app]. rewrite !bcnt_app. lia.
Qed.

Lemma ek_view_clear_b G OUT es G' OUT' es' hj1 p p' hj2 :
  HarnessRep.hl_recs (HarnessRep.hs_expected (fst p')) = [] ->
  ek_b (view_of G' OUT' es' (hj1 ++ p' :: hj2)) + zsum (fun n => n) (ekeys_hl (HarnessRep.hs_expected (fst p))) =
  ek_b (view_of G OUT es (hj1 ++ p :: hj2)).
Proof.
  intros H0. rewrite !ek_b_view, !ek_view_app, (ekeys_hl_nil _ H0). cbn [app]. rewrite !zsum_app. lia.
Qed.
