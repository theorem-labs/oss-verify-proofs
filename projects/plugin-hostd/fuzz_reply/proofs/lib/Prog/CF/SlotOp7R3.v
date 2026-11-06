From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT AllocPack AllocPack3
  AllocPack3Room.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c relay_event_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition op7_trT (EL : Z) (live : bool) (mx CAP : Z) (o : adrF) : trF :=
  RMalloc (EL + 1) :: relay_event_tr live mx 0 CAP EL 1 o ++ [RFree (EL + 1) (Ret 0)].

Definition op7_capT (live : bool) (mx CAP EL : Z) : Z := send_line_cap live mx 0 CAP (EL + 1).

Definition op7_outT (live : bool) (mx CAP EL : Z) (o : adrF) : adrF := relay_event_out live mx 0 CAP EL 1 o.

Definition op7_dl (CAP CAP' : Z) (c : Z) : Z :=
  if CAP' =? CAP then 0 else one_if c (band CAP') - (if CAP =? 0 then 0 else one_if c (band CAP)).

Lemma op7_cou_step : forallb (fun k => class_of_units k <=? class_of_units (k + 1)) (zseq 0 8190) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma op7_cou_mono a b : 0 <= a <= b -> b < 8191 -> class_of_units a <= class_of_units b.
Proof.
  intros Hab Hb. pose proof op7_cou_step as T. rewrite forallb_forall in T.
  assert (G : forall n : nat, forall x, 0 <= x -> x + Z.of_nat n < 8191 ->
                class_of_units x <= class_of_units (x + Z.of_nat n)).
  { induction n as [|n IH]; intros x Hx Hn.
    - rewrite Z.add_0_r. lia.
    - specialize (IH x Hx ltac:(lia)).
      specialize (T (x + Z.of_nat n) (proj2 (In_zseq 0 8190 (x + Z.of_nat n)) ltac:(lia))).
      apply Z.leb_le in T. replace (x + Z.of_nat (S n)) with (x + Z.of_nat n + 1) by lia. lia. }
  replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia. apply G; lia.
Qed.

Lemma op7_band_mono m n : 0 <= m <= n -> band m <= band n.
Proof.
  intros H. destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hs|Hs].
  - destruct (SlotParse.band_units m ltac:(lia)) as (Em & Hkm & Hrm).
    destruct (SlotParse.band_units n ltac:(lia)) as (En & Hkn & Hrn).
    rewrite Em, En. apply op7_cou_mono; lia.
  - pose proof (AllocPackRoom.band_range m ltac:(lia)). unfold band at 2. rewrite (proj2 (Z.leb_le _ _) Hs).
    cbv beta iota. lia.
Qed.

Lemma op7_sl_shift : forall f mx no cap rem (j s : nat) (o : adrF),
  sl_run f mx no cap rem (s + j)%nat (shift_addr sptr s o) =
  (shift_tr sptr s (fst (sl_run f mx no cap rem j o)),
   (fst (snd (sl_run f mx no cap rem j o)), shift_addr sptr s (snd (snd (sl_run f mx no cap rem j o))))).
Proof.
  induction f as [|f IH]; intros mx no cap rem j s o; cbn [sl_run]; cbv zeta; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (cap <? no + n).
  - pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) s (Ret j)) as E.
    cbn [shift_addr] in E. rewrite Nat.add_succ_r in E. rewrite E. destruct (cap =? 0); reflexivity.
  - apply IH.
Qed.

Lemma op7_sl_cap : forall f mx no cap rem j o j' o',
  fst (snd (sl_run f mx no cap rem j o)) = fst (snd (sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; cbn [sl_run]; cbv zeta; [reflexivity|].
  destruct (rem <=? 0); [reflexivity|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (cap <? no + n); [cbn [fst snd]; apply IH|apply IH].
Qed.

Inductive op7_ch (M : Z) : Z -> adrF -> nat -> trF -> Z -> adrF -> Prop :=
| op7_ch_nil cap a j : op7_ch M cap a j [] cap a
| op7_ch_grow cap a j c tr cap' a' : 0 <= cap < c -> c <= M -> op7_ch M c (Ret j) (S j) tr cap' a' ->
    op7_ch M cap a j ((if cap =? 0 then RMalloc c else RRealloc cap c a) :: tr) cap' a'.

Lemma op7_sl_ch M mx : 0 <= mx -> forall f no cap rem j o, 0 <= no -> 0 <= cap -> 2 * (no + rem) <= M ->
  op7_ch M cap o j (fst (sl_run f mx no cap rem j o)) (fst (snd (sl_run f mx no cap rem j o)))
    (snd (snd (sl_run f mx no cap rem j o))).
Proof.
  intros Hmx f. induction f as [|f IH]; intros no cap rem j o Hno Hcap HM; cbn [sl_run]; cbv zeta.
  - apply op7_ch_nil.
  - destruct (rem <=? 0) eqn:Er; [apply op7_ch_nil|]. apply Z.leb_gt in Er.
    set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
    assert (Hn : 0 < n <= rem).
    { unfold n. destruct (Z.eqb_spec mx 0) as [E0|E0]; destruct (Z.ltb_spec mx rem) as [E1|E1];
        cbn [negb andb]; lia. }
    destruct (cap <? no + n) eqn:Ec.
    + apply Z.ltb_lt in Ec. cbn [fst snd]. apply op7_ch_grow; [lia|lia|]. apply IH; lia.
    + apply IH; lia.
Qed.

Lemma op7_T_ch live mx CAP EL o : 0 <= mx -> 0 <= EL -> 0 <= CAP ->
  op7_ch (2 * (EL + 1)) CAP o 1 (relay_event_tr live mx 0 CAP EL 1 o) (op7_capT live mx CAP EL)
    (op7_outT live mx CAP EL o).
Proof.
  intros Hmx HE HC.
  unfold relay_event_tr, send_line_tr, op7_capT, send_line_cap, op7_outT, relay_event_out, send_line_out.
  destruct live; [|apply op7_ch_nil].
  rewrite (op7_sl_cap _ mx 0 CAP (EL + 1) 0 adr0 1 o).
  apply (op7_sl_ch (2 * (EL + 1)) mx Hmx); lia.
Qed.

Definition op7_dz (x c : Z) : Z := if x =? 0 then 0 else one_if c (band x).

Lemma op7_dz_0 c : op7_dz 0 c = 0.
Proof. reflexivity. Qed.

Lemma op7_dz_pos x c : x <> 0 -> op7_dz x c = one_if c (band x).
Proof. intros H. unfold op7_dz. rewrite (proj2 (Z.eqb_neq x 0) H). reflexivity. Qed.

Lemma op7_dz_b x c : 0 <= op7_dz x c <= 1.
Proof. unfold op7_dz. destruct (x =? 0); [lia|apply one_if_b]. Qed.

Lemma op7_dl_eq CAP CAP' c : op7_dl CAP CAP' c = if CAP' =? CAP then 0 else one_if c (band CAP') - op7_dz CAP c.
Proof. reflexivity. Qed.

Lemma op7_malloc_live bc n : p3_live (pb3_malloc bc n) = lv_add (p3_live bc) (band n) 1.
Proof. reflexivity. Qed.

Lemma op7_free_live bc n p : p3_live (pb3_free bc n p) = lv_add (p3_live bc) (band n) (-1).
Proof. reflexivity. Qed.

Lemma op7_free_bytes bc n p : p3_bytes (pb3_free bc n p) = p3_bytes bc - n.
Proof. reflexivity. Qed.

Lemma op7_free_mis bc n p : p3_mis (pb3_free bc n p) = mis_del (p3_mis bc) p.
Proof. reflexivity. Qed.

Lemma op7_mis_del_in M p e : In e (mis_del M p) -> In e M /\ fst e <> p.
Proof.
  unfold mis_del. intros Hd. apply List.filter_In in Hd as [Hm Hn]. split; [exact Hm|].
  intros Ee. cbv beta in Hn. rewrite Ee, sptr_eqb_refl in Hn. cbn in Hn. discriminate.
Qed.

Lemma op7_mis_realloc_in M k n p q e : In e (mis_realloc M k n p q) -> (fst e = q /\ q = p) \/ (In e M /\ fst e <> p).
Proof.
  unfold mis_realloc. intros H.
  match type of H with In _ (if ?b then _ else _) => destruct b eqn:C end.
  - destruct H as [<-|H]; [|right; exact (op7_mis_del_in M p e H)].
    apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C _]. apply sptr_eqb_eq in C.
    left. cbn [fst]. split; [symmetry; exact C|exact C].
  - right. exact (op7_mis_del_in M p e H).
Qed.

Lemma op7_flen_del (M : list (sptr * Z)) p (x : Z) :
  (length (List.filter (fun e => (snd e =? x)%Z) (mis_del M p)) <= length (List.filter (fun e => (snd e =? x)%Z) M))%nat.
Proof.
  unfold mis_del. induction M as [|e M IH]; [cbn; lia|]. cbn [List.filter].
  destruct (sptr_eqb (fst e) p); cbn [negb List.filter]; destruct (snd e =? x); cbn [length]; lia.
Qed.

Lemma op7_flen_del_lt (M : list (sptr * Z)) p (x : Z) e0 : In e0 M -> fst e0 = p -> snd e0 = x ->
  (length (List.filter (fun e => (snd e =? x)%Z) (mis_del M p)) <
   length (List.filter (fun e => (snd e =? x)%Z) M))%nat.
Proof.
  intros Hin H1 H2. induction M as [|e M IH]; [destruct Hin|].
  pose proof (op7_flen_del M p x) as F. unfold mis_del in F, IH |- *. cbn [List.filter].
  destruct Hin as [<-|Hin].
  - rewrite H1, sptr_eqb_refl, H2, Z.eqb_refl. cbn [negb List.filter length]. lia.
  - specialize (IH Hin).
    destruct (sptr_eqb (fst e) p); cbn [negb List.filter]; destruct (snd e =? x); cbn [length]; lia.
Qed.

Lemma op7_cnt_realloc M k n p q x : 0 <= k < n -> count_mis (mis_realloc M k n p q) x <= count_mis M x.
Proof.
  intros Hk. pose proof (op7_band_mono k n ltac:(lia)) as Bm.
  unfold mis_realloc, count_mis.
  match goal with |- context[if ?b then _ else _] => destruct b eqn:C end.
  - apply andb_true_iff in C as [_ C]. rewrite (proj2 (Z.eqb_neq (band n + 1) (band k))) in C by lia.
    cbn [orb] in C.
    destruct (mis_lookup M p) as [v|] eqn:Hl; [|discriminate]. apply Z.eqb_eq in C. subst v.
    unfold mis_lookup in Hl. destruct (List.find (fun e => sptr_eqb (fst e) p) M) as [e0|] eqn:Hf; [|discriminate].
    cbn [option_map] in Hl. injection Hl as He0. apply List.find_some in Hf as [Hin Hp]. cbv beta in Hp.
    apply sptr_eqb_eq in Hp.
    cbn [List.filter snd]. destruct (band n + 1 =? x) eqn:Ex.
    + apply Z.eqb_eq in Ex. pose proof (op7_flen_del_lt M p x e0 Hin Hp ltac:(lia)). cbn [length]. lia.
    + pose proof (op7_flen_del M p x). lia.
  - pose proof (op7_flen_del M p x). lia.
Qed.

Definition op7_I (qs : list sptr) (b1 : pbound3) (CAP : Z) (p0 : sptr) (bc : pbound3) (cap : Z) (a : adrF) : Prop :=
  p3_cap bc = p3_cap b1 /\ p3_mcap bc = p3_mcap b1 /\ length (p3_live bc) = 49%nat /\
  (forall c, 0 <= c -> znth c (p3_live bc) = znth c (p3_live b1) + op7_dz cap c - op7_dz CAP c) /\
  p3_bytes bc = p3_bytes b1 + cap - CAP /\ 0 <= CAP <= cap /\
  (forall c, count_mis (p3_mis bc) c <= count_mis (p3_mis b1) c) /\
  (forall e, In e (p3_mis bc) ->
     (cap <> 0 /\ fst e = resolveF qs a /\ (cap = CAP -> In e (p3_mis b1))) \/
     (In e (p3_mis b1) /\ (CAP = 0 \/ fst e <> p0))).

Lemma op7_I_init qs b1 CAP p0 a : 0 <= CAP -> length (p3_live b1) = 49%nat -> resolveF qs a = p0 ->
  op7_I qs b1 CAP p0 b1 CAP a.
Proof.
  intros HC Hl Ha. unfold op7_I. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hl|].
  split; [intros c _; lia|]. split; [lia|]. split; [lia|]. split; [intros c; lia|].
  intros e He. destruct (Z.eqb_spec CAP 0) as [E|E]; [right; split; [exact He|left; exact E]|].
  destruct (sptr_eqb (fst e) p0) eqn:Ep.
  - left. apply sptr_eqb_eq in Ep. split; [exact E|]. split; [rewrite Ha; exact Ep|]. intros _; exact He.
  - right. split; [exact He|]. right. intros Ee. rewrite Ee, sptr_eqb_refl in Ep. discriminate.
Qed.

Lemma op7_I_malloc qs b1 CAP p0 bc a c j : op7_I qs b1 CAP p0 bc 0 a -> 0 < c ->
  op7_I qs b1 CAP p0 (pb3_malloc bc c) c (Ret j).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hc. pose proof (AllocPackRoom.band_range c ltac:(lia)) as Bc.
  assert (CAP = 0) as -> by lia.
  unfold op7_I, pb3_malloc. cbn [p3_cap p3_mcap p3_live p3_bytes p3_mis].
  split; [exact H1|]. split; [exact H2|]. split; [rewrite AllocPackRoom.lv_add_length; exact H3|].
  split.
  { intros x Hx. rewrite znth_lv_add_d by (first [exact H3 | lia]). rewrite H4 by exact Hx.
    rewrite (op7_dz_pos c x) by lia. rewrite !op7_dz_0. lia. }
  split; [lia|]. split; [lia|]. split; [exact H7|].
  intros e He. destruct (H8 e He) as [(E & _)|R]; [exfalso; lia|right; exact R].
Qed.

Lemma op7_I_realloc qs b1 CAP p0 bc cap a c j : op7_I qs b1 CAP p0 bc cap a -> 0 < cap < c ->
  op7_I qs b1 CAP p0 (pb3_realloc bc cap c (resolveF qs a) (nth j qs (SP 0 0))) c (Ret j).
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hc.
  pose proof (AllocPackRoom.band_range c ltac:(lia)) as Bc. pose proof (AllocPackRoom.band_range cap ltac:(lia)) as Bk.
  unfold op7_I, pb3_realloc. cbn [p3_cap p3_mcap p3_live p3_bytes p3_mis].
  split; [exact H1|]. split; [exact H2|]. split; [rewrite !AllocPackRoom.lv_add_length; exact H3|].
  split.
  { intros x Hx. rewrite znth_lv_add_d by (first [rewrite AllocPackRoom.lv_add_length; exact H3 | lia]).
    rewrite znth_lv_add_d by (first [exact H3 | lia]). rewrite H4 by exact Hx.
    rewrite (op7_dz_pos c x), (op7_dz_pos cap x) by lia. lia. }
  split; [lia|]. split; [lia|].
  split.
  { intros x. pose proof (op7_cnt_realloc (p3_mis bc) cap c (resolveF qs a) (nth j qs (SP 0 0)) x ltac:(lia)).
    specialize (H7 x). lia. }
  intros e He. apply op7_mis_realloc_in in He as [(Ef & Eq)|(Hm & Hn)].
  - left. split; [lia|]. split; [exact Ef|]. intros E. exfalso. lia.
  - destruct (H8 e Hm) as [(_ & Ef & _)|R]; [contradiction|right; exact R].
Qed.

Lemma op7_ch_run qs b1 CAP p0 M : forall cap a j tr cap' a', op7_ch M cap a j tr cap' a' ->
  forall bc, op7_I qs b1 CAP p0 bc cap a ->
  op7_I qs b1 CAP p0 (run_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc qs bc j tr) cap' a'.
Proof.
  intros cap a j tr cap' a' H. induction H as [cap a j|cap a j c tr cap' a' Hc HM Hch IH]; intros bc HI; [exact HI|].
  destruct (Z.eqb_spec cap 0) as [E|E].
  - subst cap. cbn [run_from]. apply IH. apply (op7_I_malloc qs b1 CAP p0 bc a c j HI). lia.
  - cbn [run_from]. apply IH. apply op7_I_realloc; [exact HI|lia].
Qed.

Lemma op7_ch_room qs b1 CAP p0 M (R : pbound3 -> Z -> Prop)
  (HR : forall bc cap a c, op7_I qs b1 CAP p0 bc cap a -> 0 <= cap < c -> c <= M -> R bc c) :
  forall cap a j tr cap' a', op7_ch M cap a j tr cap' a' ->
  forall bc, op7_I qs b1 CAP p0 bc cap a ->
  room_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc R qs bc j tr.
Proof.
  intros cap a j tr cap' a' H. induction H as [cap a j|cap a j c tr cap' a' Hc HM Hch IH]; intros bc HI; [exact I|].
  destruct (Z.eqb_spec cap 0) as [E|E].
  - subst cap. cbn [room_from]. split; [exact (HR bc 0 a c HI Hc HM)|].
    apply IH. apply (op7_I_malloc qs b1 CAP p0 bc a c j HI). lia.
  - cbn [room_from]. split; [exact (HR bc cap a c HI Hc HM)|].
    apply IH. apply op7_I_realloc; [exact HI|lia].
Qed.

Lemma op7_slack NW pl k V L A b al alb c : RI3_ledger NW pl k V L A b al alb -> 0 <= c < 49 ->
  znth c (p3_live b) + 3 <= znth c (p3_cap b).
Proof.
  intros (HC & _ & HN & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) Hc. destruct (H c Hc) as (H1 & H2 & H3).
  pose proof (cons_le pl k c). pose proof (prom_c_nonneg (rv_pend V) c). pose proof (nc_cnt_bounds V L A c).
  pose proof (ek_c_nonneg V c).
  assert (Z.of_nat (length (rv_nc V)) <= 26) by (unfold NC_MAX in HN; lia).
  rewrite HC, CS_reply_at by exact Hc.
  unfold cs_band. destruct (Z.eqb_spec c 0) as [E|E]; cbv beta iota.
  - subst c. pose proof (SlotParse.x0_bound pl). unfold CAPS0, RI_BASE, SlotParse.BTEXT in *. lia.
  - unfold CBASE, RI_BASE in *. lia.
Qed.

Lemma op7_room_at NW pl K V L A b al alb EL qs CAP p0 bc cap a c :
  RI3_ledger NW pl K V L A b al alb -> 0 <= EL -> 2 * (EL + 1) <= NMAX -> CAP <= NMAX ->
  op7_I qs (pb3_malloc b (EL + 1)) CAP p0 bc cap a -> 0 <= cap < c -> c <= NMAX -> room_pack3 bc c.
Proof.
  intros HL HE HN HC (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _) Hc HcM.
  pose proof HL as (HCs & HMc & _ & HlL & _).
  pose proof (AllocPackRoom.band_range c ltac:(lia)) as Bc.
  pose proof (AllocPackRoom.band_range (EL + 1) ltac:(lia)) as Be.
  unfold pb3_malloc in H1, H2, H4, H5, H7. cbn [p3_cap p3_mcap p3_live p3_bytes p3_mis] in H1, H2, H4, H5, H7.
  apply (room_pack3_of bc c BMAX NMAX).
  - rewrite H1, H2, HCs, HMc. apply CS_reply_capok3.
  - lia.
  - pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL).
    assert (X : PB3_MAX + 3 * NMAX <= BMAX) by (apply Z.leb_le; vm_compute; reflexivity). lia.
  - rewrite H4 by lia. rewrite H1. rewrite znth_lv_add_d by (first [exact HlL | lia]).
    pose proof (op7_slack _ _ _ _ _ _ _ _ _ (band c) HL Bc).
    pose proof (one_if_b (band c) (band (EL + 1))). pose proof (op7_dz_b cap (band c)).
    pose proof (op7_dz_b CAP (band c)). lia.
  - intros Hb. rewrite H2. pose proof (H7 (band c + 1)).
    pose proof (ledger3_mis _ _ _ _ _ _ _ _ _ (band c + 1) HL ltac:(lia)). lia.
Qed.

Lemma op7_run_eq qs b EL live mx CAP o :
  runF pack3_form qs b (op7_trT EL live mx CAP o) =
  pb3_free (run_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc qs (pb3_malloc b (EL + 1)) 1
    (relay_event_tr live mx 0 CAP EL 1 o)) (EL + 1) (nth 0 qs (SP 0 0)).
Proof.
  change (runF pack3_form qs b (op7_trT EL live mx CAP o)) with
    (run_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc qs b 0 (op7_trT EL live mx CAP o)).
  unfold op7_trT. cbn [run_from]. rewrite run_from_app. reflexivity.
Qed.

Lemma op7_entry NW pl K V L A b al alb V' L' OUT live qs a' CAP CAP' e :
  RI3_ledger NW pl K V L A b al alb -> res_ok_pack3 A b -> 0 <= CAP ->
  List.NoDup (map fst (blocks L A)) ->
  (0 < CAP -> In (OUT, CAP) (blocks L A)) -> (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
  (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> OUT \/ live = false -> ptr_addr L' p = ptr_addr L p) ->
  (forall a m, In a (rv_nc V) -> In (a, m) (blocks L A) -> a <> OUT \/ live = false -> In a (rv_nc V')) ->
  (live = true -> In (ptr_addr L' (resolveF qs a')) (rv_nc V')) ->
  (live = false -> CAP' = CAP) ->
  (CAP' <> 0 /\ fst e = resolveF qs a' /\ (CAP' = CAP -> In e (p3_mis b))) \/
    (In e (p3_mis b) /\ (CAP = 0 \/ fst e <> sptr_of L A OUT)) ->
  In (ptr_addr L' (fst e)) (rv_nc V').
Proof.
  intros HL HA HC HB Hin Hout Hpa Hv Hlast HcF He.
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  assert (Gen : In e (p3_mis b) -> ptr_addr L (fst e) <> OUT \/ live = false -> In (ptr_addr L' (fst e)) (rv_nc V')).
  { intros Hm Hne. destruct (HU e Hm) as (_ & n & Hn).
    pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HI & _) & _).
    assert (Ha : In (ptr_addr L (fst e)) (rv_nc V)).
    { apply HI. exact (in_map (fun e0 => ptr_addr L (fst e0)) _ e Hm). }
    rewrite (Hpa (fst e) n Hn Hne). apply (Hv _ n Ha); [|exact Hne].
    exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ (fst e, n) Hn). }
  destruct live.
  - destruct He as [(_ & Hf & _)|(Hm & Hor)].
    + rewrite Hf. apply Hlast. reflexivity.
    + destruct (HU e Hm) as (_ & n & Hn).
      apply Gen; [exact Hm|left]. intros Ea.
      assert (Hbl : In (OUT, n) (blocks L A)).
      { rewrite <- Ea. exact (in_map (fun b0 => (ptr_addr L (fst b0), snd b0)) _ (fst e, n) Hn). }
      destruct (Z.eqb_spec CAP 0) as [E0|E0]; [exact (Hout E0 n Hbl)|].
      destruct Hor as [E1|Hne]; [lia|].
      pose proof (Hin ltac:(lia)) as Hb0.
      destruct (sptr_of_spec L A OUT CAP (proj2 (stdpp.base.NoDup_ListNoDup _) HB) Hb0) as (Hp0 & Ep0).
      apply Hne.
      assert (Eq : (fst e, n) = (sptr_of L A OUT, CAP)).
      { apply (nodup_map_eq (fun b0 => ptr_addr L (fst b0)) (user_blocks A)); [|exact Hn|exact Hp0|].
        - unfold blocks in HB. rewrite map_map in HB. exact HB.
        - cbn [fst]. rewrite Ea, Ep0. reflexivity. }
      injection Eq as E2 _. exact E2.
  - apply Gen; [|right; reflexivity].
    destruct He as [(_ & _ & Hm)|(Hm & _)]; [exact (Hm (HcF eq_refl))|exact Hm].
Qed.

Lemma op7_shift_tr live mx NO CAP EL s o :
  shift_tr sptr s (relay_event_tr live mx NO CAP EL 0 o) = relay_event_tr live mx NO CAP EL s (shift_addr sptr s o).
Proof.
  unfold relay_event_tr, send_line_tr. destruct live; [|reflexivity].
  pose proof (op7_sl_shift (Z.to_nat (EL + 1)) mx NO CAP (EL + 1) 0 s o) as E.
  rewrite Nat.add_0_r in E. rewrite E. reflexivity.
Qed.

Lemma op7_shift_out live mx NO CAP EL s o :
  shift_addr sptr s (relay_event_out live mx NO CAP EL 0 o) = relay_event_out live mx NO CAP EL s (shift_addr sptr s o).
Proof.
  unfold relay_event_out, send_line_out. destruct live; [|reflexivity].
  pose proof (op7_sl_shift (Z.to_nat (EL + 1)) mx NO CAP (EL + 1) 0 s o) as E.
  rewrite Nat.add_0_r in E. rewrite E. reflexivity.
Qed.

Theorem op7_room3 NW pl K V L A b al alb EL live mx CAP o :
  RI3_ledger NW pl K V L A b al alb -> 0 <= EL -> 2 * (EL + 1) <= NMAX -> 0 <= mx -> 0 <= CAP <= NMAX ->
  forall qs, length qs = nretF (op7_trT EL live mx CAP o) -> roomF pack3_form qs b (op7_trT EL live mx CAP o).
Proof.
  intros HL HE HN Hmx HC qs _. pose proof HL as (_ & _ & _ & HlL & _).
  change (roomF pack3_form qs b (op7_trT EL live mx CAP o)) with
    (room_from pbound3 sptr (SP 0 0) pb3_malloc pb3_free pb3_realloc room_pack3 qs b 0 (op7_trT EL live mx CAP o)).
  unfold op7_trT. cbn [room_from]. split; [apply (room3_ledger _ _ _ _ _ _ _ _ _ _ HL); lia|].
  apply room_from_app. split.
  - assert (HR : forall bc cap a c, op7_I qs (pb3_malloc b (EL + 1)) CAP (resolveF qs o) bc cap a -> 0 <= cap < c ->
        c <= 2 * (EL + 1) -> room_pack3 bc c).
    { intros bc cap a c HI Hc HM.
      apply (op7_room_at NW pl K V L A b al alb EL qs CAP (resolveF qs o) bc cap a c);
        [exact HL|lia|lia|lia|exact HI|lia|lia]. }
    apply (op7_ch_room qs (pb3_malloc b (EL + 1)) CAP (resolveF qs o) (2 * (EL + 1)) room_pack3 HR
      CAP o 1 _ _ _ (op7_T_ch live mx CAP EL o Hmx HE ltac:(lia))).
    apply op7_I_init; [lia| |reflexivity].
    rewrite op7_malloc_live, AllocPackRoom.lv_add_length. exact HlL.
  - cbn [room_from]. exact I.
Qed.

Theorem op7_ledger3 NW pl K K' V L A b al alb EL live mx CAP OUT qs V' L' A' :
  RI3_ledger NW pl K V L A b al alb -> res_ok_pack3 A b ->
  0 <= EL -> 2 * (EL + 1) <= NMAX -> 0 <= mx -> 0 <= CAP <= NMAX ->
  length qs = nretF (op7_trT EL live mx CAP (known_at L A OUT)) ->
  res_ok_pack3 A' (runF pack3_form qs b (op7_trT EL live mx CAP (known_at L A OUT))) ->
  nc_step NW pl K' V L A V' L' A' al alb (op7_dl CAP (op7_capT live mx CAP EL)) (op7_capT live mx CAP EL - CAP) ->
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (0 < CAP -> In (OUT, CAP) (blocks L A)) -> (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
  (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> OUT \/ live = false -> ptr_addr L' p = ptr_addr L p) ->
  (forall a m, In a (rv_nc V) -> In (a, m) (blocks L A) -> a <> OUT \/ live = false -> In a (rv_nc V')) ->
  (live = true -> In (ptr_addr L' (resolveF qs (op7_outT live mx CAP EL (known_at L A OUT)))) (rv_nc V')) ->
  RI3_ledger NW pl K' V' L' A' (runF pack3_form qs b (op7_trT EL live mx CAP (known_at L A OUT))) al alb.
Proof.
  intros HL HA HE HN Hmx HC Hq HA' HS HB HB' Hin Hout Hpa Hv Hlast.
  pose proof HL as (HCs & HMc & _ & HlL & _).
  assert (HcF : live = false -> op7_capT live mx CAP EL = CAP) by (intros ->; reflexivity).
  pose proof (op7_T_ch live mx CAP EL (known_at L A OUT) Hmx HE ltac:(lia)) as Hch.
  assert (HI0 : op7_I qs (pb3_malloc b (EL + 1)) CAP (sptr_of L A OUT) (pb3_malloc b (EL + 1)) CAP
      (known_at L A OUT)).
  { apply op7_I_init; [lia| |reflexivity]. rewrite op7_malloc_live, AllocPackRoom.lv_add_length. exact HlL. }
  pose proof (op7_ch_run _ _ _ _ _ _ _ _ _ _ _ Hch _ HI0) as HIT.
  rewrite (op7_run_eq qs b EL live mx CAP (known_at L A OUT)) in HA' |- *.
  destruct HIT as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  pose proof (AllocPackRoom.band_range (EL + 1) ltac:(lia)) as Be.
  apply (ledger3_nc NW pl K V L A b al alb K' V' L' A' _ (op7_dl CAP (op7_capT live mx CAP EL))
    (op7_capT live mx CAP EL - CAP) HL HS).
  - exact H1.
  - exact H2.
  - rewrite op7_free_live, AllocPackRoom.lv_add_length. exact H3.
  - intros c Hc. rewrite op7_free_live. rewrite znth_lv_add_d by (first [exact H3 | lia]). rewrite H4 by lia.
    rewrite op7_malloc_live. rewrite znth_lv_add_d by (first [exact HlL | lia]).
    rewrite op7_dl_eq. destruct (Z.eqb_spec (op7_capT live mx CAP EL) CAP) as [E|E]; cbv iota.
    + rewrite E. lia.
    + rewrite (op7_dz_pos (op7_capT live mx CAP EL) c) by lia. lia.
  - rewrite op7_free_bytes, H5. change (p3_bytes (pb3_malloc b (EL + 1))) with (p3_bytes b + (EL + 1)). lia.
  - split.
    + intros x Hx. unfold mis_addrs in Hx. apply in_map_iff in Hx as (e & <- & He). cbv beta.
      rewrite op7_free_mis in He. apply op7_mis_del_in in He as [He _].
      apply (op7_entry NW pl K V L A b al alb V' L' OUT live qs (op7_outT live mx CAP EL (known_at L A OUT)) CAP
        (op7_capT live mx CAP EL) e HL HA ltac:(lia) HB Hin Hout Hpa Hv Hlast HcF).
      exact (H8 e He).
    + destruct HA' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HMIS & _). exact (mis_nodup L' A' _ _ HB' HMIS).
Qed.

Lemma op7_nc_step NW pl K K' V L A b al alb V' L' A' dl db :
  RI3_ledger NW pl K V L A b al alb -> K <= K' ->
  (length (rv_nc V') <= NC_MAX)%nat ->
  (forall c, 0 <= c < 49 -> nc_cnt V L A c + dl c <= nc_cnt V' L' A' c) ->
  ncs V L A + db <= ncs V' L' A' -> ncs V' L' A' <= NW V' -> NW V' <= NW V -> rv_pend V' = rv_pend V ->
  rv_ek V' = rv_ek V ->
  nc_step NW pl K' V L A V' L' A' al alb dl db.
Proof.
  intros (HC & HM & HN & HlL & HL & Ha & HE & HB & HW1 & HW2 & HP & HMis & H) Hk HN' HC' HB' HW1' HW' HP' HEK.
  pose proof (cdat_mono pl K K' Hk). pose proof (consb_mono pl K K' Hk).
  assert (EB : ek_b V' = ek_b V) by (unfold ek_b; rewrite HEK; reflexivity).
  assert (EC : forall c, ek_c V' c = ek_c V c) by (intros c; unfold ek_c; rewrite HEK; reflexivity).
  unfold nc_step. rewrite HP', EB, HEK.
  split; [exact HN'|]. split; [exact HC'|]. split; [exact HB'|]. split; [exact HW1'|].
  split; [unfold DATA_PER in *; lia|].
  split; [|split; [lia|exact HE]].
  intros c Hc. rewrite EC. destruct (H c Hc) as (_ & _ & H3). pose proof (cons_mono pl K K' c Hk). lia.
Qed.

Theorem op7_res3 E K K' V L A EL live mx CAP OUT :
  RI3_reply E K V L A -> K <= K' ->
  0 <= EL -> 2 * (EL + 1) <= NMAX -> 0 <= mx -> 0 <= CAP <= NMAX ->
  List.NoDup (map fst (blocks L A)) ->
  (0 < CAP -> In (OUT, CAP) (blocks L A)) -> (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
  exists bnd, res_ok_pack3 A bnd /\
    (forall qs, length qs = nretF (op7_trT EL live mx CAP (known_at L A OUT)) ->
       roomF pack3_form qs bnd (op7_trT EL live mx CAP (known_at L A OUT))) /\
    forall L' A' qs, length qs = nretF (op7_trT EL live mx CAP (known_at L A OUT)) ->
      res_ok_pack3 A' (runF pack3_form qs bnd (op7_trT EL live mx CAP (known_at L A OUT))) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c + op7_dl CAP (op7_capT live mx CAP EL) c <= nc_cnt V' L' A' c) ->
        ncs V L A + (op7_capT live mx CAP EL - CAP) <= ncs V' L' A' -> ncs V' L' A' <= rv_wt V' -> rv_wt V' <= rv_wt V ->
        rv_pend V' = rv_pend V -> rv_ek V' = rv_ek V -> List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> OUT \/ live = false -> ptr_addr L' p = ptr_addr L p) ->
        (forall a m, In a (rv_nc V) -> In (a, m) (blocks L A) -> a <> OUT \/ live = false -> In a (rv_nc V')) ->
        (live = true -> In (ptr_addr L' (resolveF qs (op7_outT live mx CAP EL (known_at L A OUT)))) (rv_nc V')) ->
        RI3_reply E K' V' L' A'.
Proof.
  intros (b & al & alb & HR & HL) Hk HEL HN Hmx HCAP HND HO HO0.
  exists b. split; [exact HR|]. split.
  - intros qs Hq.
    exact (op7_room3 rv_wt (ss_pl E) K V L A b al alb EL live mx CAP (known_at L A OUT) HL HEL HN Hmx HCAP qs Hq).
  - intros L' A' qs Hq HR' V' HN' HC' HB' HW1' HW' HP' HEK HND' HK HV HLast.
    exists (runF pack3_form qs b (op7_trT EL live mx CAP (known_at L A OUT))), al, alb. split; [exact HR'|].
    apply (op7_ledger3 rv_wt (ss_pl E) K K' V L A b al alb EL live mx CAP OUT qs V' L' A'); try assumption.
    apply (op7_nc_step rv_wt (ss_pl E) K K' V L A b al alb V' L' A'); assumption.
Qed.
