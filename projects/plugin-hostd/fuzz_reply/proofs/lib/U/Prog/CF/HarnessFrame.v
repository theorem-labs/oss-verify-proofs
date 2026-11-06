From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayModel HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import list_find_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma hf_in_elem : forall {X} (x : X) l, In x l -> list_elem_of x l.
Proof.
  intros X x l. induction l as [|y l IH]; intros H; [destruct H|].
  destruct H as [<-|H]; [apply list_elem_of_here | apply list_elem_of_further; exact (IH H)].
Qed.

Lemma hf_elem_in : forall {X} (x : X) l, list_elem_of x l -> In x l.
Proof. intros X x l H. induction H as [y l|y z l H IH]; [left; reflexivity | right; exact IH]. Qed.

Lemma hf_nodup : forall {X} (l : list X), NoDup l <-> List.NoDup l.
Proof.
  intros X l. induction l as [|x l IH]; split; intros H.
  - constructor.
  - constructor.
  - inversion H as [|y l' Hn Hl]; subst. constructor; [intros Hi; apply Hn; exact (hf_in_elem _ _ Hi) | apply IH; exact Hl].
  - inversion H as [|y l' Hn Hl]; subst. constructor; [intros Hi; apply Hn; exact (hf_elem_in _ _ Hi) | apply IH; exact Hl].
Qed.

Lemma hf_nodup_app : forall {X} (l1 l2 : list X), List.NoDup l1 -> List.NoDup l2 ->
  (forall a, In a l1 -> ~ In a l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros X l1. induction l1 as [|x l1 IH]; intros l2 H1 H2 D; [exact H2|].
  inversion H1 as [|y l Hn Hl]; subst. cbn [app]. constructor.
  - intros Hi. apply in_app_iff in Hi as [Hi|Hi]; [exact (Hn Hi) | exact (D x (or_introl eq_refl) Hi)].
  - apply IH; [exact Hl | exact H2 | intros a Ha; exact (D a (or_intror Ha))].
Qed.

Lemma hf_nodup_l : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  intros X l1. induction l1 as [|x l1 IH]; intros l2 ND; [constructor|].
  inversion ND as [|y l Hn Hl]; subst.
  constructor; [intros H; apply Hn; apply in_or_app; left; exact H | exact (IH l2 Hl)].
Qed.

Lemma hf_nodup_disj : forall {X} (l1 l2 : list X) a, List.NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
  intros X l1. induction l1 as [|x l1 IH]; intros l2 a ND H1 H2; [destruct H1|].
  inversion ND as [|y l Hn Hl]; subst. destruct H1 as [<-|H1].
  - apply Hn. apply in_or_app. right. exact H2.
  - exact (IH l2 a Hl H1 H2).
Qed.

Lemma hf_nodup_drop : forall {X} (l : list X) i, List.NoDup l -> List.NoDup (firstn i l ++ skipn (S i) l).
Proof.
  intros X l i ND. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
  - destruct (nth_error l i) as [x|] eqn:Hx; [|apply nth_error_None in Hx; lia].
    destruct (nth_error_split l i Hx) as (l1 & l2 & E & Hl1). subst l i.
    rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
    rewrite skipn_app, (skipn_all2 l1) by lia. cbn [app].
    replace (S (length l1) - length l1)%nat with 1%nat by lia. cbn [skipn].
    apply (NoDup_remove_1 l1 l2 x). exact ND.
  - rewrite firstn_all2, skipn_all2 by lia. rewrite app_nil_r. exact ND.
Qed.

Lemma hf_ro_glob : forall a, 0x318a0 <= a < 0x31aa0 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha.
  assert (C : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x318a0 + Z.of_nat i)))) (seq 0 512) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat (a - 0x318a0))).
  rewrite Z2Nat.id in C by lia. replace (0x318a0 + (a - 0x318a0)) with a in C by lia.
  apply negb_true_iff. apply C. apply in_seq. lia.
Qed.

Definition wrecs (l : hlist) : list (word * list byte) := map (fun r => (Z_to_bv 64 (fst r), snd r)) (hl_recs l).

Lemma hf_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app, !length_le8. reflexivity. Qed.

Lemma hf_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, hf_text_rec_len, IH.
  cbn [length]. lia.
Qed.

Lemma hf_rec_bytes : forall sg m V rs junk j r, bytes_at sg m V (concat (map text_rec rs) ++ junk) ->
  nth_error rs j = Some r -> bytes_at sg m (V + 16 * Z.of_nat j) (text_rec r).
Proof.
  intros sg m V rs junk j r H Hj.
  destruct (nth_error_split rs j Hj) as (l1 & l2 & -> & <-).
  rewrite map_app, concat_app in H. cbn [map concat] in H.
  apply bytes_at_app in H. destruct H as [H _].
  apply bytes_at_app in H. destruct H as [_ H].
  apply bytes_at_app in H. destruct H as [H _].
  rewrite hf_concat_len in H. replace (V + Z.of_nat (16 * length l1)) with (V + 16 * Z.of_nat (length l1)) in H by lia.
  exact H.
Qed.

Lemma hf_texts_drop : forall (rs : list (Z * list byte)) i,
  map (fun r => bzs (snd r)) (firstn i rs ++ skipn (S i) rs) =
  firstn i (map (fun r => bzs (snd r)) rs) ++ skipn (S i) (map (fun r => bzs (snd r)) rs).
Proof. intros rs i. rewrite map_app, firstn_map, skipn_map. reflexivity. Qed.

Lemma src_out : forall h, NoDup (hs_blocks h) ->
  forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
  ~ In q (list_blocks (hs_held h)).
Proof.
  intros h ND q Hq Hh. apply hf_nodup in ND. unfold hs_blocks in ND.
  apply (hf_nodup_disj (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h))
           (list_blocks (hs_held h)) q); [rewrite <- !app_assoc; exact ND | exact Hq | exact Hh].
Qed.

Lemma hf_in_drop : forall {X} (l : list X) i x, In x (firstn i l ++ skipn (S i) l) -> In x l.
Proof.
  intros X l i x H. apply in_app_iff in H as [H|H].
  - rewrite <- (firstn_skipn i l). apply in_or_app. left. exact H.
  - rewrite <- (firstn_skipn (S i) l). apply in_or_app. right. exact H.
Qed.

Lemma hf_in_keep : forall {X} (l : list X) i x d, (i < length l)%nat -> In x l -> x <> nth i l d ->
  In x (firstn i l ++ skipn (S i) l).
Proof.
  intros X l i x d Hi H N. destruct (nth_error l i) as [y|] eqn:Hy; [|apply nth_error_None in Hy; lia].
  destruct (nth_error_split l i Hy) as (l1 & l2 & E & Hl1). subst l i.
  rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all.
  rewrite skipn_app, (skipn_all2 l1) by lia. cbn [app].
  replace (S (length l1) - length l1)%nat with 1%nat by lia. cbn [skipn].
  rewrite app_nth2, Nat.sub_diag in N by lia. cbn [nth] in N.
  apply in_app_iff in H as [H|[H|H]];
    [apply in_or_app; left; exact H | exfalso; exact (N (eq_sym H)) | apply in_or_app; right; exact H].
Qed.

Lemma hf_lb_drop : forall (l l' : hlist) i q, hl_v l' = hl_v l -> hl_cap l' = hl_cap l ->
  hl_recs l' = firstn i (hl_recs l) ++ skipn (S i) (hl_recs l) -> In q (list_blocks l') -> In q (list_blocks l).
Proof.
  intros l l' i q EV EC ER H. unfold list_blocks in *. rewrite EV, EC, ER in H.
  apply in_app_iff in H as [H|H]; apply in_or_app; [left; exact H | right].
  apply in_map_iff in H as (r & <- & Hr). apply in_map. exact (hf_in_drop _ _ _ Hr).
Qed.

Section HF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis BW : blocks_writable Bm API.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition src_base (L : layout) (A : astate) (mem : word -> option byte) (HA : Z) (h : hsrc) : Prop :=
  rw_cells segs mem HA [C4 (Z_to_bv 64 (hs_fd h)); C4 (Z_to_bv 64 (hs_open h));
                        C4 (Z_to_bv 64 (hs_closed h)); C4 (Z_to_bv 64 (hs_eintr h))] /\
  (hs_closed h = 0 \/ hs_closed h = 1) /\ (hs_eintr h = 0 \/ hs_eintr h = 1) /\
  hs_open h = 1 /\ 0 <= hs_fd h < 2 ^ 31 /\
  list_at Bm L A mem (HA + 16) (hs_pending h) false /\
  rw_cells segs mem (HA + 32) [C8 (Z_to_bv 64 (hs_off h)); C8 (Z_to_bv 64 (hs_partial h));
                               C8 (Z_to_bv 64 (hs_npartial h)); C4 (Z_to_bv 64 (hs_overlong h))] /\
  ((hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
   (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) /\
  0 <= hs_npartial h <= 6000 /\ (hs_overlong h = 0 \/ hs_overlong h = 1) /\
  In (hs_partial h, 6000) (blocks L A) /\ fresh_block Bm (hs_partial h) 6000 /\
  Z.of_nat (length (hs_pjunk h)) = 6000 /\
  rw_cells segs mem (hs_partial h) [CB (Z.to_nat 6000) (hs_pjunk h)] /\
  ~ In (Z_to_bv 8 0) (hs_W h).

Lemma src_at_iff : forall L A mem HA h,
  src_at Bm L A mem HA h <->
  src_base L A mem HA h /\ list_at Bm L A mem (HA + 64) (hs_expected h) true /\
  list_at Bm L A mem (HA + 80) (hs_held h) true /\ NoDup (hs_blocks h).
Proof. intros L A mem HA h. unfold src_at, src_base. tauto. Qed.

Definition kept_block (E F : Z -> Prop) (L : layout) (A : astate) (q : Z) : Prop :=
  ~ F q /\ forall k i, In (q, k) (blocks L A) -> 0 <= i < k -> ~ E (q + i).

Lemma list_blocks_nodup : forall L A mem LA l lines, list_at Bm L A mem LA l lines -> List.NoDup (list_blocks l).
Proof.
  intros L A mem LA l lines (_ & _ & _ & ND1 & ND2 & _). unfold list_blocks.
  apply hf_nodup in ND1.
  destruct (hl_cap l =? 0); cbn [app]; [exact ND1|]. constructor; [exact ND2 | exact ND1].
Qed.

Lemma list_at_rmid : forall K sp E F L A mem md L' A' mem' md' LA l lines,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp - K -> MR L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  list_at Bm L A mem LA l lines ->
  (forall i, 0 <= i < 16 -> img_plain Bm (LA + i) /\ ~ E (LA + i)) ->
  (forall q, In q (list_blocks l) -> kept_block E F L A q) ->
  list_at Bm L' A' mem' LA l lines.
Proof.
  intros K sp E F L A mem md L' A' mem' md' LA l lines SEG HK HM R (C & B1 & AR & ND1 & ND2 & FA) HL HB.
  split.
  { apply (rmid_rw_img Bm API AX K sp E F L A mem md L' A' mem' md' LA _ (hg_img_low Bm SEG) HK HM R C).
    intros j Hj. cbn in Hj. apply HL. lia. }
  split; [exact B1|].
  split.
  { destruct AR as [AR|(Hc & Hin & Hfr & Hj & Hcells)]; [left; exact AR|right].
    assert (Hv : In (hl_v l) (list_blocks l)).
    { unfold list_blocks. rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) ltac:(lia)). left. reflexivity. }
    destruct (HB _ Hv) as (NF & NE).
    split; [exact Hc|].
    split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R Hin ltac:(lia) NF
                           ltac:(lia) (NE _ 0 Hin ltac:(lia))))|].
    split; [exact Hfr|]. split; [exact Hj|].
    eapply (rmid_rw_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R Hin ltac:(lia) NF Hcells);
      [lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia |].
    intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia.
    apply (NE _ i Hin). lia. }
  split; [exact ND1|]. split; [exact ND2|].
  rewrite Forall_forall in FA |- *. intros r Hr. destruct (FA r Hr) as (Hin & Hfr & Hc & H1 & H2).
  assert (Hq : In (fst r) (list_blocks l)) by (unfold list_blocks; apply in_or_app; right; apply in_map; exact Hr).
  destruct (HB _ Hq) as (NF & NE).
  split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R Hin ltac:(lia) NF
                         ltac:(lia) (NE _ 0 Hin ltac:(lia))))|].
  split; [exact Hfr|].
  split; [|split; [exact H1 | exact H2]].
  eapply (rmid_rw_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R Hin ltac:(lia) NF Hc);
    [lia | cbn [cells_size csize]; lia |].
  intros i Hi. cbn [cells_size csize] in Hi. apply (NE _ i Hin). lia.
Qed.

Lemma src_base_rmid : forall K sp E F L A mem md L' A' mem' md' HA h,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp - K -> MR L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  src_base L A mem HA h ->
  (forall i, 0 <= i < 64 -> img_plain Bm (HA + i) /\ ~ E (HA + i)) ->
  (forall q, In q (list_blocks (hs_pending h)) \/ q = hs_partial h -> kept_block E F L A q) ->
  src_base L' A' mem' HA h.
Proof.
  intros K sp E F L A mem md L' A' mem' md' HA h SEG HK HM R
    (C1 & H1 & H2 & H3 & H4 & PL & C2 & H5 & H6 & H7 & PIn & PFr & PJ & PC & PW) HL HB.
  assert (T : forall a cs, rw_cells segs mem a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 64 ->
                rw_cells segs mem' a cs).
  { intros a cs H Ha Hb. apply (rmid_rw_img Bm API AX K sp E F L A mem md L' A' mem' md' a _ (hg_img_low Bm SEG)
      HK HM R H). intros j Hj. replace (a + j) with (HA + (a - HA + j)) by lia. apply HL. lia. }
  destruct (HB (hs_partial h) (or_intror eq_refl)) as (NF & NE).
  split; [apply T; [exact C1 | lia | cbn; lia]|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split.
  { apply (list_at_rmid K sp E F L A mem md L' A' mem' md' _ _ _ SEG HK HM R PL).
    - intros i Hi. replace (HA + 16 + i) with (HA + (16 + i)) by lia. apply HL. lia.
    - intros q Hq. apply HB. left. exact Hq. }
  split; [apply T; [exact C2 | lia | cbn; lia]|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
  split; [exact (proj1 (rmid_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ 0 R PIn ltac:(lia) NF
                         ltac:(lia) (NE _ 0 PIn ltac:(lia))))|].
  split; [exact PFr|]. split; [exact PJ|].
  split; [|exact PW].
  eapply (rmid_rw_block Bm API BW K sp E F L A mem md L' A' mem' md' _ _ _ _ R PIn ltac:(lia) NF PC);
    [lia | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia |].
  intros i Hi. cbn [cells_size csize] in Hi. rewrite Nat.add_0_r, Z2Nat.id in Hi by lia.
  apply (NE _ i PIn). lia.
Qed.

Lemma hf_blk_img : forall L A mem md q k i, MR L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img Bm (q + i).
Proof.
  intros L A mem md q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as <- <-. exact (ax_blocks_img AX L A mem md p k' i HM Hp Hi).
Qed.

Lemma hf_blk_align : forall L A mem md q k, MR L A mem md -> In (q, k) (blocks L A) -> q mod 16 = 0.
Proof.
  intros L A mem md q k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as <- <-. exact (mr_blocks_aligned _ _ (aa_laws API) L A mem md p k' HM Hp).
Qed.

Lemma hf_kept : forall L A mem md (E F : Z -> Prop) X Y C V q, MR L A mem md ->
  (forall a, X <= a < Y -> in_img Bm a) ->
  (forall a, E a -> (X <= a < Y) \/ (0 < C /\ V <= a < V + 16 * C)) ->
  (0 < C -> In (V, 16 * C) (blocks L A)) ->
  ~ F q -> (0 < C -> q <> V) -> kept_block E F L A q.
Proof.
  intros L A mem md E F X Y C V q HM HX HE HV NF NV. split; [exact NF|].
  intros k i Hin Hi X0. destruct (HE _ X0) as [D|(HC & D)].
  - exact (hf_blk_img L A mem md q k i HM Hin Hi (HX _ D)).
  - destruct (blocks_disjoint Bm API L A mem md V (16 * C) q k HM (HV HC) Hin (fun e => NV HC (eq_sym e))); lia.
Qed.

Lemma hf_img_notE : forall (E : Z -> Prop) X Y C V a L A mem md, MR L A mem md ->
  (forall a, E a -> (X <= a < Y) \/ (0 < C /\ V <= a < V + 16 * C)) ->
  (0 < C -> In (V, 16 * C) (blocks L A)) ->
  in_img Bm a -> ~ (X <= a < Y) -> ~ E a.
Proof.
  intros E X Y C V a L A mem md HM HE HV Ha HN X0. destruct (HE _ X0) as [D|(HC & D)]; [exact (HN D)|].
  apply (hf_blk_img L A mem md V (16 * C) (a - V) HM (HV HC) ltac:(lia)).
  replace (V + (a - V)) with a by lia. exact Ha.
Qed.

Lemma hf_list_pos : forall L A mem LA l lines q, list_at Bm L A mem LA l lines -> In q (list_blocks l) ->
  exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem LA l lines q (_ & _ & AR & _ & _ & FA) Hq. unfold list_blocks in Hq.
  apply in_app_iff in Hq as [Hq|Hq].
  - destruct (hl_cap l =? 0) eqn:EC; [destruct Hq|]. apply Z.eqb_neq in EC. destruct Hq as [<-|[]].
    destruct AR as [(X & _)|(Hc & Hin & _)]; [lia|]. exists (16 * hl_cap l). split; [lia | exact Hin].
  - apply in_map_iff in Hq as (r & <- & Hr). rewrite Forall_forall in FA. destruct (FA r Hr) as (Hin & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [lia | exact Hin].
Qed.

Lemma hf_list_v : forall L A mem LA l lines, list_at Bm L A mem LA l lines ->
  (0 < hl_cap l -> In (hl_v l, 16 * hl_cap l) (blocks L A) /\ In (hl_v l) (list_blocks l)).
Proof.
  intros L A mem LA l lines (_ & _ & AR & _) HC.
  destruct AR as [(X & _)|(_ & Hin & _)]; [lia|]. split; [exact Hin|].
  unfold list_blocks. rewrite (proj2 (Z.eqb_neq (hl_cap l) 0) ltac:(lia)). left. reflexivity.
Qed.

Lemma hf_lrec : forall L A mem LA l lines, list_at Bm L A mem LA l lines ->
  forall j r', nth_error (wrecs l) j = Some r' ->
  bytes_at segs mem (hl_v l + 16 * Z.of_nat j) (le8 (fst r') ++ le8 (Z_to_bv 64 (Z.of_nat (length (snd r'))))) /\
  bytes_at segs mem (bv_unsigned (fst r')) (snd r' ++ [Z_to_bv 8 0]) /\
  4096 <= bv_unsigned (fst r') /\ bv_unsigned (fst r') + Z.of_nat (length (snd r')) + 1 <= alloc_ceiling /\
  0 < hl_cap l /\ hl_v l + 16 * hl_cap l <= alloc_ceiling.
Proof.
  intros L A mem LA l lines (C & B1 & AR & ND1 & ND2 & FA) j r' Hj.
  unfold wrecs in Hj. rewrite nth_error_map in Hj.
  destruct (nth_error (hl_recs l) j) as [r|] eqn:Hr; [|discriminate]. cbn in Hj. injection Hj as <-. cbn [fst snd].
  assert (Hjl : (j < length (hl_recs l))%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
  rewrite Forall_forall in FA. destruct (FA r (nth_error_In _ _ Hr)) as (Hin & (F1 & F2 & F3) & Hc & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (U : bv_unsigned (Z_to_bv 64 (fst r)) = fst r) by (apply unsigned_lit; lia).
  rewrite U.
  destruct AR as [(X & _)|(Hcap & Hvin & (V1 & V2 & V3) & Hjk & Hv)]; [unfold hl_n in B1; lia|].
  split; [|split; [|split; [lia | split; [lia | split; lia]]]].
  - destruct Hv as [[_ BV] _]. cbn [cells_bytes cbytes] in BV. rewrite app_nil_r in BV.
    exact (hf_rec_bytes segs mem (hl_v l) (hl_recs l) (hl_junk l) j r BV Hr).
  - destruct Hc as [[_ BC] _]. cbn [cells_bytes cbytes] in BC. rewrite app_nil_r in BC. exact BC.
Qed.

Lemma hf_list_head : forall L A mem LA l lines, list_at Bm L A mem LA l lines ->
  bytes_at segs mem LA (le8 (Z_to_bv 64 (hl_v l))) /\ bytes_at segs mem (LA + 8) (le4 (Z_to_bv 64 (hl_n l))) /\
  0 <= hl_v l < 2 ^ 64 /\ (0 < hl_cap l -> 4096 <= hl_v l /\ hl_v l + 16 * hl_cap l <= alloc_ceiling).
Proof.
  intros L A mem LA l lines (C & B1 & AR & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct C as [[_ BC] _]. cbn [cells_bytes cbytes] in BC.
  apply bytes_at_app in BC. destruct BC as [B8 BC]. apply bytes_at_app in BC. destruct BC as [B4 _].
  rewrite length_le8 in B4. split; [exact B8|]. split; [exact B4|].
  destruct AR as [(X1 & X2)|(Hc & _ & (V1 & V2 & _) & _)].
  - split; [lia | intros; lia].
  - split; [lia | intros _; lia].
Qed.

Lemma src_rest_rmid : forall K sp E F L A mem md L' A' mem' md' HA h,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp - K -> MR L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  (forall a, HA <= a < HA + 96 -> img_plain Bm a) ->
  src_at Bm L A mem HA h ->
  (forall a, E a -> (HA + 80 <= a < HA + 96) \/
     (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h))) ->
  (forall q, F q -> In q (list_blocks (hs_held h))) ->
  src_base L' A' mem' HA h /\ list_at Bm L' A' mem' (HA + 64) (hs_expected h) true.
Proof.
  intros K sp E F L A mem md L' A' mem' md' HA h SEG HK HM R HP S HE HF.
  apply src_at_iff in S. destruct S as (SB & LE & LH & ND).
  pose proof (hf_list_v L A mem (HA + 80) (hs_held h) true LH) as HV.
  apply hf_nodup in ND. unfold hs_blocks in ND.
  assert (OUT : forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
                ~ In q (list_blocks (hs_held h))).
  { intros q Hq Hh.
    apply (hf_nodup_disj (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h))
             (list_blocks (hs_held h)) q); [rewrite <- !app_assoc; exact ND | exact Hq | exact Hh]. }
  assert (KQ : forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
               kept_block E F L A q).
  { intros q Hq. apply (hf_kept L A mem md E F (HA + 80) (HA + 96) (hl_cap (hs_held h)) (hl_v (hs_held h)) q HM).
    - intros a Ha. exact (proj1 (HP a ltac:(lia))).
    - exact HE.
    - intros HC. exact (proj1 (HV HC)).
    - intros X. exact (OUT q Hq (HF q X)).
    - intros HC EQ. subst q. exact (OUT _ Hq (proj2 (HV HC))). }
  assert (NE : forall i, 0 <= i < 80 -> img_plain Bm (HA + i) /\ ~ E (HA + i)).
  { intros i Hi. split; [apply HP; lia|].
    exact (hf_img_notE E (HA + 80) (HA + 96) (hl_cap (hs_held h)) (hl_v (hs_held h)) (HA + i) L A mem md HM HE
             (fun HC => proj1 (HV HC)) (proj1 (HP (HA + i) ltac:(lia))) ltac:(lia)). }
  split.
  - apply (src_base_rmid K sp E F L A mem md L' A' mem' md' HA h SEG HK HM R SB).
    + intros i Hi. apply NE. lia.
    + intros q [Hq|Hq]; apply KQ; [apply in_or_app; left; exact Hq|].
      subst q. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity.
  - apply (list_at_rmid K sp E F L A mem md L' A' mem' md' (HA + 64) _ true SEG HK HM R LE).
    + intros i Hi. replace (HA + 64 + i) with (HA + (64 + i)) by lia. apply NE. lia.
    + intros q Hq. apply KQ. apply in_app_iff. right. apply in_app_iff. right. exact Hq.
Qed.

Lemma src_at_set_held : forall L A mem HA h H',
  src_base L A mem HA h -> list_at Bm L A mem (HA + 64) (hs_expected h) true ->
  list_at Bm L A mem (HA + 80) H' true ->
  (forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
     ~ In q (list_blocks H')) ->
  NoDup (hs_blocks h) ->
  src_at Bm L A mem HA (set_held h H').
Proof.
  intros L A mem HA h H' SB LE LH D ND. apply src_at_iff.
  split; [exact SB|]. split; [exact LE|]. split; [exact LH|].
  apply hf_nodup. apply hf_nodup in ND. unfold hs_blocks in *. unfold set_held. cbn [hs_pending hs_partial hs_expected hs_held].
  replace (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h) ++ list_blocks H')
    with ((list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ++ list_blocks H')
    by (rewrite <- !app_assoc; reflexivity).
  apply hf_nodup_app; [ | exact (list_blocks_nodup L A mem _ _ _ LH) | exact D].
  apply (hf_nodup_l _ (list_blocks (hs_held h))). rewrite <- !app_assoc. exact ND.
Qed.

Lemma src_parts_pos : forall L A mem HA h, src_base L A mem HA h ->
  list_at Bm L A mem (HA + 64) (hs_expected h) true ->
  forall q, In q (list_blocks (hs_pending h) ++ [hs_partial h] ++ list_blocks (hs_expected h)) ->
  exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem HA h SB LE q Hq. pose proof SB as (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & PIn & _).
  apply in_app_iff in Hq as [Hq|Hq]; [exact (hf_list_pos L A mem _ _ _ q LP Hq)|].
  apply in_app_iff in Hq as [Hq|Hq]; [destruct Hq as [<-|[]]; exists 6000; split; [lia | exact PIn]|].
  exact (hf_list_pos L A mem _ _ _ q LE Hq).
Qed.

Lemma set_held_self : forall h, set_held h (hs_held h) = h.
Proof. intros h. destruct h. reflexivity. Qed.

End HF.
