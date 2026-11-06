From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadQ RelayRunT RelayRunF HarnessGlue
  relay_event_b_c check_shape_event_c strnlen_c memcpy_c SlotPass7D SlotPass7R HarnessFrame.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bytes_split3 : forall segs m a (txt : list byte) (z : byte) sl,
  bytes_at segs m a (txt ++ [z]) -> bytes_at segs m (a + Z.of_nat (length txt) + 1) sl ->
  bytes_at segs m a (txt ++ z :: sl).
Proof.
  intros segs m a txt z sl H1 H2.
  replace (txt ++ z :: sl) with ((txt ++ [z]) ++ sl) by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app. split; [exact H1|]. rewrite length_app. cbn [length].
  replace (a + Z.of_nat (length txt + 1)) with (a + Z.of_nat (length txt) + 1) by lia. exact H2.
Qed.

Lemma bytes_prefix3 : forall segs m a (txt : list byte) (z : byte) sl,
  bytes_at segs m a (txt ++ z :: sl) -> bytes_at segs m a (txt ++ [z]).
Proof.
  intros segs m a txt z sl H.
  replace (txt ++ z :: sl) with ((txt ++ [z]) ++ sl) in H by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in H. exact (proj1 H).
Qed.

Fixpoint slack_at (segs : list Segment) (m : word -> option byte) (a : Z) (n : nat) : list byte :=
  match n with
  | O => []
  | S n' => match mbyte segs m a with Some b => b | None => Z_to_bv 8 0 end :: slack_at segs m (a + 1) n'
  end.

Lemma slack_at_len : forall segs m n a, length (slack_at segs m a n) = n.
Proof. intros segs m n. induction n as [|n IH]; intros a; [reflexivity|]. cbn [slack_at length]. rewrite IH. reflexivity. Qed.

Lemma slack_at_nth : forall segs m n a i, (i < n)%nat ->
  nth_error (slack_at segs m a n) i =
  Some (match mbyte segs m (a + Z.of_nat i) with Some b => b | None => Z_to_bv 8 0 end).
Proof.
  intros segs m n. induction n as [|n IH]; intros a i Hi; [lia|].
  destruct i as [|i]; cbn [slack_at nth_error].
  - replace (a + Z.of_nat 0) with a by lia. reflexivity.
  - rewrite IH by lia. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. reflexivity.
Qed.

Lemma slack_at_bytes : forall segs m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present m (a + i)) -> bytes_at segs m a (slack_at segs m a n).
Proof.
  intros segs m a n H0 H1 HP. apply bytes_at_of_mbyte; [exact H0|rewrite slack_at_len; exact H1|].
  intros i Hi. rewrite slack_at_len in Hi. rewrite slack_at_nth by exact Hi.
  destruct (HP (Z.of_nat i) ltac:(lia)) as [b Hb]. unfold mbyte. rewrite Hb. reflexivity.
Qed.

Definition rekey (f : Z * list byte * list byte -> list byte) (k : Z * list byte * list byte)
  : Z * list byte * list byte := (fst k, f k).

Definition reslack (f : Z * list byte * list byte -> list byte) (e : rentry) : rentry :=
  RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e)
     (re_hp e) (re_kh e) (re_pad2 e) (map (rekey f) (re_keys e)) (re_U e) (re_junk e).

Definition new_slack (segs : list Segment) (m : word -> option byte) (k : Z * list byte * list byte)
  : list byte :=
  slack_at segs m (key_addr k + Z.of_nat (length (key_text k)) + 1)
    (Z.to_nat ((- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8)).

Lemma rekey_addr : forall f ks, map key_addr (map (rekey f) ks) = map key_addr ks.
Proof. intros f ks. rewrite map_map. reflexivity. Qed.
Lemma rekey_text : forall f ks, map key_text (map (rekey f) ks) = map key_text ks.
Proof. intros f ks. rewrite map_map. reflexivity. Qed.
Lemma rekey_texts : forall f ks, keys_texts (map (rekey f) ks) = keys_texts ks.
Proof. intros f ks. unfold keys_texts. rewrite map_map. reflexivity. Qed.
Lemma rekey_ptrs : forall f ks, key_ptrs (map (rekey f) ks) = key_ptrs ks.
Proof. intros f ks. unfold key_ptrs. rewrite map_map. reflexivity. Qed.
Lemma rekey_total : forall f ks, keys_total (map (rekey f) ks) = keys_total ks.
Proof.
  intros f. induction ks as [|q ks IH]; [reflexivity|].
  change (Z.of_nat (length (key_text q)) + 5 + keys_total (map (rekey f) ks) =
          Z.of_nat (length (key_text q)) + 5 + keys_total ks). rewrite IH. reflexivity.
Qed.
Lemma reslack_bytes : forall f e, entry_bytes (reslack f e) = entry_bytes e.
Proof. intros f e. unfold entry_bytes, re_nheld. cbn. rewrite length_map. reflexivity. Qed.
Lemma reslack_blocks : forall f e, entry_blocks (reslack f e) = entry_blocks e.
Proof. intros f e. unfold entry_blocks. cbn. rewrite rekey_addr. reflexivity. Qed.
Lemma reslack_target : forall f G OUT es hj,
  target_addrs G OUT (map (reslack f) es) hj = target_addrs G OUT es hj.
Proof.
  intros f G OUT es hj. unfold target_addrs. rewrite map_map.
  assert (H : map (fun e => entry_blocks (reslack f e)) es = map entry_blocks es).
  { apply map_ext. apply reslack_blocks. } rewrite H. reflexivity.
Qed.
Lemma reslack_cost : forall f es hj, slot_cost (map (reslack f) es) hj = slot_cost es hj.
Proof.
  intros f es. induction es as [|e es IH]; intros [|h hj]; try reflexivity.
  change (pair_cost (reslack f e) h + slot_cost (map (reslack f) es) hj = pair_cost e h + slot_cost es hj).
  rewrite IH. unfold pair_cost. cbn [reslack re_keys re_skip re_used]. rewrite rekey_total. reflexivity.
Qed.

Lemma reslack_wt : forall f es hj, nc_wt (map (reslack f) es) hj = nc_wt es hj.
Proof.
  intros f es hj.
  assert (W : AllocBound.zsum nw_ent (map (reslack f) es) = AllocBound.zsum nw_ent es).
  { induction es as [|e es IH]; [reflexivity|]. cbn [map]. rewrite !AllocBound.zsum_cons, IH. f_equal.
    unfold nw_ent, re_nheld. cbn [reslack re_cap re_used re_hp re_kh re_keys]. rewrite length_map. reflexivity. }
  unfold nc_wt. rewrite W, length_map. reflexivity.
Qed.

Lemma nd_out : forall (x y : Z) l, List.NoDup (x :: y :: l) -> forall q, In q (x :: l) -> q <> y.
Proof.
  intros x y l H q Hq E. subst q. inversion H as [|? ? H1 H2]; subst. inversion H2 as [|? ? H3 H4]; subst.
  destruct Hq as [E|E]; [apply H1; left; exact (eq_sym E)|exact (H3 E)].
Qed.

Lemma nd_swap : forall (x y y' : Z) l, List.NoDup (x :: y :: l) -> ~ In y' (x :: l) -> List.NoDup (x :: y' :: l).
Proof.
  intros x y y' l H N. inversion H as [|? ? H1 H2]; subst. inversion H2 as [|? ? H3 H4]; subst.
  constructor.
  - intros [E|E]; [apply N; left; exact (eq_sym E)|apply H1; right; exact E].
  - constructor; [intros E; apply N; right; exact E|exact H4].
Qed.

Section PS.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.

Lemma entry_pos : forall L A mem e q, RelayRep.entry_ok B L A mem e -> In q (entry_blocks e) ->
  exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem e q (_ & _ & _ & _ & _ & _ & _ & _ & _ & BU & _ & HP & _ & _ & KS) Hq.
  unfold entry_blocks in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (re_cap e =? 0) eqn:EC; [destruct Hq|]. apply Z.eqb_neq in EC. destruct Hq as [<-|[]].
    destruct BU as [(X & _)|(C & IN & _)]; [lia|]. exists (re_cap e). split; [exact C|exact IN].
  - apply in_app_iff in Hq as [Hq|Hq].
    + destruct (re_hp e =? 0) eqn:EH; [destruct Hq|]. apply Z.eqb_neq in EH. destruct Hq as [<-|[]].
      destruct HP as [(X & _)|(IN & _ & _ & HK & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
    + apply in_map_iff in Hq as (k & <- & Hk). rewrite Forall_forall in KS. destruct (KS k Hk) as (IN & _).
      exists (Z.of_nat (length (key_text k)) + 1). split; [lia|exact IN].
Qed.

Lemma src_pos : forall L A mem HA h q, src_at B L A mem HA h -> In q (hs_blocks h) ->
  exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem HA h q (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & PIn & _ & _ & _ & _ & LE & LH & _) Hq.
  unfold hs_blocks in Hq. apply in_app_iff in Hq as [Hq|Hq]; [exact (hf_list_pos B L A mem _ _ _ q LP Hq)|].
  apply in_app_iff in Hq as [Hq|Hq]; [destruct Hq as [<-|[]]; exists 6000; split; [lia|exact PIn]|].
  apply in_app_iff in Hq as [Hq|Hq];
    [exact (hf_list_pos B L A mem _ _ _ q LE Hq)|exact (hf_list_pos B L A mem _ _ _ q LH Hq)].
Qed.

Lemma relay_pos : forall L A mem t nfd G OUT es hj, relay_at B L A mem t nfd G OUT es hj ->
  forall q, In q (G :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj)) ->
  exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem t nfd G OUT es hj (_ & IN & _ & ES & _ & _ & PA & _) q [<-|Hq].
  { exists SRC_TABLE. split; [unfold SRC_TABLE, SRC_ENTRY; lia|exact IN]. }
  apply in_app_iff in Hq as [Hq|Hq].
  - apply in_concat in Hq as (l & Hl & Hq). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in ES. exact (entry_pos L A mem e q (ES e He) Hq).
  - apply in_concat in Hq as (l & Hl & Hq). apply in_map_iff in Hl as (p & <- & Hp).
    destruct (pair_find _ _ _ es hj p PA Hp) as (e & HE). destruct HE as (SRC & _).
    exact (src_pos L A mem _ _ q SRC Hq).
Qed.

End PS.

Section RK.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BW : blocks_writable B API.
Hypothesis SL : block_slack_present B API.
Variables (K sp : Z) (E F : Z -> Prop) (OUT : Z).
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Variables (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model).
Hypothesis HK : YM05.alloc_ceiling <= sp - K.
Hypothesis HM : aa_MR API L A mem md.
Hypothesis HR : rmid B API K sp E F L A mem md L' A' mem' md'.
Hypothesis KP : forall q k, In (q, k) (blocks L A) -> q <> OUT -> kept_block E F L A q.
Hypothesis IP : forall a, 0x31040 <= a < 0x311c0 -> img_plain B a /\ ~ E a.

Lemma rk_block : forall q k, In (q, k) (blocks L A) -> 0 < k -> q <> OUT -> In (q, k) (blocks L' A').
Proof.
  intros q k H Hk HO. destruct (KP q k H HO) as (NF & NE).
  exact (proj1 (rmid_block B API BW K sp E F L A mem md L' A' mem' md' q k 0 HR H Hk NF ltac:(lia)
    (NE k 0 H ltac:(lia)))).
Qed.

Lemma rk_cells : forall q k a cs, In (q, k) (blocks L A) -> 0 < k -> q <> OUT ->
  rw_cells (ms_segs B) mem a cs -> q <= a -> a + Z.of_nat (cells_size cs) <= q + k ->
  rw_cells (ms_segs B) mem' a cs.
Proof.
  intros q k a cs H Hk HO C H1 H2. destruct (KP q k H HO) as (NF & NE).
  apply (rmid_rw_block B API BW K sp E F L A mem md L' A' mem' md' q k a cs HR H Hk NF C H1 H2).
  intros i Hi. replace (a + i) with (q + (a - q + i)) by lia. exact (NE k (a - q + i) H ltac:(lia)).
Qed.

Lemma rk_bytes : forall q k a bs, In (q, k) (blocks L A) -> 0 < k -> q <> OUT ->
  bytes_at (ms_segs B) mem a bs -> q <= a -> a + Z.of_nat (length bs) <= q + k ->
  bytes_at (ms_segs B) mem' a bs.
Proof.
  intros q k a bs H Hk HO C H1 H2. destruct (KP q k H HO) as (NF & NE).
  apply (rmid_bytes_block B API BW K sp E F L A mem md L' A' mem' md' q k a bs HR H Hk NF C H1 H2).
  intros i Hi. replace (a + i) with (q + (a - q + i)) by lia. exact (NE k (a - q + i) H ltac:(lia)).
Qed.

Lemma rk_img : forall a cs, rw_cells (ms_segs B) mem a cs -> 0x31040 <= a ->
  a + Z.of_nat (cells_size cs) <= 0x311c0 -> rw_cells (ms_segs B) mem' a cs.
Proof.
  intros a cs C H1 H2.
  apply (rmid_rw_img B API AX K sp E F L A mem md L' A' mem' md' a cs (hg_img_low B SEG) HK HM HR C).
  intros i Hi. apply IP. lia.
Qed.

Lemma rk_list : forall LA l lines, list_at B L A mem LA l lines -> 0x31040 <= LA -> LA + 16 <= 0x311c0 ->
  (forall q, In q (list_blocks l) -> q <> OUT) -> list_at B L' A' mem' LA l lines.
Proof.
  intros LA l lines H H1 H2 HO.
  apply (list_at_rmid B API AX BW K sp E F L A mem md L' A' mem' md' LA l lines SEG HK HM HR H).
  - intros i Hi. apply IP. lia.
  - intros q Hq. destruct (hf_list_pos B L A mem LA l lines q H Hq) as (k & _ & Hin).
    exact (KP q k Hin (HO q Hq)).
Qed.

Lemma rk_src : forall HA h, src_at B L A mem HA h -> 0x31040 <= HA -> HA + 96 <= 0x311c0 ->
  (forall q, In q (hs_blocks h) -> q <> OUT) -> src_at B L' A' mem' HA h.
Proof.
  intros HA h S H1 H2 HO.
  assert (KB : forall q, In q (hs_blocks h) -> kept_block E F L A q).
  { intros q Hq. destruct (src_pos B L A mem HA h q S Hq) as (k & _ & Hin). exact (KP q k Hin (HO q Hq)). }
  apply src_at_iff in S. destruct S as (SB & LE & LH & ND).
  assert (LE' : list_at B L' A' mem' (HA + 64) (hs_expected h) true).
  { apply rk_list; [exact LE|lia|lia|]. intros q Hq. apply HO. unfold hs_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hq. }
  assert (LH' : list_at B L' A' mem' (HA + 80) (hs_held h) true).
  { apply rk_list; [exact LH|lia|lia|]. intros q Hq. apply HO. unfold hs_blocks.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hq. }
  apply src_at_iff. split; [|split; [exact LE'|split; [exact LH'|exact ND]]].
  apply (src_base_rmid B API AX BW K sp E F L A mem md L' A' mem' md' HA h SEG HK HM HR SB).
  - intros i Hi. apply IP. lia.
  - intros q [Hq|Hq]; apply KB; unfold hs_blocks.
    + apply in_or_app. left. exact Hq.
    + subst q. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
Qed.

Lemma rk_key : forall a txt sl,
  In (a, Z.of_nat (length txt) + 1) (blocks L A) -> fresh_block B a (Z.of_nat (length txt) + 1) ->
  bytes_at (ms_segs B) mem a (txt ++ Z_to_bv 8 0 :: sl) -> a <> OUT ->
  In (a, Z.of_nat (length txt) + 1) (blocks L' A') /\
  bytes_at (ms_segs B) mem' a (txt ++ Z_to_bv 8 0 :: slack_at (ms_segs B) mem' (a + Z.of_nat (length txt) + 1)
    (Z.to_nat ((- (a + Z.of_nat (length txt) + 1)) mod 8))).
Proof.
  intros a txt sl IN FR HB HO.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct FR as (F1 & F2 & _).
  assert (IN' : In (a, Z.of_nat (length txt) + 1) (blocks L' A')) by (apply rk_block; [exact IN|lia|exact HO]).
  split; [exact IN'|].
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length txt) + 1)) 8 ltac:(lia)) as R8.
  apply bytes_split3.
  - eapply rk_bytes; [exact IN|lia|exact HO|exact (bytes_prefix3 _ _ _ _ _ _ HB)|lia|].
    rewrite length_app. cbn [length]. lia.
  - apply slack_at_bytes; [lia|rewrite Z2Nat.id by lia; lia|].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    pose proof HR as (M' & _).
    apply (SL L' A' mem' md' a (Z.of_nat (length txt) + 1) _ M' IN').
    assert (E8 : forall N, 8 * ((N + 7) / 8) = N + (- N) mod 8) by (intros N; Z.div_mod_to_equations; lia).
    replace (a + (Z.of_nat (length txt) + 1)) with (a + Z.of_nat (length txt) + 1) by lia.
    rewrite E8. lia.
Qed.

Lemma rk_entry : forall e, RelayRep.entry_ok B L A mem e -> (forall q, In q (entry_blocks e) -> q <> OUT) ->
  RelayRep.entry_ok B L' A' mem' (reslack (new_slack (ms_segs B) mem') e).
Proof.
  intros e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS) HO.
  unfold RelayRep.entry_ok, re_nheld in *.
  cbn [reslack re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, rekey_ptrs, rekey_addr, rekey_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    assert (Q : re_buf e <> OUT).
    { apply HO. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_cap e) 0) ltac:(lia)). left. reflexivity. }
    split; [exact C|]. split; [exact (rk_block _ _ IN C Q)|]. split; [exact FR|]. split; [exact J|].
    eapply rk_cells; [exact IN|exact C|exact Q|exact BC|lia|].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
  split; [exact H10|]. split.
  { destruct HP as [(HP0 & HK0)|(IN & FR & HC & HH & HBY)].
    - left. split; [exact HP0|]. rewrite HK0. reflexivity.
    - right. pose proof FR as (FR1 & _).
      assert (Q : re_hp e <> OUT).
      { apply HO. unfold entry_blocks. rewrite (proj2 (Z.eqb_neq (re_hp e) 0) ltac:(lia)).
        apply in_or_app. right. left. reflexivity. }
      split; [exact (rk_block _ _ IN ltac:(lia) Q)|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply rk_bytes; [exact IN|lia|exact Q|exact HBY|lia|]. rewrite slot_key_ptrs_length. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. rewrite Forall_forall in KS |- *. intros [[a txt] sl] Hk.
  destruct (KS _ Hk) as (IN & FR & HBY & NZ & LEN & PAD).
  cbn [rekey key_addr key_text key_slack fst snd] in IN, FR, HBY, NZ, LEN, PAD |- *.
  assert (Q : a <> OUT).
  { apply HO. unfold entry_blocks. apply in_or_app. right. apply in_or_app. right.
    change a with (key_addr (a, txt, sl)). apply in_map. exact Hk. }
  destruct (rk_key a txt sl IN FR HBY Q) as (IN' & HBY').
  unfold new_slack. cbn [key_addr key_text fst snd].
  split; [exact IN'|]. split; [exact FR|]. split; [exact HBY'|]. split; [exact NZ|]. split; [exact LEN|].
  rewrite slack_at_len.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma rk_pair : forall t e p, pair_ok B L A mem t e p -> (forall q, In q (hs_blocks (fst p)) -> q <> OUT) ->
  pair_ok B L' A' mem' t (reslack (new_slack (ms_segs B) mem') e) p.
Proof.
  intros t e p HP HO. unfold pair_ok in *. cbv zeta in *.
  cbn [reslack re_keys re_fd re_skip re_used re_eof re_U]. rewrite rekey_texts.
  destruct HP as (SRC & HI & REST).
  split; [|split; [exact HI|exact REST]].
  apply rk_src; [exact SRC|unfold G_S, SRC_SIZE; lia|unfold G_S, SRC_SIZE; lia|exact HO].
Qed.

Lemma rk_pairs : forall t es hj, Forall2 (pair_ok B L A mem t) es hj ->
  (forall p, In p hj -> forall q, In q (hs_blocks (fst p)) -> q <> OUT) ->
  Forall2 (pair_ok B L' A' mem' t) (map (reslack (new_slack (ms_segs B) mem')) es) hj.
Proof.
  intros t es hj H. induction H as [|e p es hj HE HF IH]; intros HO; cbn [map]; constructor.
  - apply rk_pair; [exact HE|]. apply HO. left. reflexivity.
  - apply IH. intros p' Hp'. apply HO. right. exact Hp'.
Qed.

Lemma rk_relay : forall t nfd G OUT' es hj,
  relay_at B L A mem t nfd G OUT es hj ->
  (forall q, In q (G :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj)) ->
     q <> OUT') ->
  relay_at B L' A' mem' t nfd G OUT' (map (reslack (new_slack (ms_segs B) mem')) es) hj.
Proof.
  intros t nfd G OUT' es hj ((tail & HT & TC) & IN & FR & ES & ND & FD & PA & NDH & ZH & NDA) NO.
  pose proof NDA as NDL. unfold target_addrs in NDL. apply hf_nodup in NDL.
  pose proof (nd_out _ _ _ NDL) as NOUT.
  assert (GO : G <> OUT) by (apply NOUT; left; reflexivity).
  assert (GK : 0 < SRC_TABLE) by (unfold SRC_TABLE, SRC_ENTRY; lia).
  split.
  { exists tail. split; [rewrite length_map; exact HT|].
    assert (EB : map entry_bytes (map (reslack (new_slack (ms_segs B) mem')) es) = map entry_bytes es).
    { rewrite map_map. apply map_ext. apply reslack_bytes. }
    rewrite EB. eapply rk_cells; [exact IN|exact GK|exact GO|exact TC|lia|].
    cbn [cells_size csize]. unfold SRC_TABLE, SRC_ENTRY. lia. }
  split; [exact (rk_block G SRC_TABLE IN GK GO)|]. split; [exact FR|]. split.
  { apply Forall_map. rewrite Forall_forall in ES |- *. intros e He. apply rk_entry; [exact (ES e He)|].
    intros q Hq. apply NOUT. right. apply in_or_app. left. apply in_concat. exists (entry_blocks e).
    split; [apply in_map; exact He|exact Hq]. }
  split; [rewrite map_map; exact ND|]. split; [apply Forall_map; exact FD|]. split.
  { apply rk_pairs; [exact PA|]. intros p Hp q Hq. apply NOUT. right. apply in_or_app. right.
    apply in_concat. exists (hs_blocks (fst p)).
    split; [apply (in_map (fun p => hs_blocks (fst p))); exact Hp|exact Hq]. }
  split; [exact NDH|]. split.
  { intros i HI HZ. apply rk_img; [exact (ZH i HI HZ)|unfold G_S, SRC_SIZE; lia|].
    cbn [cells_size csize]. unfold G_S, SRC_SIZE. lia. }
  rewrite reslack_target. unfold target_addrs. apply hf_nodup. apply (nd_swap _ _ _ _ NDL).
  intros X. exact (NO OUT' X eq_refl).
Qed.

End RK.

Theorem op7_rb_relay_holds : op7_rb_relay_stmt.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res t nfd G es hj
    nout cap out cap' out' HF HM HWF HR HEL HFR HRES HOUT HL0 HL1 Ht HREL.
  pose proof HF as (FF & _ & PRE & _).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (SL : block_slack_present B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by
    (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (NI : forall a, 0x30fc0 <= a < 0x311c0 -> img_plain B a).
  { intros a Ha. apply PL. exists 0x30fc0, 512. split; [unfold G_reply, frame_G; right; left; reflexivity|lia]. }
  pose proof (proj1 (proj1 PRE)) as LP. destruct LP as (_ & _ & _ & _ & _ & _ & SPLO & _).
  assert (HK : @YM05.alloc_ceiling rc <= slot_sp E - OP7_K).
  { unfold slot_sp, SLOT_FRAME, OP7_K, RELAY_EVENT_K, RELAY_EVENT_FRAME, SEND_LINE_K, SEND_LINE_FRAME,
      REALLOC_STACK, ALLOC_STACK, SLOT_STACK in *. lia. }
  assert (OB : 0 < bv_unsigned cap ->
    In (bv_unsigned out, bv_unsigned cap) (blocks L A) /\ fresh_block B (bv_unsigned out) (bv_unsigned cap)).
  { intros HC. destruct HOUT as ((O & junk & [(X & _)|(_ & _ & IO & FO & _)]) & _); [lia|split; assumption]. }
  assert (KP : forall q k, In (q, k) (blocks L A) -> q <> bv_unsigned out ->
    kept_block (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A q).
  { intros q k Hin HO. split.
    - intros [X|(_ & X)]; [exact (proj1 (HRES q k Hin) X)|exact (HO X)].
    - intros k' i Hin' Hi X. pose proof (hf_blk_img B (API rc) AX L A mem md q k' i HM Hin' Hi) as NIq.
      destruct X as [X|[[X|[X|[X|(_ & X)]]]|X]].
      + exact (proj2 (HRES q k' Hin') i Hi X).
      + apply NIq. exact (proj1 (NI (q + i) ltac:(unfold G_BROKEN in X; lia))).
      + apply NIq. exact (proj1 (NI (q + i) ltac:(unfold G_EINTR in X; lia))).
      + apply NIq. exact (proj1 (NI (q + i) ltac:(unfold G_OUTV in X; lia))).
      + destruct (Z_lt_le_dec 0 (bv_unsigned cap)) as [HC|HC]; [|lia].
        destruct (OB HC) as (IO & _).
        destruct (blocks_disjoint B (API rc) L A mem md (bv_unsigned out) (bv_unsigned cap) q k' HM IO Hin'
                   (fun e => HO (eq_sym e))); lia.
      + apply NIq. exact (proj1 (NI (q + i) ltac:(unfold G_LOCK in X; lia))). }
  assert (IP : forall a, 0x31040 <= a < 0x311c0 ->
    img_plain B a /\ ~ op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL a).
  { intros a Ha. pose proof (NI a ltac:(lia)) as PA. split; [exact PA|]. destruct PA as (PI & _).
    intros [X|[[X|[X|[X|(_ & X)]]]|X]].
    - pose proof HFR as (_ & _ & NIr). apply (NIr (a - res)); [lia|].
      replace (res + (a - res)) with a by lia. exact PI.
    - unfold G_BROKEN in X. lia.
    - unfold G_EINTR in X. lia.
    - unfold G_OUTV in X. lia.
    - destruct (Z_lt_le_dec 0 (bv_unsigned cap)) as [HC|HC]; [|lia].
      destruct (OB HC) as (_ & (_ & _ & NIo)). apply (NIo (a - bv_unsigned out)); [lia|].
      replace (bv_unsigned out + (a - bv_unsigned out)) with a by lia. exact PI.
    - unfold G_LOCK in X. lia. }
  assert (NO : forall q, In q (G :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj)) ->
    q <> bv_unsigned out').
  { intros q Hq. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDA).
    unfold target_addrs in NDA. apply hf_nodup in NDA. pose proof (nd_out _ _ _ NDA q Hq) as QO.
    destruct (op7_live cl br dd EL).
    - destruct (relay_pos B L A mem t nfd G (bv_unsigned out) es hj HREL q Hq) as (k & Hk & Hin).
      exact (HL1 eq_refl q k Hin QO Hk).
    - rewrite (HL0 eq_refl). exact QO. }
  exists (map (reslack (new_slack (ms_segs B) mem')) es).
  pose proof (rk_relay B (API rc) SEG AX BW SL OP7_K (slot_sp E) _ _ (bv_unsigned out) L A mem md L' A' mem' md'
    HK HM HR KP IP t nfd G (bv_unsigned out') es hj HREL NO) as R1.
  split; [eapply relay_at_t; [exact R1|lia]|].
  split; [apply length_map|]. split; [apply reslack_cost|]. split; [apply reslack_target|]. split.
  - rewrite map_map. apply map_ext. intros x. reflexivity.
  - apply reslack_wt.
Qed.
