From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotExitRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotExitWip.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition EMPTY_SLACK : list byte := map (Z_to_bv 8) [46; 0; 117; 115; 97; 103].

Lemma rom_at : forall m A bs, ro_agree rsegs m -> ro_bytes_b rsegs A bs = true -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof.
  intros m A bs RO HB H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct (nth_error bs i) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
  destruct (ro_bytes_nth rsegs bs A i x (ro_bytes_b_sound rsegs bs A HB) Ex) as [R1 R2].
  unfold ro_agree in RO. rewrite (RO _ R2). exact R1.
Qed.

Lemma empty_at : forall m, ro_agree rsegs m -> bytes_at rsegs m 0x102e9 ([] ++ Z_to_bv 8 0 :: EMPTY_SLACK).
Proof.
  intros m RO. apply rom_at; [exact RO| vm_compute; reflexivity | lia | cbn; lia].
Qed.

Lemma empty_ro : forall i, 0 <= i < Z.of_nat (length ([] : list byte) + 1 + length EMPTY_SLACK) ->
  ro_addr rsegs (Z_to_bv 64 (0x102e9 + i)) = true.
Proof.
  intros i Hi. cbn in Hi.
  assert (C : forallb (fun n => ro_addr rsegs (Z_to_bv 64 (0x102e9 + Z.of_nat n))) (seq 0 7) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat i) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in C by lia. exact C.
Qed.

Lemma empty_nz : ~ In (Z_to_bv 8 0) ([] : list byte).
Proof. intros []. Qed.

Lemma find_text_lt : forall y rs i, find_text y rs = Some i -> (i < length rs)%nat.
Proof.
  intros y rs. induction rs as [|r rs IH]; intros i H; cbn [find_text] in H; [discriminate|].
  destruct (list_eqb (bzs (snd r)) (bzs y)); [injection H as <-; cbn; lia|].
  destruct (find_text y rs) as [i'|] eqn:Ef; cbn [option_map] in H; [|discriminate].
  injection H as <-. specialize (IH i' eq_refl). cbn. lia.
Qed.

Lemma in_drop_nth : forall (rs : list (Z * list byte)) i x, (i < length rs)%nat ->
  (In x rs <-> In x (drop_nth i rs) \/ nth i rs (0, []) = x).
Proof.
  intros rs i x Hi. pose proof (split_at rs i (0, []) Hi) as Q. unfold drop_nth. split; intros X.
  - rewrite Q in X. apply in_app_iff in X as [X|[X|X]].
    + left. apply in_or_app. left. exact X.
    + right. exact X.
    + left. apply in_or_app. right. exact X.
  - rewrite Q. destruct X as [X|X].
    + apply in_app_iff in X as [X|X]; apply in_or_app; [left; exact X|right; right; exact X].
    + apply in_or_app. right. left. exact X.
Qed.

Lemma ends_run_len : forall P w rs d rs' ds c, ends_run P rs d w = Some (rs', ds, c) ->
  (length rs' + w = length rs)%nat /\ (forall x, In x rs <-> In x rs' \/ In x ds).
Proof.
  intros P w. induction w as [|w IH]; intros rs d rs' ds c H; cbn [ends_run] in H.
  - injection H as <- <- <-. split; [lia|]. intros x. cbn [In]. tauto.
  - destruct (split_nul d) as [[l d']|]; [|cbn in H; discriminate]. cbv zeta in H.
    destruct (Nat.leb 4 (length l) && list_eqb (bzs (skipn (length l - 4) l)) (bzs END4) && prefixb P l);
      [|cbn in H; discriminate].
    destruct (find_text (firstn (length l - 4) l) rs) as [i|] eqn:Ef; [|cbn in H; discriminate].
    destruct (ends_run P (drop_nth i rs) d' w) as [[[r0 d0] c0]|] eqn:Er; [|cbn in H; discriminate].
    injection H as <- <- <-.
    destruct (IH _ _ _ _ _ Er) as [L1 I1]. pose proof (find_text_lt _ _ _ Ef) as Hi.
    rewrite drop_nth_length in L1 by exact Hi. split; [lia|].
    intros x. rewrite (in_drop_nth rs i x Hi), (I1 x). cbn [In]. tauto.
Qed.

Lemma filter_nil_none : forall (rs : list (Z * list byte)), filter (fun r => negb (prefixb [] (snd r))) rs = [].
Proof. induction rs as [|r rs IH]; [reflexivity|]. cbn [filter]. exact IH. Qed.

Lemma filter_nil_all : forall (rs : list (Z * list byte)), filter (fun r => prefixb [] (snd r)) rs = rs.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  change (r :: filter (fun r => prefixb [] (snd r)) rs = r :: rs). rewrite IH. reflexivity.
Qed.

Lemma nodup_concat_nth : forall {X Y} (f : X -> list Y) (l : list X) d p p' q,
  List.NoDup (concat (map f l)) -> (p < length l)%nat -> (p' < length l)%nat -> p <> p' ->
  In q (f (nth p l d)) -> In q (f (nth p' l d)) -> False.
Proof.
  intros X Y f l d. induction l as [|x l IH]; intros p p' q ND Hp Hp' Hne H1 H2; cbn [length] in *; [lia|].
  cbn [map concat] in ND.
  assert (INC : forall r, (r < length l)%nat -> In q (f (nth r l d)) -> In q (concat (map f l))).
  { intros r Hr Hq. apply in_concat. exists (f (nth r l d)). split; [apply in_map, nth_In; exact Hr|exact Hq]. }
  destruct p as [|p]; destruct p' as [|p']; cbn [nth] in H1, H2.
  - lia.
  - exact (hf_nodup_disj _ _ q ND H1 (INC p' ltac:(lia) H2)).
  - exact (hf_nodup_disj _ _ q ND H2 (INC p ltac:(lia) H1)).
  - apply (IH p p' q); [|lia|lia|lia|exact H1|exact H2]. exact (List.NoDup_app_remove_l _ _ ND).
Qed.

Lemma f2_nth : forall {X Y} (P : X -> Y -> Prop) l1 l2 d1 d2 n, Forall2 P l1 l2 -> (n < length l1)%nat ->
  P (nth n l1 d1) (nth n l2 d2).
Proof.
  intros X Y P l1 l2 d1 d2 n H. revert n. induction H as [|x y l1 l2 Hxy H IH]; intros n Hn;
    cbn [length] in Hn; [lia|].
  destruct n as [|n]; cbn [nth]; [exact Hxy|apply IH; lia].
Qed.

Lemma entries_out_split : forall es i e, nth_error es i = Some e ->
  skipn (Z.to_nat (entries_total (firstn i es))) (entries_out es) = keys_out (re_keys e) ++ entries_out (skipn (S i) es).
Proof.
  induction es as [|e0 es IH]; intros i e H; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in H.
  - injection H as <-. reflexivity.
  - pose proof (keys_out_length (re_keys e0)) as K. pose proof (keys_total_nonneg (re_keys e0)).
    pose proof (exit_entries_nonneg (firstn i es)).
    change (entries_total (firstn (S i) (e0 :: es))) with (keys_total (re_keys e0) + entries_total (firstn i es)).
    change (entries_out (e0 :: es)) with (keys_out (re_keys e0) ++ entries_out es).
    change (skipn (S (S i)) (e0 :: es)) with (skipn (S i) es).
    replace (Z.to_nat (keys_total (re_keys e0) + entries_total (firstn i es)))
      with (length (keys_out (re_keys e0)) + Z.to_nat (entries_total (firstn i es)))%nat by lia.
    rewrite skipn_app, skipn_all2 by lia.
    replace (length (keys_out (re_keys e0)) + Z.to_nat (entries_total (firstn i es)) - length (keys_out (re_keys e0)))%nat
      with (Z.to_nat (entries_total (firstn i es))) by lia.
    cbn [app]. apply IH. exact H.
Qed.

Lemma entries_total_S : forall es i e, nth_error es i = Some e ->
  entries_total (firstn (S i) es) = entries_total (firstn i es) + keys_total (re_keys e).
Proof.
  induction es as [|e0 es IH]; intros i e H; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error] in H.
  - injection H as <-. unfold entries_total. cbn [firstn fold_right]. rewrite Z.add_0_r, Z.add_0_l. reflexivity.
  - specialize (IH i e H). unfold entries_total in *. cbn [firstn fold_right] in *. rewrite IH. ring.
Qed.

Lemma entries_total_le : forall es n, entries_total (firstn n es) <= entries_total es.
Proof.
  induction es as [|e es IH]; intros n; [destruct n; cbn; lia|].
  pose proof (exit_entries_nonneg es) as NN. pose proof (keys_total_nonneg (re_keys e)) as NK.
  specialize (IH (Nat.pred n)). unfold entries_total in *.
  destruct n as [|n]; cbn [firstn fold_right Nat.pred] in *; lia.
Qed.

Lemma held_done_blocks : forall h H' q, hl_v H' = hl_v (hs_held h) -> hl_cap H' = hl_cap (hs_held h) ->
  hl_recs H' = [] -> In q (hs_blocks (set_held h H')) -> In q (hs_blocks h).
Proof.
  intros h H' q EV EC ER Hq. unfold hs_blocks, set_held in *. cbn [hs_pending hs_partial hs_expected hs_held] in Hq.
  rewrite !in_app_iff in Hq |- *. destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [tauto|tauto|tauto|].
  right; right; right. unfold list_blocks in Hq |- *. rewrite EV, EC, ER in Hq. cbn [map] in Hq.
  rewrite app_nil_r in Hq. apply in_or_app. left. exact Hq.
Qed.

Lemma held_in_blocks : forall h q, In q (list_blocks (hs_held h)) -> In q (hs_blocks h).
Proof. intros h q Hq. unfold hs_blocks. rewrite !in_app_iff. tauto. Qed.

Lemma rw_writable : forall segs m a cs i, rw_cells segs m a cs -> 0 <= i < Z.of_nat (cells_size cs) ->
  writable_at segs m (a + i).
Proof. intros segs m a cs i (_ & _ & _ & W) Hi. exact (W i Hi). Qed.

Section Wid.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma rmid_widen_E : forall K1 sp1 K sp (Ee Ee' Ff : Z -> Prop) L A mem md L' A' mem' md',
  aa_MR API L A mem md ->
  sp - K <= sp1 - K1 -> sp1 <= sp -> @YM05.alloc_ceiling rc <= sp - K -> sp <= 2 ^ 64 ->
  (forall a, sp - K <= a < sp -> writable_at (ms_segs B) mem a) ->
  (forall a, Ee a \/ ~ Ee a) ->
  (forall a, Ee a -> (sp - K <= a < sp) \/ Ee' a) ->
  (forall a, sp - K <= a < sp -> Ee a -> writable_at (ms_segs B) mem' a) ->
  rmid B API K1 sp1 Ee Ff L A mem md L' A' mem' md' ->
  rmid B API K sp Ee' Ff L A mem md L' A' mem' md'.
Proof.
  intros K1 sp1 K sp Ee Ee' Ff L A mem md L' A' mem' md' HM H1 H2 H3 H4 HWS ED HE HWE
    (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & MD1 & BY1 & BK1 & SC1).
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL. pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [exact LY1|]. split; [exact LN1|].
  split; [exact PA1|]. split; [exact SV1|]. split; [exact Z01|]. split; [exact OW1|]. split; [exact MD1|].
  split.
  { intros a Ha NO NO' NS NE. apply BY1; [exact Ha | exact NO | exact NO' | |].
    - unfold sk in *. intros [X|X]; apply NS; [left; lia | right; exact X].
    - intros X. destruct (HE a X) as [Y|Y]; [apply NS; unfold sk; left; exact Y | exact (NE Y)]. }
  split.
  { intros p n i Hp Hp' NF Hi NE. apply (BK1 p n i); [exact Hp | exact Hp' | exact NF | exact Hi |].
    intros X. destruct (HE _ X) as [Y|Y]; [|exact (NE Y)].
    destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HM Hp Hi) as (_ & R1 & R2 & _). lia. }
  intros a Ha.
  assert (D : sk B K1 sp1 a \/ ~ sk B K1 sp1 a) by (unfold sk; lia).
  destruct D as [D|D]; [exact (SC1 a D)|].
  unfold sk in Ha. destruct Ha as [Ha|Ha]; [|exfalso; apply D; right; exact Ha].
  destruct (ED a) as [X|X]; [exact (HWE a Ha X)|].
  assert (NO : ~ owned B L A a) by (intro Y; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Y); lia).
  assert (NO' : ~ owned B L' A' a) by (intro Y; pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M1 Y); lia).
  assert (Hr : @YM05.alloc_ceiling rc <= a < 2 ^ 64) by lia.
  apply (proj2 (BY1 a (or_introl Hr) NO NO' D X)). exact (HWS a ltac:(lia)).
Qed.

Lemma img_keep : AllocExtra B (aa_MR API) -> ms_segs B = rsegs ->
  forall K sp (Ee Ff : Z -> Prop) L A mem md L' A' mem' md' X Y C V a cs,
  @YM05.alloc_ceiling rc <= sp - K -> aa_MR API L A mem md ->
  rmid B API K sp Ee Ff L A mem md L' A' mem' md' ->
  (forall x, Ee x -> (X <= x < Y) \/ (0 < C /\ V <= x < V + 16 * C)) ->
  (0 < C -> In (V, 16 * C) (blocks L A)) ->
  rw_cells (ms_segs B) mem a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain B (a + i) /\ ~ (X <= a + i < Y)) ->
  rw_cells (ms_segs B) mem' a cs.
Proof.
  intros AX SEG K sp Ee Ff L A mem md L' A' mem' md' X Y C V a cs HK HM R HE HV H D.
  apply (rmid_rw_img B API AX K sp Ee Ff L A mem md L' A' mem' md' a cs (hg_img_low B SEG) HK HM R H).
  intros i Hi. destruct (D i Hi) as [P N]. split; [exact P|].
  exact (hf_img_notE B API AX Ee X Y C V (a + i) L A mem md HM HE HV (proj1 P) N).
Qed.

End Wid.
