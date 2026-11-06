(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass9G.v, with its addresses and numbers changed; 1611 of its 1721 lines of code are new or changed and 561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass1w.v, with its module paths and module names changed; 1841 of its 1994 lines of code are new or changed and 1568 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocBound AllocPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3 SlotRun3 SlotNcMove3 SlotNcWt SlotP5R3 SlotP5Res3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c check_no_loss_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c op_add_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadP SlotEntry RelayCap SlotExitScanAux relay_instance_gone_b_c relay_remove_b_c SlotPass5Run SlotPass5Loop SlotPass5Check SlotPass1w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass5T.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Ltac l2_gs := unfold HarnessRep.G_S, Statement.G_S, CF.check_shape_ends_c.G_S, CF.drain_b_c.G_S, CF.gesture_model_c.G_S,
  CF.source_reset_c.G_S, CheckRep.G_GONE, CF.check_no_loss_c.G_GONE, CF.check_shape_ends_c.G_GONE, SRC_SIZE, SOURCES_MAX in *.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPackGSF AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3P SlotP5ResP.

Lemma l2_rd8 : forall m a (v : word), bytes_at rsegs m a (le8 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Inductive l2st : Type := L2Pre | L2Mid | L2Post.

Definition l2_segs (P : list byte) (Lss kss : list (list (list Z))) (n : nat) : list (list Z) :=
  map (fun p => gone_segment (bzs P) (nth p Lss []) (nth p kss [])) (seq 0 n).

Section L2P.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable P : list byte.

Definition l2_pre (L : layout) (A : astate) (mem : word -> option byte) (t : Z) (e : rentry) (p : hsrc * nat)
    (Ls ks : list (list Z)) : Prop :=
  let h := fst p in
  src_at B L A mem (G_S + SRC_SIZE * Z.of_nat (snd p)) h /\ (snd p < 4)%nat /\
  hs_fd h = re_fd e /\
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) /\
  map snd (hl_recs (hs_expected h)) = map (map (Z_to_bv 8)) Ls /\ Forall zrange Ls /\
  NoDup (texts (hs_held h)) /\ NoDup ks /\ same_set ks (upds (texts (hs_held h)) Ls) /\
  keys_texts (re_keys e) = snd (gei (bzs P) ks) /\
  hl_n (hs_held h) + Z.of_nat (count_begin Ls) < 2 ^ 22 /\
  hl_n (hs_pending h) <= t /\ hl_cap (hs_pending h) <= Z.max 8 (2 * t) /\
  Z.of_nat (length (pending_stream h)) <= WRITE_MAX * t /\
  ecap_ok (hl_cap (hs_expected h)) /\ hl_cap (hs_held h) < 2 ^ 24.

Definition l2_mid (L : layout) (A : astate) (mem : word -> option byte) (t : Z) (e : rentry) (p : hsrc * nat)
    (ks : list (list Z)) : Prop :=
  let h := fst p in
  src_at B L A mem (G_S + SRC_SIZE * Z.of_nat (snd p)) h /\ (snd p < 4)%nat /\
  hs_fd h = re_fd e /\
  (re_eof e = 0 -> re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h))) /\
  hl_recs (hs_expected h) = [] /\
  NoDup (texts (hs_held h)) /\ NoDup ks /\ same_set ks (texts (hs_held h)) /\
  keys_texts (re_keys e) = snd (gei (bzs P) ks) /\
  hl_n (hs_held h) < 2 ^ 26 /\
  hl_n (hs_pending h) <= t /\ hl_cap (hs_pending h) <= Z.max 8 (2 * t) /\
  Z.of_nat (length (pending_stream h)) <= WRITE_MAX * t /\
  ecap_ok (hl_cap (hs_expected h)) /\ hl_cap (hs_held h) < 2 ^ 24.

Definition l2_pair (s : l2st) (L : layout) (A : astate) (mem : word -> option byte) (t : Z) (e : rentry)
    (p : hsrc * nat) (Ls ks : list (list Z)) : Prop :=
  match s with
  | L2Pre => l2_pre L A mem t e p Ls ks
  | L2Mid => l2_mid L A mem t e p ks
  | L2Post => pair_ok (rc := rc) B L A mem t e p
  end.

Definition l2_rel (st : nat -> l2st) (L : layout) (A : astate) (mem : word -> option byte) (t nfd G OUT : Z)
    (es : list rentry) (hj : list (hsrc * nat)) (Lss kss : list (list (list Z))) : Prop :=
  (exists tail, table_at B mem G es tail) /\
  In (G, SRC_TABLE) (blocks L A) /\ fresh_block B G SRC_TABLE /\
  Forall (CF.RelayRep.entry_ok B L A mem) es /\
  NoDup (map re_fd es) /\
  Forall (fun e => FIRST_FD <= re_fd e < FIRST_FD + nfd) es /\
  length hj = length es /\
  (forall p, (p < length es)%nat ->
     l2_pair (st p) L A mem t (nth p es no_entry) (nth p hj no_hj) (nth p Lss []) (nth p kss [])) /\
  NoDup (map snd hj) /\
  (forall i, (i < 4)%nat -> slot_open hj i = false ->
     rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) /\
  NoDup (target_addrs G OUT es hj).

End L2P.

Lemma l2_ta : forall G OUT es hj1 h s hj2,
  target_addrs G OUT es (hj1 ++ (h, s) :: hj2) =
  (G :: OUT :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj1)) ++
  hs_blocks h ++ concat (map (fun p => hs_blocks (fst p)) hj2).
Proof.
  intros. unfold target_addrs. rewrite map_app, concat_app. cbn [map concat fst app]. rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma l2_nth_other : forall {X} (l1 l2 : list X) x y d q, q <> length l1 ->
  nth q (l1 ++ x :: l2) d = nth q (l1 ++ y :: l2) d.
Proof.
  intros X l1 l2 x y d q H. destruct (Nat.lt_ge_cases q (length l1)) as [L|L].
  - rewrite !app_nth1 by exact L. reflexivity.
  - rewrite !app_nth2 by exact L. destruct (q - length l1)%nat as [|n] eqn:Eq; [lia|]. reflexivity.
Qed.

Lemma l2_nth_side : forall {X} (l1 l2 : list X) x d q, (q < length (l1 ++ x :: l2))%nat -> q <> length l1 ->
  In (nth q (l1 ++ x :: l2) d) (l1 ++ l2).
Proof.
  intros X l1 l2 x d q H1 H2. rewrite length_app in H1. cbn [length] in H1.
  destruct (Nat.lt_ge_cases q (length l1)) as [L|L].
  - rewrite app_nth1 by exact L. apply in_or_app. left. apply nth_In. exact L.
  - rewrite app_nth2 by exact L. destruct (q - length l1)%nat as [|n] eqn:Eq; [lia|]. cbn [nth].
    apply in_or_app. right. apply nth_In. lia.
Qed.

Section L2T.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BW : blocks_writable B API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis SL : block_slack_present B API.
Hypothesis PL : forall a, in_globals G_reply a -> img_plain B a.
Variable P : list byte.

Lemma l2_slot_img : forall j k, (j < 4)%nat -> 0 <= k < 96 -> img_plain B (G_S + SRC_SIZE * Z.of_nat j + k).
Proof. intros j k Hj Hk. apply PL, in_G_bss. unfold G_S, SRC_SIZE. lia. Qed.

Lemma l2_pair_src : forall s L A mem t e h j Ls ks, l2_pair (rc := rc) B P s L A mem t e (h, j) Ls ks ->
  src_at B L A mem (G_S + SRC_SIZE * Z.of_nat j) h /\ (j < 4)%nat.
Proof.
  intros s L A mem t e h j Ls ks H. destruct s; cbn [l2_pair] in H.
  - unfold l2_pre in H. cbv zeta in H. cbn [fst snd] in H. destruct H as (S & J & _). exact (conj S J).
  - unfold l2_mid in H. cbv zeta in H. cbn [fst snd] in H. destruct H as (S & J & _). exact (conj S J).
  - unfold pair_ok in H. cbv zeta in H. cbn [fst snd] in H. destruct H as (S & J & _). exact (conj S J).
Qed.

Lemma l2_pair_rmid : forall s K sp Ew Fw L A mem md L' A' mem' md' t e h j Ls ks,
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid B API K sp Ew Fw L A mem md L' A' mem' md' ->
  l2_pair (rc := rc) B P s L A mem t e (h, j) Ls ks ->
  (forall k, 0 <= k < 96 -> img_plain B (G_S + SRC_SIZE * Z.of_nat j + k) /\ ~ Ew (G_S + SRC_SIZE * Z.of_nat j + k)) ->
  (forall q, In q (hs_blocks h) -> kept_block Ew Fw L A q) ->
  l2_pair (rc := rc) B P s L' A' mem' t (fresh_entry B mem' e) (h, j) Ls ks.
Proof.
  intros s K sp Ew Fw L A mem md L' A' mem' md' t e h j Ls ks HK HM R PR HL HB.
  destruct s; cbn [l2_pair] in PR |- *.
  - unfold l2_pre in PR |- *. cbv zeta in PR |- *. cbn [fst snd] in PR |- *.
    destruct PR as (S & REST).
    split; [exact (src_at_rmid B API AX BW K sp Ew Fw L A mem md L' A' mem' md' _ h SEG HK HM R S HL HB)|].
    cbn [fresh_entry re_fd re_eof re_skip re_U re_keys]. rewrite fresh_keys_texts. exact REST.
  - unfold l2_mid in PR |- *. cbv zeta in PR |- *. cbn [fst snd] in PR |- *.
    destruct PR as (S & REST).
    split; [exact (src_at_rmid B API AX BW K sp Ew Fw L A mem md L' A' mem' md' _ h SEG HK HM R S HL HB)|].
    cbn [fresh_entry re_fd re_eof re_skip re_U re_keys]. rewrite fresh_keys_texts. exact REST.
  - exact (pair_rmid B API AX BW SEG K sp Ew Fw L A mem md L' A' mem' md' t e h j HK HM R PR HL HB).
Qed.

Lemma l2_ta_pos : forall st L A mem t nfd G OUT es hj Lss kss q,
  l2_rel (rc := rc) B P st L A mem t nfd G OUT es hj Lss kss ->
  (OUT = 0 \/ exists k, 0 < k /\ In (OUT, k) (blocks L A)) ->
  In q (target_addrs G OUT es hj) -> q = 0 \/ exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros st L A mem t nfd G OUT es hj Lss kss q (_ & GIN & _ & ES & _ & _ & LH & PA & _) HO HQ.
  destruct HQ as [<-|[<-|HQ]]; [right; exists SRC_TABLE; split; [unfold SRC_TABLE, SRC_ENTRY; lia|exact GIN]|exact HO|].
  right. apply in_app_iff in HQ as [HQ|HQ].
  - apply in_concat in HQ as (l0 & Hl0 & Hq). apply in_map_iff in Hl0 as (e & <- & He).
    rewrite Forall_forall in ES. destruct (ES e He) as (_ & _ & _ & _ & _ & H6 & _ & _ & _ & BU & _ & HP & _ & _ & KS).
    unfold entry_blocks in Hq. apply in_app_iff in Hq as [Hq|Hq].
    + destruct (Z.eqb_spec (re_cap e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
      destruct BU as [(X & _)|(HC & IN & _)]; [lia|]. exists (re_cap e). split; [exact HC|exact IN].
    + apply in_app_iff in Hq as [Hq|Hq].
      * destruct (Z.eqb_spec (re_hp e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
        destruct HP as [(X & _)|(IN & _ & _ & HH & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
      * apply in_map_iff in Hq as (k & <- & Hk). rewrite Forall_forall in KS. destruct (KS k Hk) as (IN & _).
        exists (Z.of_nat (length (key_text k)) + 1). split; [lia|exact IN].
  - apply in_concat in HQ as (l0 & Hl0 & Hq). apply in_map_iff in Hl0 as (p & <- & Hp).
    destruct (In_nth _ _ no_hj Hp) as (n & Hn & En).
    rewrite LH in Hn. pose proof (PA n Hn) as X. rewrite En in X. destruct p as [h j].
    destruct (l2_pair_src _ _ _ _ _ _ h j _ _ X) as [S _].
    exact (g5_src_blocks B L A mem _ h q S Hq).
Qed.

Lemma l2_rel_step : forall (st st' : nat -> l2st) K sp Ew Ff L A mem md L' A' mem' md' t nfd G OUT es hj1 h s hj2
    h' Lss kss (lbN : list Z),
  YM05.alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid B API K sp Ew Ff L A mem md L' A' mem' md' ->
  l2_rel (rc := rc) B P st L A mem t nfd G OUT es (hj1 ++ (h, s) :: hj2) Lss kss ->
  (OUT = 0 \/ exists k, 0 < k /\ In (OUT, k) (blocks L A)) ->
  (forall q, (q < length es)%nat -> q <> length hj1 -> st' q = st q) ->
  (forall a, in_img B a -> ~ (G_S + SRC_SIZE * Z.of_nat s + 64 <= a < G_S + SRC_SIZE * Z.of_nat s + 96) -> ~ Ew a) ->
  (forall q, In q (target_addrs G OUT es (hj1 ++ (h, s) :: hj2)) -> ~ In q (hs_blocks h) ->
     kept_block Ew Ff L A q) ->
  l2_pair (rc := rc) B P (st' (length hj1)) L' A' mem' t (fresh_entry B mem' (nth (length hj1) es no_entry)) (h', s)
    (nth (length hj1) Lss []) (nth (length hj1) kss []) ->
  (forall q, In q (hs_blocks h') -> In q (hs_blocks h) \/ In q lbN) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (hs_blocks h) -> ~ In q lbN) ->
  ~ In 0 lbN ->
  l2_rel (rc := rc) B P st' L' A' mem' t nfd G OUT (map (fresh_entry B mem') es) (hj1 ++ (h', s) :: hj2) Lss kss.
Proof.
  intros st st' K sp Ew Ff L A mem md L' A' mem' md' t nfd G OUT es hj1 h s hj2 h' Lss kss lbN
    HK HM R REL HO HST HIMG KP NEWP HB1 HB2 HZ.
  pose proof REL as ((tail & TL & TC) & GIN & GFR & ES & NDF & FD & LH & PA & NDH & ZH & NDA).
  rewrite l2_ta in NDA.
  assert (KX : forall q, In q ((G :: OUT :: concat (map entry_blocks es) ++ concat (map (fun p => hs_blocks (fst p)) hj1)) ++
                               concat (map (fun p => hs_blocks (fst p)) hj2)) -> kept_block Ew Ff L A q).
  { intros q Hq. apply KP; [|exact (nodup_mid_out _ _ _ q NDA Hq)].
    rewrite l2_ta. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|right].
    apply in_app_iff. right. exact Hq. }
  assert (NIH : forall p, In p (hj1 ++ hj2) -> snd p <> s).
  { intros p Hp Eq. rewrite map_app in NDH. cbn [map] in NDH. apply hf_nodup in NDH.
    apply in_app_iff in Hp as [Hp|Hp].
    - apply (hf_nodup_disj (map snd hj1) (snd (h, s) :: map snd hj2) s NDH); [rewrite <- Eq; apply in_map; exact Hp|].
      left. reflexivity.
    - pose proof (NoDup_app_remove_l _ _ NDH) as N2. inversion N2 as [|y ys NI _].
      apply NI. cbn [snd]. rewrite <- Eq. apply in_map. exact Hp. }
  assert (SLOTNE : forall j k, (j < 4)%nat -> j <> s -> 0 <= k < 96 -> ~ Ew (G_S + SRC_SIZE * Z.of_nat j + k)).
  { intros j k Hj NE Hk. apply HIMG; [exact (proj1 (l2_slot_img j k Hj Hk))|].
    unfold G_S, SRC_SIZE. intros (X1 & X2).
    destruct (Nat.lt_ge_cases j s) as [LT|GE].
    - assert (Z.of_nat j + 1 <= Z.of_nat s) by lia. lia.
    - assert (Z.of_nat s + 1 <= Z.of_nat j) by lia. lia. }
  split.
  { exists tail. split; [rewrite length_map; exact TL|].
    rewrite fresh_entries_bytes.
    destruct (KX G ltac:(apply in_or_app; left; left; reflexivity)) as (NF & NE).
    eapply (rmid_rw_block B API BW K sp Ew Ff L A mem md L' A' mem' md' _ _ _ _ R GIN
              ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) NF TC);
      [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia |].
    intros k Hk. cbn [cells_size csize] in Hk. apply (NE _ k GIN). unfold SRC_TABLE, SRC_ENTRY. lia. }
  destruct (KX G ltac:(apply in_or_app; left; left; reflexivity)) as (NFG & NEG).
  split; [exact (proj1 (rmid_block B API BW K sp Ew Ff L A mem md L' A' mem' md' _ _ 0 R GIN
                         ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) NFG ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)
                         (NEG _ 0 GIN ltac:(unfold SRC_TABLE, SRC_ENTRY; lia))))|].
  split; [exact GFR|].
  split.
  { apply Forall_map. rewrite Forall_forall in ES |- *. intros e0 He0.
    apply (entry_rmid B API BW K sp Ew Ff L A mem md L' A' mem' md' e0 SL R (ES e0 He0)).
    intros q Hq. apply KX. apply in_app_iff. left. right. right. apply in_app_iff. left.
    apply in_concat. exists (entry_blocks e0). split; [apply in_map; exact He0|exact Hq]. }
  split; [rewrite map_map; exact NDF|].
  split; [apply Forall_map; exact FD|].
  split; [rewrite length_map, <- LH, !length_app; reflexivity|].
  split.
  { intros q Hq. rewrite length_map in Hq.
    rewrite (nth_indep (map (fresh_entry B mem') es) no_entry (fresh_entry B mem' no_entry))
      by (rewrite length_map; exact Hq).
    rewrite map_nth.
    destruct (Nat.eq_dec q (length hj1)) as [->|Hne].
    - rewrite nth_middle. exact NEWP.
    - rewrite (HST q Hq Hne).
      rewrite (l2_nth_other hj1 hj2 (h', s) (h, s) no_hj q Hne).
      pose proof (PA q Hq) as PQ.
      assert (IQ : In (nth q (hj1 ++ (h, s) :: hj2) no_hj) (hj1 ++ hj2))
        by (apply l2_nth_side; [rewrite LH; exact Hq|exact Hne]).
      destruct (nth q (hj1 ++ (h, s) :: hj2) no_hj) as [h0 j0] eqn:EQ.
      destruct (l2_pair_src _ _ _ _ _ _ _ _ _ _ PQ) as [_ Hj0].
      apply (l2_pair_rmid _ K sp Ew Ff L A mem md L' A' mem' md' _ _ h0 j0 _ _ HK HM R PQ).
      + intros k0 Hk0. split; [exact (l2_slot_img j0 k0 Hj0 Hk0)|]. apply SLOTNE; [exact Hj0| |exact Hk0].
        exact (NIH (h0, j0) IQ).
      + intros q0 Hq0. apply KX.
        apply in_app_iff in IQ as [IQ|IQ].
        * apply in_app_iff. left. right. right. apply in_app_iff. right. apply in_concat.
          exists (hs_blocks h0). split; [exact (in_map (fun p => hs_blocks (fst p)) _ _ IQ)|exact Hq0].
        * apply in_app_iff. right. apply in_concat. exists (hs_blocks h0).
          split; [exact (in_map (fun p => hs_blocks (fst p)) _ _ IQ)|exact Hq0]. }
  split; [rewrite !map_app in *; exact NDH|].
  split.
  { intros q Hq HZq.
    assert (EO : slot_open (hj1 ++ (h', s) :: hj2) q = slot_open (hj1 ++ (h, s) :: hj2) q).
    { unfold slot_open. rewrite !map_app. reflexivity. }
    rewrite EO in HZq.
    assert (QI : q <> s).
    { intros ->. unfold slot_open in HZq. rewrite map_app in HZq. cbn [map snd] in HZq.
      rewrite existsb_app in HZq. cbn [existsb] in HZq. rewrite Nat.eqb_refl in HZq.
      rewrite orb_true_r in HZq. discriminate. }
    apply (rmid_rw_img B API AX K sp Ew Ff L A mem md L' A' mem' md' _ _ (hg_img_low B SEG) HK HM R (ZH q Hq HZq)).
    intros k0 Hk0. cbn [cells_size csize] in Hk0. split; [apply l2_slot_img; [exact Hq|lia]|].
    apply SLOTNE; [exact Hq|exact QI|lia]. }
  rewrite l2_ta, fresh_entries_blocks.
  apply (nodup_swap _ _ (hs_blocks h)); [exact NDA| |].
  - apply hf_nodup. destruct (l2_pair_src _ _ _ _ _ _ _ _ _ _ NEWP) as [S' _].
    destruct S' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND'). exact ND'.
  - intros q Q1 Q2.
    destruct (HB1 q Q1) as [Q3|Q3].
    + exact (nodup_mid_out _ _ _ q NDA Q2 Q3).
    + assert (QT : In q (target_addrs G OUT es (hj1 ++ (h, s) :: hj2))).
      { rewrite l2_ta. apply in_app_iff in Q2 as [Q2|Q2]; apply in_app_iff; [left; exact Q2|right].
        apply in_app_iff. right. exact Q2. }
      assert (NP := nodup_mid_out _ _ _ q NDA Q2).
      destruct (l2_ta_pos st L A mem t nfd G OUT es _ Lss kss q REL HO QT) as [->|(k0 & Hk0 & Hin)].
      * exact (HZ Q3).
      * exact (HB2 q k0 Hin Hk0 NP Q3).
Qed.

Lemma l2_kept : forall L A mem md (Ew Ff : Z -> Prop) X W h q HA,
  aa_MR API L A mem md -> src_at B L A mem HA h ->
  (forall a, X <= a < X + W -> in_img B a) ->
  (forall a, Ew a -> (X <= a < X + W) \/
     (0 < hl_cap (hs_expected h) /\
      hl_v (hs_expected h) <= a < hl_v (hs_expected h) + 16 * hl_cap (hs_expected h)) \/
     (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h))) ->
  (forall q, Ff q -> In q (hs_blocks h)) ->
  ~ In q (hs_blocks h) -> kept_block Ew Ff L A q.
Proof.
  intros L A mem md Ew Ff X W h q HA HM S HX HE HF NQ.
  destruct S as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LH & _).
  split; [intros X1; exact (NQ (HF q X1))|].
  intros m i Hin Hi Hq. destruct (HE _ Hq) as [X1|[(C & X1)|(C & X1)]].
  - exact (hf_blk_img B API AX L A mem md q m i HM Hin Hi (HX _ X1)).
  - destruct (hf_list_v B L A mem _ _ _ LE C) as [VB VL].
    assert (NE : q <> hl_v (hs_expected h)).
    { intros ->. apply NQ. unfold hs_blocks. rewrite !in_app_iff. right. right. left. exact VL. }
    destruct (blocks_disjoint B API L A mem md q m _ _ HM Hin VB NE); lia.
  - destruct (hf_list_v B L A mem _ _ _ LH C) as [VB VL].
    assert (NE : q <> hl_v (hs_held h)).
    { intros ->. apply NQ. unfold hs_blocks. rewrite !in_app_iff. right. right. right. exact VL. }
    destruct (blocks_disjoint B API L A mem md q m _ _ HM Hin VB NE); lia.
Qed.

Lemma l2_img_keep : forall E0 K sp Ew Fw L A mem md L' A' mem' md' X W,
  image_kept (rc := rc) B E0 mem -> rmid B API K sp Ew Fw L A mem md L' A' mem' md' -> aa_MR API L A mem md ->
  YM05.alloc_ceiling <= sp - K ->
  (forall a, Ew a -> X <= a < X + W \/ (~ in_img B a /\ a < YM05.alloc_ceiling)) ->
  (forall a, X <= a < X + W ->
     in_globals G_reply a /\ writable_at (ms_segs B) mem a /\ writable_at (ms_segs B) mem' a) ->
  (forall a, sk B K sp a -> lib_scratch B SLOT_STACK (ss_regs E0) a) ->
  (forall a, lib_scratch B SLOT_STACK (ss_regs E0) a -> sk B K sp a \/ YM05.alloc_ceiling <= a < 2 ^ 64) ->
  image_kept (rc := rc) B E0 mem'.
Proof.
  intros E0 K sp Ew Fw L A mem md L' A' mem' md' X W (I1 & I2 & I3 & I4) R HM HK HE HX SKL LSK.
  pose proof R as (M' & _ & _ & _ & _ & _ & _ & _ & _ & _ & BY & _ & SC).
  pose proof (aa_laws API) as LAWS.
  assert (HI : forall x, in_img B x -> 0 <= x < YM05.alloc_ceiling) by exact (hg_img_low B SEG).
  assert (FR : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ sk B K sp a -> ~ Ew a ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha NS NE. apply BY; [left; exact Ha| | |exact NS|exact NE].
    - intro Y. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HM Y). lia.
    - intro Y. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a M' Y). lia. }
  assert (NEH : forall a, YM05.alloc_ceiling <= a -> ~ Ew a).
  { intros a Ha Y. destruct (HE a Y) as [Y1|(_ & Y2)]; [|lia].
    pose proof (HI a (proj1 (PL a (proj1 (HX a Y1))))). lia. }
  split.
  { intros a Ha H1 H2 H3 H4.
    assert (NE : ~ Ew a).
    { intros Y. destruct (HE a Y) as [Y1|(Y2 & _)]; [exact (H4 (proj1 (HX a Y1)))|exact (Y2 Ha)]. }
    destruct (rmid_img B API AX K sp Ew Fw L A mem md L' A' mem' md' a HI HK HM R
                ltac:(split; [exact Ha|split; [exact H1|split; [exact H2|exact H3]]]) NE) as [E1 W1].
    destruct (I1 a Ha H1 H2 H3 H4) as [E2 W2]. split; [congruence|tauto]. }
  split.
  { intros a Ha. pose proof (I2 a Ha) as W2.
    assert (D : X <= a < X + W \/ ~ (X <= a < X + W)) by lia.
    destruct D as [D|D].
    - destruct (HX a D) as (_ & W3 & W4). tauto.
    - assert (NE : ~ Ew a).
      { intros Y. destruct (HE a Y) as [Y1|(Y2 & _)]; [exact (D Y1)|exact (Y2 (proj1 (PL a Ha)))]. }
      destruct (rmid_img B API AX K sp Ew Fw L A mem md L' A' mem' md' a HI HK HM R (PL a Ha) NE) as [_ W1].
      tauto. }
  split.
  { intros a Ha HN. destruct (I3 a Ha HN) as [E2 W2].
    destruct (FR a Ha ltac:(intros Y; exact (HN (SKL a Y))) (NEH a ltac:(lia))) as [E1 W1].
    split; [congruence|tauto]. }
  intros a Ha. assert (D : sk B K sp a \/ ~ sk B K sp a) by (unfold sk; lia).
  destruct D as [D|D]; [exact (SC a D)|].
  destruct (LSK a Ha) as [Y|Y]; [exact (False_ind _ (D Y))|].
  destruct (FR a Y D (NEH a ltac:(lia))) as [_ W1]. apply W1. exact (I4 a Ha).
Qed.

Lemma l2_pair_fd : forall s L A mem t e h j Ls ks, l2_pair (rc := rc) B P s L A mem t e (h, j) Ls ks ->
  hs_fd h = re_fd e.
Proof.
  intros s L A mem t e h j Ls ks H. destruct s; cbn [l2_pair] in H.
  - unfold l2_pre in H. cbv zeta in H. cbn [fst snd] in H. destruct H as (_ & _ & X & _). exact X.
  - unfold l2_mid in H. cbv zeta in H. cbn [fst snd] in H. destruct H as (_ & _ & X & _). exact X.
  - unfold pair_ok in H. cbv zeta in H. cbn [fst snd] in H. destruct H as (_ & _ & X & _). exact X.
Qed.

End L2T.

Lemma l2_cost_swap : forall es hj1 hj2 x y, (forall e, pair_cost e x = pair_cost e y) ->
  slot_cost es (hj1 ++ x :: hj2) = slot_cost es (hj1 ++ y :: hj2).
Proof.
  intros es hj1. revert es. induction hj1 as [|p hj1 IH]; intros es hj2 x y H.
  - destruct es as [|e es]; [reflexivity|]. cbn [app]. rewrite !slot_cost_cons, H. reflexivity.
  - destruct es as [|e es]; [reflexivity|]. cbn [app]. rewrite !slot_cost_cons, (IH es hj2 x y H). reflexivity.
Qed.

Lemma l2_zero_cells : forall segs m a, rw_cells segs m a [CB 96%nat (nulbytes 96)] ->
  rw_cells segs m a [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros segs m a H.
  assert (H2 : rw_cells segs m a ([CB 8 (nulbytes 8)] ++ [CB 88 (nulbytes 88)])).
  { apply (rw_cells_retype segs m a _ _ H); [cbn; split; [reflexivity|split; [reflexivity|exact I]]|reflexivity]. }
  destruct (hg_cut _ _ _ _ _ H2) as [H3 _].
  apply (rw_cells_retype segs m a _ _ H3); [cbn; tauto|vm_compute; reflexivity].
Qed.

Lemma l2_seg_nth : forall P Lss kss n j, (j < n)%nat ->
  nth j (l2_segs P Lss kss n) [] = gone_segment (bzs P) (nth j Lss []) (nth j kss []).
Proof.
  intros P Lss kss n j H. unfold l2_segs.
  set (f := fun p : nat => gone_segment (bzs P) (nth p Lss []) (nth p kss [])).
  rewrite (nth_indep (map f (seq 0 n)) [] (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma l2_seg_len : forall P Lss kss n, length (l2_segs P Lss kss n) = n.
Proof. intros. unfold l2_segs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma l2_ends : forall (P : list byte) (E : list (list Z)) (rs : list (Z * list byte)) (d : list byte) (z : list Z),
  NoDup E -> NoDup (rtexts rs) ->
  (forall y, In y E <-> In y (rtexts rs) /\ has_prefix (bzs P) y = true) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) rs ->
  bzs d = concat (map (fun x => x ++ END5Z) E) ++ z ->
  exists rs' ds, ends_run P rs d (want_of P rs) =
    Some (rs', ds, Z.of_nat (length (concat (map (fun x => x ++ END5Z) E)))) /\
    (forall y, In y (rtexts rs') <-> In y (rtexts rs) /\ has_prefix (bzs P) y = false).
Proof.
  intros P E. induction E as [|x E IH]; intros rs d z NE NR HS NZ HD.
  - assert (W : want_of P rs = 0%nat).
    { apply g5_want_zero. intros r Hr. destruct (prefixb P (snd r)) eqn:Pr; [|reflexivity]. exfalso.
      apply (proj2 (HS (bzs (snd r)))). split; [|rewrite <- g5_prefixb; exact Pr].
      unfold rtexts. apply (in_map (fun r => bzs (snd r))). exact Hr. }
    rewrite W. exists rs, []. split; [reflexivity|].
    intros y. split; [|tauto]. intros Hy. split; [exact Hy|].
    destruct (has_prefix (bzs P) y) eqn:Hp; [|reflexivity]. exfalso. exact (proj2 (HS y) (conj Hy Hp)).
  - apply NoDup_ListNoDup in NE. inversion NE as [|? ? NX NE']; subst. apply NoDup_ListNoDup in NE'.
    destruct (proj1 (HS x) (or_introl eq_refl)) as [Ix Px].
    destruct (In_nth (rtexts rs) x [] Ix) as (i0 & Li0 & Ni0).
    assert (Li0' : (i0 < length rs)%nat) by (unfold rtexts in Li0; rewrite length_map in Li0; exact Li0).
    rewrite (nth_rtexts rs i0 Li0') in Ni0.
    set (xb := snd (nth i0 rs (0, []))) in *.
    assert (Ixb : In (bzs xb) (rtexts rs)) by (rewrite Ni0; exact Ix).
    destruct (find_text_some xb rs Ixb) as (i & Fi & Li & Ni).
    assert (NZx : ~ In (Z_to_bv 8 0) xb).
    { rewrite Forall_forall in NZ. apply NZ. apply nth_In. exact Li0'. }
    assert (Pxb : prefixb P xb = true) by (rewrite g5_prefixb, Ni0; exact Px).
    assert (Pi : prefixb P (snd (nth i rs (0, []))) = true)
      by (rewrite g5_prefixb, Ni; rewrite <- g5_prefixb; exact Pxb).
    assert (HD' : bzs d = bzs ((xb ++ END4) ++ [Z_to_bv 8 0]) ++ (concat (map (fun x => x ++ END5Z) E) ++ z)).
    { rewrite HD. cbn [map concat]. rewrite !bzs_app, g5_end4_bzs, bzs_zero, Ni0. unfold END5Z.
      rewrite <- !app_assoc. reflexivity. }
    destruct (g5_bzs_split _ _ _ HD') as (d' & -> & HD2).
    rewrite <- (app_assoc (xb ++ END4) [Z_to_bv 8 0] d'). cbn [app].
    rewrite (g5_want_drop P rs i Li), Pi. cbn [Nat.add ends_run].
    assert (NZX : ~ In (Z_to_bv 8 0) (xb ++ END4)).
    { rewrite in_app_iff. intros [X | X]; [exact (NZx X) | exact (g5_end4_nz X)]. }
    rewrite (split_nul_app _ _ NZX). cbv beta iota zeta.
    destruct (g5_end_ok P xb Pxb) as [C1 C2]. rewrite C1, C2, Fi. cbv beta iota zeta.
    assert (LRi : (i < length (rtexts rs))%nat) by (unfold rtexts; rewrite length_map; exact Li).
    assert (NT : nth i (rtexts rs) [] = x) by (rewrite (nth_rtexts rs i Li), Ni; exact Ni0).
    assert (NR' : NoDup (rtexts (drop_nth i rs))).
    { apply NoDup_ListNoDup. rewrite rtexts_drop. pose proof (proj1 (NoDup_ListNoDup _) NR) as NR0.
      rewrite (split_at (rtexts rs) i [] LRi) in NR0. apply NoDup_remove_1 in NR0. exact NR0. }
    assert (HS' : forall y, In y E <-> In y (rtexts (drop_nth i rs)) /\ has_prefix (bzs P) y = true).
    { intros y. rewrite rtexts_drop, (in_drop_split (rtexts rs) i [] y NR LRi), NT. split.
      - intros HY. destruct (proj1 (HS y) (or_intror HY)) as [H1 H2].
        split; [split; [exact H1|] | exact H2]. intros ->. exact (NX HY).
      - intros [[H1 H2] H3]. destruct (proj2 (HS y) (conj H1 H3)) as [HY | HY]; [congruence | exact HY]. }
    assert (NZ' : Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (drop_nth i rs)).
    { rewrite (split_at rs i (0, []) Li) in NZ. apply Forall_app in NZ. destruct NZ as [N1 N2].
      inversion N2 as [|? ? _ N3]; subst. unfold drop_nth. apply Forall_app. split; assumption. }
    destruct (IH (drop_nth i rs) d' z NE' NR' HS' NZ' HD2) as (rs' & ds & ER & CH). rewrite ER.
    exists rs', (nth i rs (0, []) :: ds). split.
    + f_equal. f_equal. f_equal.
      cbn [map concat]. rewrite !length_app. unfold END5Z. change (length END4) with 4%nat.
      assert (LX : length xb = length x) by (rewrite <- Ni0, bzs_length; reflexivity).
      cbn [length]. rewrite LX. lia.
    + intros y. rewrite CH, rtexts_drop, (in_drop_split (rtexts rs) i [] y NR LRi), NT. split.
      * intros [[H1 _] H3]. split; [exact H1|exact H3].
      * intros [H1 H3]. split; [split; [exact H1|]|exact H3]. intros ->. rewrite Px in H3. discriminate.
Qed.

Lemma l2_stream : forall gn (segsz : list (list Z)) (ob : list byte) (nout : word) j pre Ls ks (E : hlist),
  (gn = 0 -> bzs ob = concat segsz) ->
  bv_unsigned nout = (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) ->
  (j < length segsz)%nat -> nth j segsz [] = gone_segment pre Ls ks ->
  map snd (hl_recs E) = map (map (Z_to_bv 8)) Ls -> Forall zrange Ls ->
  0 <= g5_at gn segsz j <= bv_unsigned nout /\
  (gn = 0 -> exists rest, skipn (Z.to_nat (g5_at gn segsz j)) ob = bstream E ++ rest).
Proof.
  intros gn segsz ob nout j pre Ls ks E HB HN HJ HS HM HR.
  rewrite HN. split; [apply g5_at_le|]. intros Hg.
  destruct (g5_bstream E Ls HM HR) as [BE LBE].
  subst gn. unfold g5_at. rewrite Z.eqb_refl, Nat2Z.id.
  assert (X : bzs (skipn (length (concat (firstn j segsz))) ob) =
              bzs (bstream E) ++ (concat (map (fun x => x ++ END5Z) (fst (gei pre ks))) ++
                                  concat (skipn (S j) segsz))).
  { rewrite (g5_skip_at segsz j ob HJ (HB eq_refl)), HS, BE. unfold gone_segment. rewrite <- app_assoc.
    reflexivity. }
  destruct (g5_bzs_split _ _ _ X) as (d' & E1 & _). exists d'. exact E1.
Qed.

Lemma l2_ends_pre : forall gn (segsz : list (list Z)) (ob : list byte) (nout : word) j (P : list byte) Ls ks
    (H : hlist),
  (gn = 0 -> bzs ob = concat segsz) ->
  bv_unsigned nout = (if gn =? 0 then Z.of_nat (length (concat segsz)) else 0) ->
  (j < length segsz)%nat -> nth j segsz [] = gone_segment (bzs P) Ls ks ->
  NoDup ks -> NoDup (texts H) -> same_set ks (texts H) ->
  Forall (fun r => ~ In (Z_to_bv 8 0) (snd r)) (hl_recs H) ->
  0 <= g5_at gn segsz j + (if gn =? 0 then Z.of_nat (length (with_nul Ls)) else 0) <= bv_unsigned nout /\
  (gn = 0 -> exists rs' ds,
     ends_run P (hl_recs H)
       (skipn (Z.to_nat (g5_at gn segsz j + (if gn =? 0 then Z.of_nat (length (with_nul Ls)) else 0))) ob)
       (want_of P (hl_recs H)) =
       Some (rs', ds, Z.of_nat (length (concat (map (fun x => x ++ END5Z) (fst (gei (bzs P) ks)))))) /\
     (forall y, In y (rtexts rs') <-> In y (rtexts (hl_recs H)) /\ has_prefix (bzs P) y = false)).
Proof.
  intros gn segsz ob nout j P Ls ks H HB HN HJ HS NK NH SS NZ.
  rewrite HN. destruct (Z.eqb_spec gn 0) as [Hg|Hg].
  - subst gn. unfold g5_at. rewrite Z.eqb_refl.
    pose proof (g5_nth_le segsz j HJ) as NL. rewrite HS in NL. unfold gone_segment in NL. rewrite length_app in NL.
    split; [lia|]. intros _.
    assert (X : bzs (skipn (Z.to_nat (Z.of_nat (length (concat (firstn j segsz))) +
                                      Z.of_nat (length (with_nul Ls)))) ob) =
                concat (map (fun x => x ++ END5Z) (fst (gei (bzs P) ks))) ++ concat (skipn (S j) segsz)).
    { apply (g5_skip_in segsz j ob (with_nul Ls)); [exact HJ | exact (HB eq_refl) | exact HS | reflexivity]. }
    pose proof (gei_ok (bzs P) ks (proj1 (NoDup_ListNoDup _) NK)) as G.
    destruct (gei (bzs P) ks) as [E0 H0]. cbn [fst] in X |- *. destruct G as (NE & _ & _ & SE & _).
    apply (l2_ends P E0 (hl_recs H) _ (concat (skipn (S j) segsz)) (proj2 (NoDup_ListNoDup _) NE) NH);
      [|exact NZ|exact X].
    intros y. rewrite (SE y), filter_In, (SS y). reflexivity.
  - unfold g5_at. rewrite (proj2 (Z.eqb_neq gn 0) Hg). split; [lia|]. intros X. contradiction.
Qed.

Lemma l2_at_step : forall gn segsz j pre Ls ks c,
  (j < length segsz)%nat -> nth j segsz [] = gone_segment pre Ls ks ->
  (gn <> 0 -> c = 0) ->
  (gn = 0 -> c = Z.of_nat (length (concat (map (fun x => x ++ END5Z) (fst (gei pre ks)))))) ->
  g5_at gn segsz j + (if gn =? 0 then Z.of_nat (length (with_nul Ls)) else 0) + c = g5_at gn segsz (S j).
Proof.
  intros gn segsz j pre Ls ks c HJ HS C1 C0.
  destruct (Z.eqb_spec gn 0) as [Hg|Hg].
  - subst gn. rewrite (C0 eq_refl), (g5_at_step 0 segsz j HJ), Z.eqb_refl, HS.
    unfold gone_segment. rewrite length_app. lia.
  - rewrite (C1 Hg). unfold g5_at. rewrite (proj2 (Z.eqb_neq gn 0) Hg). lia.
Qed.

Lemma l2_sfilter_in : forall (f : Z * list byte -> bool) (l : list (Z * list byte)) x,
  In x (filter f l) <-> In x l /\ f x = true.
Proof.
  intros f l x. induction l as [|a l IH]; cbn; [tauto|].
  match goal with |- context [if ?b then _ else _] => destruct b as [D|D] end.
  - cbn. rewrite IH. split.
    + intros [<-|[Hx Hf]]; [split; [left; reflexivity|]|split; [right; exact Hx|exact Hf]].
      destruct (f a); [reflexivity|first [contradiction|discriminate]].
    + intros [[<-|Hx] Hf]; [left; reflexivity|right; split; [exact Hx|exact Hf]].
  - rewrite IH. split.
    + intros [Hx Hf]. split; [right; exact Hx|exact Hf].
    + intros [[<-|Hx] Hf]; [|split; [exact Hx|exact Hf]]. exfalso. apply D. rewrite Hf.
      first [exact I|reflexivity].
Qed.

Lemma l2_held_after : forall gn (P : list byte) ks (H H' : hlist) (ds : list (Z * list byte)) c d,
  NoDup ks -> same_set ks (texts H) ->
  ((gn <> 0 /\ hl_recs H' = filter (fun r => negb (prefixb P (snd r))) (hl_recs H) /\
    ds = filter (fun r => prefixb P (snd r)) (hl_recs H) /\ c = 0) \/
   (gn = 0 /\ ends_run P (hl_recs H) d (want_of P (hl_recs H)) = Some (hl_recs H', ds, c))) ->
  (gn = 0 -> exists rs' ds' c', ends_run P (hl_recs H) d (want_of P (hl_recs H)) = Some (rs', ds', c') /\
     (forall y, In y (rtexts rs') <-> In y (rtexts (hl_recs H)) /\ has_prefix (bzs P) y = false)) ->
  same_set (snd (gei (bzs P) ks)) (texts H') /\ (forall r, In r (hl_recs H) -> In r (hl_recs H') \/ In r ds) /\
  incl (hl_recs H') (hl_recs H).
Proof.
  intros gn P ks H H' ds c d NK SS CASE EX.
  assert (CH : forall y, In y (texts H') <-> In y (texts H) /\ has_prefix (bzs P) y = false).
  { destruct CASE as [(Hg & R' & _ & _)|(Hg & ER)].
    - intros y. unfold texts. rewrite R'. split.
      + intros Y. apply in_map_iff in Y as (r & <- & Hr). apply l2_sfilter_in in Hr as [Hr Hf].
        split; [apply (in_map (fun r => bzs (snd r))); exact Hr|].
        rewrite <- g5_prefixb. destruct (prefixb P (snd r)); [discriminate|reflexivity].
      + intros [Y Hp]. apply in_map_iff in Y as (r & <- & Hr). apply (in_map (fun r => bzs (snd r))).
        apply l2_sfilter_in. split; [exact Hr|]. rewrite <- g5_prefixb in Hp. rewrite Hp. reflexivity.
    - destruct (EX Hg) as (rs' & ds' & c' & ER' & CH'). rewrite ER in ER'. injection ER' as E1 _ _.
      intros y. unfold texts. rewrite E1. exact (CH' y). }
  split.
  { pose proof (gei_ok (bzs P) ks (proj1 (NoDup_ListNoDup _) NK)) as G.
    destruct (gei (bzs P) ks) as [E0 H0]. cbn [snd]. destruct G as (_ & _ & _ & _ & SH).
    intros y. rewrite (SH y), filter_In, CH, (SS y).
    destruct (has_prefix (bzs P) y); cbn; split; intros [X1 X2]; (split; [exact X1|]); first [discriminate|reflexivity]. }
  destruct CASE as [(Hg & R' & D' & _)|(Hg & ER)].
  - split.
    + intros r Hr. rewrite R', D'. destruct (prefixb P (snd r)) eqn:Pr.
      * right. apply l2_sfilter_in. split; [exact Hr|exact Pr].
      * left. apply l2_sfilter_in. split; [exact Hr|]. rewrite Pr. reflexivity.
    + rewrite R'. apply g5_sfilter_incl.
  - destruct (ends_run_len _ _ _ _ _ _ _ ER) as [_ IN]. split.
    + intros r Hr. exact (proj1 (IN r) Hr).
    + intros r Hr. apply IN. left. exact Hr.
Qed.

Lemma l2_rw1 : forall segs m a x, rw_cells segs m a [C1 x] -> bytes_at segs m a [x].
Proof. intros segs m a x [[_ H] _]. cbn [cells_bytes cbytes app] in H. exact H. Qed.

Lemma l2_outv : forall segs m a b c d, rw_cells segs m G_OUTV [C8 a; C8 b; C8 c; C8 d] ->
  bytes_at segs m 0x318e0 (le8 b) /\ bytes_at segs m 0x318f0 (le8 d).
Proof.
  intros segs m a b c d [[_ BB] _]. cbn [cells_bytes cbytes] in BB.
  apply bytes_at_app in BB as [_ BB]. rewrite length_le8 in BB.
  apply bytes_at_app in BB as [BB1 BB]. rewrite length_le8 in BB.
  apply bytes_at_app in BB as [_ BB]. rewrite length_le8 in BB.
  apply bytes_at_app in BB as [BB2 _].
  assert (E1 : G_OUTV + Z.of_nat 8 = 0x318e0) by (unfold G_OUTV; reflexivity).
  assert (E2 : G_OUTV + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 = 0x318f0) by (unfold G_OUTV; reflexivity).
  rewrite E1 in BB1. rewrite E2 in BB2. split; assumption.
Qed.

Lemma l2_perm4 : forall (a b c d : list Z), Permutation (a ++ (b ++ c) ++ d) (c ++ (a ++ b ++ d)).
Proof. intros a b c d. apply (Permutation_count_occ Z.eq_dec). intros x. rewrite !count_occ_app. lia. Qed.

Lemma l2_nc_mid : forall G OUT es hj1 h s hj2,
  rv_nc (view_of G OUT es (hj1 ++ (h, s) :: hj2)) =
  (G :: OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj1)) ++
  src_nc h ++ concat (map (fun p => src_nc (fst p)) hj2).
Proof.
  intros. unfold view_of. cbn [rv_nc]. rewrite map_app, concat_app. cbn [map concat fst app].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma l2_ent_nc_len : forall es, (length (concat (map entry_nc es)) <= 2 * length es)%nat.
Proof.
  induction es as [|e es IH]; [cbn; lia|]. cbn [map concat length]. rewrite length_app.
  assert (H : (length (entry_nc e) <= 2)%nat).
  { unfold entry_nc. rewrite length_app. destruct (re_cap e =? 0), (re_hp e =? 0); cbn [length]; lia. }
  lia.
Qed.

Lemma l2_src_nc_len : forall (hj : list (hsrc * nat)),
  (length (concat (map (fun p => src_nc (fst p)) hj)) <= 4 * length hj)%nat.
Proof.
  induction hj as [|p hj IH]; [cbn; lia|]. cbn [map concat length]. rewrite length_app.
  assert (H : (length (src_nc (fst p)) <= 4)%nat).
  { unfold src_nc, arr_nc. rewrite !length_app.
    destruct (hl_cap (hs_pending (fst p)) =? 0), (hl_cap (hs_expected (fst p)) =? 0), (hl_cap (hs_held (fst p)) =? 0);
      cbn [length]; lia. }
  lia.
Qed.

Lemma l2_nc_len : forall G OUT es hj,
  (length (rv_nc (view_of G OUT es hj)) <= 2 + 2 * length es + 4 * length hj)%nat.
Proof.
  intros. unfold view_of. cbn [rv_nc length]. rewrite length_app.
  pose proof (l2_ent_nc_len es). pose proof (l2_src_nc_len hj). lia.
Qed.

Lemma l2_ent_sub : forall es q, In q (concat (map entry_nc es)) -> In q (concat (map entry_blocks es)).
Proof.
  intros es q H. apply in_concat in H as (l & Hl & Hq). apply in_map_iff in Hl as (e & <- & He).
  apply in_concat. exists (entry_blocks e). split; [apply in_map; exact He|].
  unfold entry_nc in Hq. unfold entry_blocks. rewrite !in_app_iff in *. tauto.
Qed.

Lemma l2_src_sub : forall (hj : list (hsrc * nat)) q, In q (concat (map (fun p => src_nc (fst p)) hj)) ->
  In q (concat (map (fun p => hs_blocks (fst p)) hj)).
Proof.
  intros hj q H. apply in_concat in H as (l & Hl & Hq). apply in_map_iff in Hl as (p & <- & Hp).
  apply in_concat. exists (hs_blocks (fst p)). split; [exact (in_map (fun p => hs_blocks (fst p)) _ _ Hp)|].
  unfold src_nc, arr_nc in Hq. unfold hs_blocks, list_blocks. rewrite !in_app_iff in *. tauto.
Qed.

Lemma l2_src_perm : forall h, Permutation (hs_blocks h)
  ((arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_expected h)) ++
   (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)) ++ map fst (hl_recs (hs_pending h))).
Proof.
  intros h. apply (Permutation_count_occ Z.eq_dec). intros x. unfold hs_blocks, list_blocks, arr_nc.
  rewrite !count_occ_app. lia.
Qed.

Lemma l2_out_side : forall G OUT es hj1 h hj2 q,
  NoDup (target_addrs G OUT es (hj1 ++ (h, 0%nat) :: hj2)) ->
  In q ((G :: OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj1)) ++
        concat (map (fun p => src_nc (fst p)) hj2)) ->
  ~ In q (hs_blocks h).
Proof.
  intros G OUT es hj1 h hj2 q ND Hq. rewrite l2_ta in ND. apply (nodup_mid_out _ _ _ q ND).
  rewrite !in_app_iff in Hq |- *. destruct Hq as [[<-|[<-|Hq]]|Hq].
  - left. left. reflexivity.
  - left. right. left. reflexivity.
  - left. right. right. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff;
      [left; exact (l2_ent_sub _ _ Hq)|right; exact (l2_src_sub _ _ Hq)].
  - right. exact (l2_src_sub _ _ Hq).
Qed.

Lemma l2_ta_slot : forall G OUT es hj1 h s hj2,
  target_addrs G OUT es (hj1 ++ (h, s) :: hj2) = target_addrs G OUT es (hj1 ++ (h, 0%nat) :: hj2).
Proof. intros. rewrite !l2_ta. reflexivity. Qed.

Lemma l2_nc_out : forall G OUT es hj1 h s hj2 q,
  NoDup (target_addrs G OUT es (hj1 ++ (h, s) :: hj2)) ->
  In q (rv_nc (view_of G OUT es (hj1 ++ (h, s) :: hj2))) ->
  ~ In q (map fst (hl_recs (hs_expected h))) /\ ~ In q (map fst (hl_recs (hs_held h))).
Proof.
  intros G OUT es hj1 h s hj2 q ND Hq. rewrite l2_ta_slot in ND. rewrite l2_nc_mid in Hq.
  assert (HB : forall l, (forall x, In x l -> In x (hs_blocks h)) -> ~ In q l \/ In q (hs_blocks h)).
  { intros l Hl. destruct (in_dec Z.eq_dec q l) as [I|I]; [right; exact (Hl q I)|left; exact I]. }
  apply in_app_iff in Hq as [Hq|Hq]; [|apply in_app_iff in Hq as [Hq|Hq]].
  - pose proof (l2_out_side G OUT es hj1 h hj2 q ND ltac:(apply in_app_iff; left; exact Hq)) as NI.
    split; intros X; apply NI; unfold hs_blocks, list_blocks; rewrite !in_app_iff; tauto.
  - rewrite l2_ta in ND. apply hf_nodup in ND.
    pose proof (Permutation_NoDup (l2_src_perm h) (NoDup_app_remove_r _ _ (NoDup_app_remove_l _ _ ND))) as N3.
    unfold src_nc in Hq. rewrite !in_app_iff in Hq.
    split; intros X.
    + destruct Hq as [Hq|[Hq|[Hq|Hq]]].
      * apply (hf_nodup_disj _ _ q N3); [rewrite !in_app_iff; tauto|rewrite !in_app_iff; tauto].
      * apply (hf_nodup_disj _ _ q N3); [rewrite !in_app_iff; tauto|rewrite !in_app_iff; tauto].
      * apply (hf_nodup_disj _ _ q N3); [rewrite !in_app_iff; tauto|rewrite !in_app_iff; tauto].
      * assert (NDB : List.NoDup (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)))
          by exact (NoDup_app_remove_r _ _ (NoDup_app_remove_l _ _ N3)).
        apply (hf_nodup_disj _ _ q NDB X). unfold list_blocks. apply in_app_iff. left. exact Hq.
    + destruct Hq as [Hq|[Hq|[Hq|Hq]]].
      * apply (hf_nodup_disj _ _ q N3); [rewrite !in_app_iff; tauto|unfold list_blocks; rewrite !in_app_iff; tauto].
      * apply (hf_nodup_disj _ _ q N3); [rewrite !in_app_iff; tauto|unfold list_blocks; rewrite !in_app_iff; tauto].
      * apply (hf_nodup_disj _ _ q N3); [rewrite !in_app_iff; tauto|unfold list_blocks; rewrite !in_app_iff; tauto].
      * assert (ND2 : List.NoDup (list_blocks (hs_held h))).
        { apply (NoDup_app_remove_l (map fst (hl_recs (hs_expected h)))).
          apply (NoDup_app_remove_r _ (map fst (hl_recs (hs_pending h)))).
          exact (NoDup_app_remove_l _ _ N3). }
        unfold list_blocks in ND2. exact (hf_nodup_disj _ _ q ND2 Hq X).
  - pose proof (l2_out_side G OUT es hj1 h hj2 q ND ltac:(apply in_app_iff; right; exact Hq)) as NI.
    split; intros X; apply NI; unfold hs_blocks, list_blocks; rewrite !in_app_iff; tauto.
Qed.

Definition l2_R (G OUT : Z) (es : list rentry) (hj1 : list (hsrc * nat)) (h : hsrc) (hj2 : list (hsrc * nat))
    : list Z :=
  (G :: OUT :: concat (map entry_nc es) ++ concat (map (fun p => src_nc (fst p)) hj1)) ++
  (arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_expected h)) ++
  concat (map (fun p => src_nc (fst p)) hj2).

Lemma l2_R_perm : forall G OUT es hj1 h s hj2,
  Permutation (rv_nc (view_of G OUT es (hj1 ++ (h, s) :: hj2))) (arr_nc (hs_held h) ++ l2_R G OUT es hj1 h hj2).
Proof.
  intros. rewrite l2_nc_mid. unfold l2_R.
  replace (src_nc h) with ((arr_nc (hs_pending h) ++ [hs_partial h] ++ arr_nc (hs_expected h)) ++ arr_nc (hs_held h))
    by (unfold src_nc; rewrite <- !app_assoc; reflexivity).
  apply l2_perm4.
Qed.

Lemma l2_R_eq : forall (B : malloc_syms) mem G OUT es hj1 h h' hj2,
  arr_nc (hs_pending h') = arr_nc (hs_pending h) -> hs_partial h' = hs_partial h ->
  arr_nc (hs_expected h') = arr_nc (hs_expected h) ->
  l2_R G OUT (map (fresh_entry B mem) es) hj1 h' hj2 = l2_R G OUT es hj1 h hj2.
Proof.
  intros B mem G OUT es hj1 h h' hj2 E1 E2 E3. unfold l2_R. rewrite E1, E2, E3.
  replace (map entry_nc (map (fresh_entry B mem) es)) with (map entry_nc es); [reflexivity|].
  rewrite map_map. apply map_ext. intros e. reflexivity.
Qed.

Lemma l2_R_out : forall G OUT es hj1 h s hj2 q,
  NoDup (target_addrs G OUT es (hj1 ++ (h, s) :: hj2)) -> In q (l2_R G OUT es hj1 h hj2) ->
  ~ In q (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)).
Proof.
  assert (l2_blk_in : forall h q, In q (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)) ->
    In q (hs_blocks h)).
  { clear. intros h q X. unfold hs_blocks. apply in_app_iff in X as [X|X].
    - apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold list_blocks.
      apply in_app_iff. right. exact X.
    - apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  intros G OUT es hj1 h s hj2 q ND Hq. rewrite l2_ta_slot in ND. unfold l2_R in Hq.
  apply in_app_iff in Hq as [Hq|Hq]; [|apply in_app_iff in Hq as [Hq|Hq]].
  - pose proof (l2_out_side G OUT es hj1 h hj2 q ND ltac:(apply in_app_iff; left; exact Hq)) as NI.
    intros X. apply NI. exact (l2_blk_in h q X).
  - rewrite l2_ta in ND. apply hf_nodup in ND.
    pose proof (Permutation_NoDup (l2_src_perm h) (NoDup_app_remove_r _ _ (NoDup_app_remove_l _ _ ND))) as N3.
    intros X. apply (hf_nodup_disj _ _ q N3 Hq). apply in_app_iff. left. exact X.
  - pose proof (l2_out_side G OUT es hj1 h hj2 q ND ltac:(apply in_app_iff; right; exact Hq)) as NI.
    intros X. apply NI. exact (l2_blk_in h q X).
Qed.

Lemma l2_q_same : forall L A L' A' q, List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  (forall m, In (q, m) (blocks L A) <-> In (q, m) (blocks L' A')) ->
  nc_sz L' A' q = nc_sz L A q /\ forall c, nc_has L' A' c q = nc_has L A c q.
Proof.
  intros L A L' A' q N1 N2 HQ. split.
  - destruct (in_dec Z.eq_dec q (map fst (blocks L A))) as [I|I].
    + apply in_map_iff in I as ((x & m) & Ex & Hx). cbn [fst] in Ex. subst x.
      rewrite (nw_sz_at L A q m N1 Hx), (nw_sz_at L' A' q m N2 (proj1 (HQ m) Hx)). reflexivity.
    + assert (N : forall m, ~ In (q, m) (blocks L A)) by (intros m X; apply I; exact (in_map fst _ _ X)).
      rewrite (nw_sz_none L A q N), (nw_sz_none L' A' q (fun m X => N m (proj2 (HQ m) X))). reflexivity.
  - intros c. unfold nc_has. apply Bool.eq_iff_eq_true. rewrite !existsb_exists. split.
    + intros ((x & m) & Ht & Hc). exists (x, m). split; [|exact Hc].
      cbn [fst snd] in Hc. apply andb_prop in Hc as [Hx _]. apply Z.eqb_eq in Hx. subst x. exact (proj2 (HQ m) Ht).
    + intros ((x & m) & Ht & Hc). exists (x, m). split; [|exact Hc].
      cbn [fst snd] in Hc. apply andb_prop in Hc as [Hx _]. apply Z.eqb_eq in Hx. subst x. exact (proj1 (HQ m) Ht).
Qed.

Lemma l2_has_at : forall L A q n c, List.NoDup (map fst (blocks L A)) -> In (q, n) (blocks L A) ->
  (if nc_has L A c q then 1 else 0) = one_if c (band n).
Proof.
  intros L A q n c ND Hin. unfold one_if.
  destruct (nc_has L A c q) eqn:EX; unfold nc_has in EX.
  - apply existsb_exists in EX as ((x & m) & Hx & Hc). cbn [fst snd] in Hc.
    apply andb_prop in Hc as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst x.
    rewrite (RelayRunF.nodup_fst_eq (blocks L A) q m n ND Hx Hin) in H2. rewrite H2, Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec c (band n)) as [Ec|Ec]; [|reflexivity]. exfalso.
    assert (T : existsb (fun t => (fst t =? q) && (band (snd t) =? c)) (blocks L A) = true).
    { apply existsb_exists. exists (q, n). split; [exact Hin|]. cbn [fst snd]. rewrite Z.eqb_refl, Ec, Z.eqb_refl.
      reflexivity. }
    congruence.
Qed.

Lemma l2_old_ptr : forall L A L' A' (Ff : Z -> Prop) p n,
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ Ff (ptr_addr L p) ->
     ptr_addr L' p = ptr_addr L p) ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ Ff (ptr_addr L p) -> In (p, n) (user_blocks A')) ->
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) ->
  WF A -> In (p, n) (user_blocks A) -> ~ Ff (ptr_addr L p) -> ptr_addr L' p = ptr_addr L p.
Proof.
  intros L A L' A' Ff p n ADDR KEEP ZERO HW Hin HF.
  pose proof (AllocBound.ub_nonneg A HW (p, n) Hin) as Hn. cbn [snd] in Hn.
  destruct (Z.eq_dec n 0) as [->|Hn0]; [exact (proj2 (ZERO p Hin))|].
  exact (ADDR p n Hin (KEEP p n Hin ltac:(lia) HF) HF).
Qed.

Lemma l2_wt_fresh : forall (B : malloc_syms) mem es,
  AllocBound.zsum nw_ent (map (fresh_entry B mem) es) = AllocBound.zsum nw_ent es.
Proof.
  intros B mem es. induction es as [|e es IH]; [reflexivity|]. cbn [map]. rewrite !AllocBound.zsum_cons, IH. f_equal.
  unfold nw_ent, re_nheld. cbn [fresh_entry re_cap re_used re_hp re_kh re_keys]. rewrite length_map. reflexivity.
Qed.

Lemma l2_wt_mid : forall es es' hj1 (h h' : hsrc) s hj2,
  AllocBound.zsum nw_ent es' = AllocBound.zsum nw_ent es -> length es' = length es ->
  nc_wt es' (hj1 ++ (h', s) :: hj2) = nc_wt es (hj1 ++ (h, s) :: hj2) - nw_src h + nw_src h'.
Proof.
  intros es es' hj1 h h' s hj2 E1 E2. unfold nc_wt. rewrite E1, E2, !AllocBound.zsum_app, !AllocBound.zsum_cons.
  rewrite !length_app. cbv beta. cbn [length fst]. lia.
Qed.

Lemma l2_src_held : forall h H', nw_src (set_held h H') = nw_src h - nw_list (hs_held h) + nw_list H'.
Proof. intros h H'. unfold nw_src, pending_stream. cbn [set_held hs_pending hs_expected hs_held hs_off]. lia. Qed.

Lemma l2_src_exp_held : forall h E' H',
  nw_src (set_exp_held h E' H') =
  nw_src h - nw_list (hs_expected h) - nw_list (hs_held h) + nw_list E' + nw_list H'.
Proof. intros h E' H'. unfold nw_src, pending_stream. cbn [set_exp_held hs_pending hs_expected hs_held hs_off]. lia. Qed.

Lemma l2_list_le : forall l l', hl_cap l' = hl_cap l -> (length (hl_recs l') <= length (hl_recs l))%nat ->
  nw_list l' <= nw_list l.
Proof. intros l l' C Ln. unfold nw_list, hl_n. rewrite C. unfold NC_PER. lia. Qed.

Section L2H.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma l2_arr_pos : forall L A mem LA l lines q, list_at B L A mem LA l lines -> In q (arr_nc l) ->
  exists m, 0 < m /\ In (q, m) (blocks L A).
Proof.
  intros L A mem LA l lines q (_ & _ & AR & _) Hq. unfold arr_nc in Hq.
  destruct (Z.eqb_spec (hl_cap l) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
  destruct AR as [(C1 & _)|(C1 & IN & _)]; [lia|]. exists (16 * hl_cap l). split; [lia|exact IN].
Qed.

Lemma l2_arr_sz : forall L A mem LA l lines, List.NoDup (map fst (blocks L A)) -> list_at B L A mem LA l lines ->
  AllocBound.zsum (nc_sz L A) (arr_nc l) = 16 * hl_cap l /\
  forall c, AllocBound.zsum (fun q => if nc_has L A c q then 1 else 0) (arr_nc l) = arr_c (hl_cap l) c.
Proof.
  intros L A mem LA l lines ND (_ & _ & AR & _). unfold arr_nc, arr_c.
  destruct (Z.eqb_spec (hl_cap l) 0) as [C0|C0].
  - rewrite C0. split; [reflexivity|intros c; reflexivity].
  - destruct AR as [(C1 & _)|(C1 & IN & _)]; [lia|].
    split.
    + rewrite AllocBound.zsum_cons, AllocBound.zsum_nil, (nw_sz_at L A _ _ ND IN). lia.
    + intros c. rewrite AllocBound.zsum_cons, AllocBound.zsum_nil. cbv beta. rewrite (l2_has_at L A _ _ c ND IN). lia.
Qed.

Lemma l2_nc_pos : forall L A mem nout cap out G es hj,
  output_at B L A mem nout cap out -> In (G, SRC_TABLE) (blocks L A) ->
  Forall (CF.RelayRep.entry_ok B L A mem) es -> (forall p, In p hj -> exists HA, src_at B L A mem HA (fst p)) ->
  forall q, In q (rv_nc (view_of G (bv_unsigned out) es hj)) -> q = 0 \/ exists m, 0 < m /\ In (q, m) (blocks L A).
Proof.
  intros L A mem nout cap out G es hj HO HG HE HS q Hq. unfold view_of in Hq. cbn [rv_nc] in Hq.
  destruct Hq as [<-|[<-|Hq]].
  - right. exists SRC_TABLE. split; [apply Z.ltb_lt; vm_compute; reflexivity|exact HG].
  - unfold output_at in HO. cbv zeta in HO. destruct HO as ((O & junk & [(_ & H0 & _)|(H1 & _ & H2 & _)]) & _).
    + left. exact H0.
    + right. exists (bv_unsigned cap). split; [exact H1|exact H2].
  - right. apply in_app_iff in Hq as [Hq|Hq].
    + apply in_concat in Hq as (l & Hl & Hq). apply in_map_iff in Hl as (e & <- & He).
      rewrite Forall_forall in HE. pose proof (HE e He) as EOK.
      destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBUF & _ & HHP & _).
      unfold entry_nc in Hq. apply in_app_iff in Hq as [Hq|Hq].
      * destruct (Z.eqb_spec (re_cap e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
        destruct HBUF as [(C1 & _)|(C1 & IN & _)]; [lia|]. exists (re_cap e). split; [exact C1|exact IN].
      * destruct (Z.eqb_spec (re_hp e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
        destruct HHP as [(C1 & _)|(IN & _ & _ & K8 & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
    + apply in_concat in Hq as (l & Hl & Hq). apply in_map_iff in Hl as (p & <- & Hp).
      destruct (HS p Hp) as (HA & SRC).
      destruct SRC as (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & HPART & _ & _ & _ & _ & LE & LH & _).
      unfold src_nc in Hq. rewrite !in_app_iff in Hq.
      destruct Hq as [Hq|[[<-|[]]|[Hq|Hq]]].
      * exact (l2_arr_pos _ _ _ _ _ _ q LP Hq).
      * exists 6000. split; [lia|exact HPART].
      * exact (l2_arr_pos _ _ _ _ _ _ q LE Hq).
      * exact (l2_arr_pos _ _ _ _ _ _ q LH Hq).
Qed.

Lemma l2_ncs_wt : forall L A mem md G nout cap out es hj,
  aa_MR API L A mem md -> output_at B L A mem nout cap out -> In (G, SRC_TABLE) (blocks L A) ->
  Forall (CF.RelayRep.entry_ok B L A mem) es -> (forall p, In p hj -> exists HA, src_at B L A mem HA (fst p)) ->
  (length es <= 4)%nat -> length hj = length es -> List.NoDup (map fst (blocks L A)) ->
  ncs (view_of G (bv_unsigned out) es hj) L A <= nc_wt es hj.
Proof.
  intros L A mem md G nout cap out es hj HM HO HG Hent HS Hes Hlen HN.
  assert (XG : nc_sz L A G <= SRC_TABLE) by (rewrite (nw_sz_at L A _ _ HN HG); lia).
  assert (XO : nc_sz L A (bv_unsigned out) <= TBBYTES).
  { unfold output_at in HO. cbv zeta in HO. destruct HO as ((O & junk & Hc) & Hcap).
    destruct Hc as [(Hc0 & Ho0 & _)|(_ & _ & Hin & _)].
    - rewrite Ho0, (nw_sz_none L A 0 (nw_no_zero B API L A mem md HM)). unfold TBBYTES. lia.
    - rewrite (nw_sz_at L A _ _ HN Hin). exact Hcap. }
  assert (XE : AllocBound.zsum (nc_sz L A) (concat (map entry_nc es)) <= AllocBound.zsum nw_ent es).
  { rewrite nw_zsum_concat. apply nw_zsum_le. intros e He.
    rewrite Forall_forall in Hent. exact (nw_ent_le B L A mem e HN (Hent e He)). }
  assert (XS : AllocBound.zsum (nc_sz L A) (concat (map (fun p => src_nc (fst p)) hj)) <=
               AllocBound.zsum (fun p => nw_src (fst p)) hj).
  { rewrite nw_zsum_concat. apply nw_zsum_le. intros p Hp.
    destruct (HS p Hp) as (HA & Hsrc). exact (nw_src_le B L A mem _ (fst p) HN Hsrc). }
  unfold ncs, view_of, nc_wt. cbn [rv_nc]. rewrite !AllocBound.zsum_cons, AllocBound.zsum_app.
  unfold NW_ENT0, NW_SRC0, CF.op_add_c.PARTIAL_BYTES. lia.
Qed.

Lemma l2_rel_src : forall P st L A mem t nfd G OUT es hj Lss kss,
  l2_rel (rc := rc) B P st L A mem t nfd G OUT es hj Lss kss ->
  forall p, In p hj -> exists HA, src_at B L A mem HA (fst p).
Proof.
  intros P st L A mem t nfd G OUT es hj Lss kss (_ & _ & _ & _ & _ & _ & LH & PA & _) p Hp.
  destruct (In_nth hj p no_hj Hp) as (i & Hi & Ei).
  pose proof (PA i ltac:(lia)) as PE. rewrite Ei in PE. destruct p as [h j].
  destruct (l2_pair_src B P _ _ _ _ _ _ h j _ _ PE) as [S _]. exists (G_S + SRC_SIZE * Z.of_nat j). exact S.
Qed.

End L2H.

Section L2.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable E : sstart.
Variable RI : res_inv.
Variables t k : Z.
Variable fx' : FPState.
Variables cl br gn dd ei G nfd : Z.
Variables mx nout cap out : word.
Variable N : nat.
Variables Lss kss : list (list (list Z)).
Variables ob P slack : list byte.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HAX : AllocExtra B (aa_MR API).
Hypothesis HBW : blocks_writable B API.
Hypothesis HSL : block_slack_present B API.
Hypothesis HNDB : blocks_nodup B API.
Hypothesis HPL : forall a, in_globals G_reply a -> img_plain B a.
Hypothesis HERR : errno_addr B = 0x31acc.
Hypothesis HERRC : forall m, exists ev, rw_cells (ms_segs B) m (errno_addr B) [C4 ev].
Hypothesis HINP : 0 < ss_n E -> exists q, In (q, ss_n E) (user_blocks (ss_A E)) /\ ptr_addr (ss_L E) q = ss_p E.
Hypothesis HNIT : 0 < ss_n E -> ~ In (ss_p E, ss_n E) (ss_T E).
Hypothesis HSPLO : YM05.alloc_ceiling + SLOT_STACK <= spZ (ss_regs E).
Hypothesis HSPHI : spZ (ss_regs E) < 2 ^ 63.
Hypothesis HPLEN : (length P + 1 + length slack <= 48)%nat.
Hypothesis HTP : getr (ss_regs E) 4 = Z_to_bv 64 (ms_tp B).
Hypothesis HSPAL : spZ (ss_regs E) mod 16 = 0.
Hypothesis HCNL : @check_no_loss_contract fx' rc B API pack3_ag_formT.
Hypothesis HCSE : @check_shape_ends_contract fx' rc B API pack3_ag_formT.
Hypothesis HRNL : (l2_res_nl3P GSF RM_ag).
Hypothesis HRSE : (l2_res_se3P GSF RM_ag).
Hypothesis HRI3 : RI = (RI3P GSF).
Hypothesis HOS : gn = 0 -> bzs ob = concat (l2_segs P Lss kss N).
Hypothesis HNO : bv_unsigned nout = (if gn =? 0 then Z.of_nat (length (concat (l2_segs P Lss kss N))) else 0).
Hypothesis HOBL : Z.of_nat (length ob) = bv_unsigned nout.
Hypothesis HP0 : ~ In (Z_to_bv 8 0) P.
Hypothesis HPA : (- (slot_sp E + 40 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis HFZ : frm_zero (@fp_csr fx').
Hypothesis HTT : 0 <= t < OPS_MAX.
Hypothesis HKK : 0 <= k <= ss_n E.
Hypothesis HNN : ss_n E < INPUT_MAX.
Hypothesis HNFD : 0 <= nfd <= t + 1.
Hypothesis HN4 : (N <= 4)%nat.

Definition l2_body (st : nat -> l2st) (av : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (es : list rentry) (hj : list (hsrc * nat)) : Prop :=
  aa_MR API L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm (ss_md E)) /\
  ro_agree (ms_segs B) mem /\ image_kept (rc := rc) B E mem /\ stack_mid B E mem /\
  driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem /\
  globals_at B mem cl br gn dd ei (Z.of_nat N) G nfd mx nout cap out /\
  output_at (rc := rc) B L A mem nout cap out /\
  l2_rel (rc := rc) B P st L A mem t nfd G (bv_unsigned out) es hj Lss kss /\
  length es = N /\ slot_cost es hj <= k /\ RI E k (view_of G (bv_unsigned out) es hj) L A /\
  rw_cells (ms_segs B) mem (slot_sp E + 32) [C8 (Z_to_bv 64 av)] /\
  rw_cells (ms_segs B) mem (slot_sp E + 40) [CB (length P + 1 + length slack) (P ++ Z_to_bv 8 0 :: slack)] /\
  bytes_at (ms_segs B) mem (bv_unsigned out) ob.

Definition l2_core (d : nat) : layout -> astate -> (word -> option byte) -> Model -> list rentry ->
    list (hsrc * nat) -> Prop :=
  l2_body (fun p => if Nat.ltb p d then L2Post else L2Pre) (g5_at gn (l2_segs P Lss kss N) d).

Definition l2_regs (i j : nat) (regs : bvmap 5 word) : Prop :=
  base_regs E regs /\
  getr regs 23 = Z_to_bv 64 (slot_sp E + 32) /\ getr regs 25 = Z_to_bv 64 DIV10 /\
  getr regs 27 = Z_to_bv 64 (G_S + 4) /\ getr regs 24 = Z_to_bv 64 1 /\
  getr regs 8 = Z_to_bv 64 (ss_p E + k) /\ getr regs 26 = Z_to_bv 64 (ss_n E - k) /\
  getr regs 22 = Z_to_bv 64 t /\ getr regs 9 = Z_to_bv 64 (G_S + 96 * Z.of_nat i) /\
  getr regs 18 = Z_to_bv 64 (Z.of_nat j) /\ getr regs 19 = Z_to_bv 64 (56 * Z.of_nat j) /\
  getr regs 21 = Z_to_bv 64 (4 - Z.of_nat i).

Definition l2_cnt (j i : nat) (hj : list (hsrc * nat)) : nat :=
  if Nat.ltb (snd (nth j hj no_hj)) i then S j else j.

Definition l2_inv (j i : nat) (c : config) : Prop :=
  exists L A regs mem md es hj,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x14510) mem (seg_rom (ms_segs B))) md /\
    (j < N)%nat /\ (i < 4)%nat /\ l2_regs i j regs /\ l2_core (l2_cnt j i hj) L A mem md es hj.

Definition l2_s24 (c : config) : Prop :=
  exists L A regs mem md es hj,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x144f0) mem (seg_rom (ms_segs B))) md /\
    tail_regs E t k regs /\ l2_core 0 L A mem md es hj.

Lemma l2_step : forall (st st' : nat -> l2st) (av av' : Z) K Ew Ff (Fw : Z -> Prop) L A mem md L' A' mem' md'
    es hj1 h s hj2 h' (lbN : list Z) lo,
  l2_body st av L A mem md es (hj1 ++ (h, s) :: hj2) ->
  0 <= K -> K + SLOT_FRAME <= SLOT_STACK -> 64 <= lo ->
  rmid B API K (slot_sp E) Ew Ff L A mem md L' A' mem' md' ->
  (forall a, Ew a \/ ~ Ew a) ->
  (forall a, Ew a -> (G_S + SRC_SIZE * Z.of_nat s + lo <= a < G_S + SRC_SIZE * Z.of_nat s + 96) \/
     (slot_sp E + 32 <= a < slot_sp E + 40) \/
     (0 < hl_cap (hs_expected h) /\
      hl_v (hs_expected h) <= a < hl_v (hs_expected h) + 16 * hl_cap (hs_expected h)) \/
     (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h))) ->
  (forall q, Ff q -> In q (hs_blocks h)) ->
  (forall q, Fw q -> In q (hs_blocks h)) ->
  st_init_done A' = true -> ro_agree (ms_segs B) mem' ->
  (forall q, (q < N)%nat -> q <> length hj1 -> st' q = st q) ->
  l2_pair (rc := rc) B P (st' (length hj1)) L' A' mem' t (fresh_entry B mem' (nth (length hj1) es no_entry)) (h', s)
    (nth (length hj1) Lss []) (nth (length hj1) kss []) ->
  (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ (0 < m -> ~ Fw q)) \/ In q lbN) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ Fw q -> ~ In q lbN) ->
  (forall q, In q (hs_blocks h') -> In q (hs_blocks h) \/ In q lbN) ->
  (forall q, In q lbN -> In q (hs_blocks h')) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ Fw q -> In q (hs_blocks h) -> In q (hs_blocks h')) ->
  ~ In 0 lbN ->
  hs_pending h' = hs_pending h -> hs_off h' = hs_off h ->
  rw_cells (ms_segs B) mem' (slot_sp E + 32) [C8 (Z_to_bv 64 av')] ->
  bytes_at (ms_segs B) mem' (bv_unsigned out) ob ->
  (aa_MR API L' A' mem' md' -> output_at (rc := rc) B L' A' mem' nout cap out ->
   l2_rel (rc := rc) B P st' L' A' mem' t nfd G (bv_unsigned out) (map (fresh_entry B mem') es)
     (hj1 ++ (h', s) :: hj2) Lss kss ->
   RI E k (view_of G (bv_unsigned out) (map (fresh_entry B mem') es) (hj1 ++ (h', s) :: hj2)) L' A') ->
  l2_body st' av' L' A' mem' md' (map (fresh_entry B mem') es) (hj1 ++ (h', s) :: hj2).
Proof.
  intros st st' av av' K Ew Ff Fw L A mem md L' A' mem' md' es hj1 h s hj2 h' lbN lo
    BODY HK0 HK1 Hlo R DEC HEw HFf HFw INIT' RO' HST NEWP K2 K3 HB1 HB2 HSV HZ HPD HOF AT' OB' RV.
  destruct BODY as (HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST0 & HDK & HGL & HOUT & REL & HLEN & HCOST & HRI &
    HAT & HPF & HOB).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof REL as (_ & _ & _ & _ & _ & _ & LH & PA & _ & _ & NDA).
  rewrite l2_ta in NDA.
  assert (Lp : (length hj1 < length es)%nat) by (rewrite <- LH, length_app; cbn [length]; lia).
  pose proof (PA _ Lp) as PE. rewrite nth_middle in PE.
  destruct (l2_pair_src B P _ _ _ _ _ _ h s _ _ PE) as [SRC Hs4].
  destruct (l2_pair_src B P _ _ _ _ _ _ h' s _ _ NEWP) as [SRC' _].
  set (HA := G_S + SRC_SIZE * Z.of_nat s) in *.
  assert (HKS : YM05.alloc_ceiling <= slot_sp E - K) by (unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LH0 & _).
  pose proof SRC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE' & LH0' & _).
  pose proof (hf_list_head B L A mem _ _ _ LE) as (_ & _ & _ & EV1).
  pose proof (hf_list_head B L A mem _ _ _ LH0) as (_ & _ & _ & HV1).
  set (Ew' := fun a => (HA + lo <= a < HA + 96) \/
     (0 < hl_cap (hs_expected h) /\
      hl_v (hs_expected h) <= a < hl_v (hs_expected h) + 16 * hl_cap (hs_expected h)) \/
     (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h))).
  assert (RW : rmid B API SLOT_STACK (spZ (ss_regs E)) Ew' Ff L A mem md L' A' mem' md').
  { apply (rmid_widen_E B API K (slot_sp E) SLOT_STACK (spZ (ss_regs E)) Ew Ew' Ff L A mem md L' A' mem' md' HMR);
      [unfold slot_sp, SLOT_FRAME in *; lia|unfold slot_sp, SLOT_FRAME; lia|lia|lia| |exact DEC| | |exact R].
    - intros a Ha. destruct HIK as (_ & _ & _ & I4). apply I4. unfold lib_scratch. left. exact Ha.
    - intros a Ha. destruct (HEw a Ha) as [X|[X|X]]; [right; left; exact X|left|right; right; exact X].
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - intros a Ha1 Ha2. destruct (HEw a Ha2) as [X|[X|[(C & X)|(C & X)]]].
      + exfalso. unfold HA, G_S, SRC_SIZE, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      + replace a with (slot_sp E + 32 + (a - (slot_sp E + 32))) by lia. apply (rw_writable _ _ _ _ _ AT').
        cbn [cells_size csize]. lia.
      + exfalso. specialize (EV1 C). unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
      + exfalso. specialize (HV1 C). unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (HKW : YM05.alloc_ceiling <= spZ (ss_regs E) - SLOT_STACK) by lia.
  assert (EWA : forall a,
      (0 < hl_cap (hs_expected h) /\
       hl_v (hs_expected h) <= a < hl_v (hs_expected h) + 16 * hl_cap (hs_expected h)) \/
      (0 < hl_cap (hs_held h) /\ hl_v (hs_held h) <= a < hl_v (hs_held h) + 16 * hl_cap (hs_held h)) ->
      ~ in_img B a /\ a < YM05.alloc_ceiling).
  { intros a [(C & X)|(C & X)].
    - destruct (hf_list_v B L A mem _ _ _ LE C) as [VB _]. split; [|specialize (EV1 C); lia].
      replace a with (hl_v (hs_expected h) + (a - hl_v (hs_expected h))) by lia.
      exact (hf_blk_img B API HAX L A mem md _ _ (a - hl_v (hs_expected h)) HMR VB ltac:(lia)).
    - destruct (hf_list_v B L A mem _ _ _ LH0 C) as [VB _]. split; [|specialize (HV1 C); lia].
      replace a with (hl_v (hs_held h) + (a - hl_v (hs_held h))) by lia.
      exact (hf_blk_img B API HAX L A mem md _ _ (a - hl_v (hs_held h)) HMR VB ltac:(lia)). }
  assert (WIN : forall a, HA + lo <= a < HA + 96 -> in_img B a).
  { intros a Ha. exact (proj1 (HPL a ltac:(apply in_G_bss; unfold HA, G_S, SRC_SIZE in *; lia))). }
  assert (KPT : forall q, ~ In q (hs_blocks h) -> kept_block Ew' Ff L A q).
  { intros q NQ. apply (l2_kept B API HAX L A mem md Ew' Ff (HA + lo) (96 - lo) h q HA HMR SRC);
      [| |exact HFf|exact NQ].
    - intros a Ha. apply WIN. lia.
    - intros a [X|X]; [left; lia|right; exact X]. }
  assert (IMGNE : forall a, in_img B a -> ~ (HA + 64 <= a < HA + 96) -> ~ Ew' a).
  { intros a Ha NW [X|X]; [apply NW; lia|exact (proj1 (EWA a X) Ha)]. }
  assert (OUTP : bv_unsigned out = 0 \/ exists k0, 0 < k0 /\ In (bv_unsigned out, k0) (blocks L A)).
  { unfold output_at in HOUT. cbv zeta in HOUT.
    destruct HOUT as ((O & junk & [(H1 & H2 & _)|(H1 & _ & H3 & _)]) & _); [left; exact H2|right].
    exists (bv_unsigned cap). split; assumption. }
  assert (SK0 : forall a cs, rw_cells (ms_segs B) mem a cs -> slot_sp E <= a ->
      a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ (slot_sp E + 32 <= a + i < slot_sp E + 40)) ->
      rw_cells (ms_segs B) mem' a cs).
  { intros a cs H1 H2 H3 H4. apply (rmid_rw_hi B API K (slot_sp E) Ew Ff L A mem md L' A' mem' md' a cs);
      [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|rewrite HERR; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia
      |exact HMR|exact R|exact H1|exact H2|exact H3|].
    intros k0 Hk0 X. destruct (HEw _ X) as [X1|[X1|X1]].
    - unfold HA, G_S, SRC_SIZE, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - exact (H4 k0 Hk0 X1).
    - destruct (EWA _ X1) as (_ & X2). unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  pose proof RW as (M' & W' & BD' & _ & _ & _ & _ & _ & _ & VM' & _).
  split; [exact M'|]. split; [exact W'|]. split; [exact BD'|]. split; [exact INIT'|].
  split; [destruct HVM as (vm & ->); destruct VM' as (vm' & ->); exists vm'; apply with_vmmaps_twice|].
  split; [exact RO'|].
  split.
  { apply (l2_img_keep B API HAX HSEG HPL E SLOT_STACK (spZ (ss_regs E)) Ew' Ff L A mem md L' A' mem' md' (HA + 64) 32
      HIK RW HMR HKW).
    - intros a [X|X]; [left; lia|right; exact (EWA a X)].
    - intros a Ha. split; [apply in_G_bss; unfold HA, G_S, SRC_SIZE in *; lia|].
      destruct (Z_lt_ge_dec a (HA + 80)) as [D|D].
      + split.
        * replace a with (HA + 64 + (a - (HA + 64))) by lia. apply (rw_writable _ _ _ _ _ (proj1 LE)).
          cbn [cells_size csize]. lia.
        * replace a with (HA + 64 + (a - (HA + 64))) by lia. apply (rw_writable _ _ _ _ _ (proj1 LE')).
          cbn [cells_size csize]. lia.
      + split.
        * replace a with (HA + 80 + (a - (HA + 80))) by lia. apply (rw_writable _ _ _ _ _ (proj1 LH0)).
          cbn [cells_size csize]. lia.
        * replace a with (HA + 80 + (a - (HA + 80))) by lia. apply (rw_writable _ _ _ _ _ (proj1 LH0')).
          cbn [cells_size csize]. lia.
    - intros a Ha. exact Ha.
    - intros a Ha. left. exact Ha. }
  split.
  { destruct HST0 as (ST1 & ST2 & ST3). unfold stack_mid.
    split; [apply SK0; [exact ST1|lia|unfold saved_cells; cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia
           |intros i Hi; lia]|].
    split; [apply SK0; [exact ST2|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia
           |intros i Hi; cbn [cells_size csize Nat.add] in Hi; lia]|].
    apply SK0; [exact ST3|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia
           |intros i Hi; cbn [cells_size csize Nat.add] in Hi; lia]. }
  split.
  { assert (ND1 : List.NoDup (map fst (blocks L A))) by (apply hf_nodup; exact (HNDB L A mem md HMR)).
    apply (push_driver B API HBW E _ _ SLOT_STACK (spZ (ss_regs E)) Ew' Ff L A mem md L' A' mem' md'
      (hs_blocks h) (hs_blocks h') HWF ND1 HDK RW HINP HNIT).
    - intros q Hq. rewrite l2_ta. apply in_app_iff. right. apply in_app_iff. left. exact Hq.
    - intros q Hq. rewrite l2_ta, fresh_entries_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hq.
    - intros q Hq HNL. rewrite l2_ta in Hq. rewrite l2_ta, fresh_entries_blocks.
      apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|right].
      apply in_app_iff in Hq as [Hq|Hq]; [exfalso; exact (HNL Hq)|]. apply in_app_iff. right. exact Hq.
    - intros q Hq. rewrite l2_ta, fresh_entries_blocks in Hq. rewrite l2_ta.
      apply in_app_iff in Hq as [Hq|Hq]; [left; apply in_app_iff; left; exact Hq|].
      apply in_app_iff in Hq as [Hq|Hq]; [right; exact Hq|].
      left. apply in_app_iff. right. apply in_app_iff. right. exact Hq.
    - intros q Hq. exact (g5_src_blocks B L A mem _ h q SRC Hq).
    - intros q m Hq. destruct (K2 q m Hq) as [(Ho & Hm)|Hn]; [|right; exact (HB2 q Hn)].
      destruct (in_dec Z.eq_dec q (hs_blocks h)) as [IH|IH].
      + destruct (Z_le_gt_dec m 0) as [M0|M0]; [left; split; [exact Ho|intros; lia]|].
        right. exact (HSV q m Ho ltac:(lia) (Hm ltac:(lia)) IH).
      + left. split; [exact Ho|intros _; exact IH].
    - intros q m Hq Hm NI X. destruct (HB1 q X) as [Y|Y]; [exact (NI Y)|].
      exact (K3 q m Hq Hm (fun Z => NI (HFw q Z)) Y).
    - intros q HQ. apply KPT. intros X. apply HQ. rewrite l2_ta. apply in_app_iff. right. apply in_app_iff. left.
      exact X. }
  split.
  { apply (push_globals B API HAX HSEG SLOT_STACK (spZ (ss_regs E)) Ew' Ff L A mem md L' A' mem' md'
      cl br gn dd ei _ G nfd mx nout cap out HKW HMR RW HPL).
    - intros a [X|X]; [left; unfold HA in *; l2_gs; lia|right; exact (proj1 (EWA a X))].
    - exact HERRC.
    - exact HGL. }
  assert (OUTA' : output_at (rc := rc) B L' A' mem' nout cap out).
  { apply (output_rmid B API HBW SLOT_STACK (spZ (ss_regs E)) Ew' Ff L A mem md L' A' mem' md' nout cap out RW HOUT).
    intros HC0. apply KPT. intros X.
    exact (nodup_mid_out _ _ _ _ NDA ltac:(apply in_app_iff; left; right; left; reflexivity) X). }
  assert (REL' : l2_rel (rc := rc) B P st' L' A' mem' t nfd G (bv_unsigned out) (map (fresh_entry B mem') es)
      (hj1 ++ (h', s) :: hj2) Lss kss).
  { apply (l2_rel_step B API HAX HBW HSEG HSL HPL P st st' SLOT_STACK (spZ (ss_regs E)) Ew' Ff L A mem md L' A' mem' md'
      t nfd G (bv_unsigned out) es hj1 h s hj2 h' Lss kss lbN HKW HMR RW REL OUTP).
    - intros q Hq Hne. apply HST; [lia|exact Hne].
    - exact IMGNE.
    - intros q _ NQ. exact (KPT q NQ).
    - exact NEWP.
    - exact HB1.
    - intros q m Hq Hm NI X. exact (K3 q m Hq Hm (fun Z => NI (HFw q Z)) X).
    - exact HZ. }
  split; [exact OUTA'|].
  split; [exact REL'|].
  split; [rewrite length_map; exact HLEN|].
  split.
  { rewrite fresh_cost. rewrite (l2_cost_swap es hj1 hj2 (h', s) (h, s)); [exact HCOST|].
    intros e0. unfold pair_cost, pending_stream. cbn [fst]. rewrite HPD, HOF. reflexivity. }
  split; [exact (RV M' OUTA' REL')|].
  split; [exact AT'|].
  split; [|exact OB'].
  apply SK0; [exact HPF|lia|cbn [cells_size csize]; unfold slot_sp, SLOT_FRAME in *; lia|].
  intros i Hi. lia.
Qed.

Lemma l2_call1 : forall (st : nat -> l2st) L A R1 mem md es hj1 h s hj2,
  l2_body st (g5_at gn (l2_segs P Lss kss N) (length hj1)) L A mem md es (hj1 ++ (h, s) :: hj2) ->
  st (length hj1) = L2Pre ->
  getr R1 1 = Z_to_bv 64 0x14558 -> getr R1 2 = Z_to_bv 64 (slot_sp E) ->
  getr R1 4 = getr (ss_regs E) 4 -> getr R1 10 = Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat s) ->
  getr R1 11 = Z_to_bv 64 (slot_sp E + 32) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' R1 (Z_to_bv 64 CHECK_NO_LOSS) mem (seg_rom (ms_segs B))) md)
    (fun c' => exists L' A' regs' mem' md' h1,
       c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 0x14558) mem' (seg_rom (ms_segs B))) md' /\
       regs_preserved R1 regs' /\
       l2_body (fun q => if Nat.eqb q (length hj1) then L2Mid else st q)
         (g5_at gn (l2_segs P Lss kss N) (length hj1) +
          (if gn =? 0 then Z.of_nat (length (with_nul (nth (length hj1) Lss []))) else 0))
         L' A' mem' md' (map (fresh_entry B mem') es) (hj1 ++ (h1, s) :: hj2)).
Proof.
  intros st L A R1 mem md es hj1 h s hj2 BODY STP G1 G2 G4 G10 G11.
  set (segsz := l2_segs P Lss kss N) in *.
  set (A0 := g5_at gn segsz (length hj1)) in *.
  set (Ls := nth (length hj1) Lss []) in *. set (ks := nth (length hj1) kss []) in *.
  pose proof BODY as (HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST0 & HDK & HGL & HOUT & REL & HLEN & HCOST & HRI &
    HAT & HPF & HOB).
  pose proof REL as (_ & _ & _ & _ & _ & _ & LH & PA & _ & _ & NDA).
  rewrite l2_ta in NDA.
  assert (Lp : (length hj1 < length es)%nat) by (rewrite <- LH, length_app; cbn [length]; lia).
  pose proof (PA _ Lp) as PE. rewrite nth_middle, STP in PE. cbn [l2_pair] in PE.
  unfold l2_pre in PE. cbv zeta in PE. cbn [fst snd] in PE. fold Ls ks in PE.
  destruct PE as (SRC & Hs4 & HFD & HEOF & HEXP & HZR & NDH & NDK & SSK & KEYS & HCNT & HPN & HPC & HPS & HEC & HHC).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LHd & _).
  pose proof LE as (_ & LEn & _ & LEnd & _ & LEfa).
  pose proof LHd as (_ & LHn & _ & LHnd & _ & LHfa).
  assert (TXE : texts (hs_expected h) = Ls) by exact (texts_lines _ _ HEXP HZR).
  assert (FBE : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) (hl_recs (hs_expected h)))
    by (eapply Forall_impl; [|exact LEfa]; intros r X; exact (proj1 X)).
  assert (FBH : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) (hl_recs (hs_held h)))
    by (eapply Forall_impl; [|exact LHfa]; intros r X; exact (proj1 X)).
  assert (NDL : List.NoDup (map fst (blocks L A))) by (apply hf_nodup; exact (HNDB L A mem md HMR)).
  assert (INH : In (h, s) (hj1 ++ (h, s) :: hj2)) by (apply in_or_app; right; left; reflexivity).
  rewrite HRI3 in HRI.
  destruct (HRNL E k k L A G (bv_unsigned out) es (hj1 ++ (h, s) :: hj2) h s HRI (Z.le_refl k) INH
    ltac:(rewrite TXE; exact HCNT) NDL) as (bnd & ROK & ROOM & RIK).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (KV : 0 <= CHECK_NO_LOSS_K /\ CHECK_NO_LOSS_K + SLOT_FRAME <= SLOT_STACK)
    by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (G2' : YK11.getr R1 2 = Z_to_bv 64 (slot_sp E)) by exact G2.
  assert (SPR : spZ R1 = slot_sp E).
  { unfold spZ. rewrite G2'. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (U11 : bv_unsigned (getr R1 11) = slot_sp E + 32).
  { rewrite G11. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  pose proof HGL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & _).
  assert (SEGJ : nth (length hj1) segsz [] = gone_segment (bzs P) Ls ks) by (apply l2_seg_nth; lia).
  assert (SEGL : (length hj1 < length segsz)%nat) by (unfold segsz; rewrite l2_seg_len; lia).
  destruct (l2_stream gn segsz ob nout (length hj1) (bzs P) Ls ks (hs_expected h) HOS HNO SEGL SEGJ HEXP HZR)
    as [ST1 ST2].
  pose proof (HCNL L A R1 mem md bnd h s gn A0 nout out ob) as HC. cbv zeta in HC.
  rewrite U11, SPR in HC.
  eapply SR_bind.
  { apply HC; clear HC.
    - exact HSEG.
    - unfold call_pre_k. rewrite SPR. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|].
      split; [change (YK11.getr R1 1) with (getr R1 1); rewrite G1; unfold YK0s.ret_ok; vm_compute; reflexivity|].
      split; [unfold slot_sp, SLOT_FRAME in *; Z.div_mod_to_equations; lia|].
      split; [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
      split; [unfold slot_sp, SLOT_FRAME in *; lia|].
      split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); left; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
      split; [change (YK11.getr R1 4) with (getr R1 4); rewrite G4; exact HTP|].
      split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); right; exact Ha|].
      intros X. rewrite HINIT in X. discriminate.
    - exact HINIT.
    - exact HRO.
    - intros a Ha. apply HPL, in_G_bss. l2_gs. lia.
    - exact Hs4.
    - exact G10.
    - exact SRC.
    - exact NDH.
    - pose proof (ecap_ok_lt _ HEC). unfold hl_n in *. lia.
    - rewrite TXE. exact HCNT.
    - unfold slot_sp, SLOT_FRAME in *. Z.div_mod_to_equations. lia.
    - lia.
    - unfold slot_sp, SLOT_FRAME in *. lia.
    - exact HAT.
    - destruct Q17 as [-> | ->]; lia.
    - exact (l2_rw1 _ _ _ _ Q5).
    - exact (proj1 (l2_outv _ _ _ _ _ _ Q11)).
    - exact (proj2 (l2_outv _ _ _ _ _ _ Q11)).
    - exact HOB.
    - exact HOBL.
    - unfold output_at in HOUT. cbv zeta in HOUT.
      destruct HOUT as ((O & junk & [(C0 & O0 & N0 & OE)|(C0 & NC & IN & FR & BY & LO & LJ)]) & CAPB).
      + left. apply length_zero_iff_nil. lia.
      + right. exists (bv_unsigned cap). split; [lia|]. split; [exact IN|]. split; [exact FR|].
        intros X. exact (nodup_mid_out _ _ _ _ NDA ltac:(apply in_app_iff; left; right; left; reflexivity) X).
    - exact ST1.
    - exact ST2.
    - exact ROK.
    - exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & E' & H' & EC & RP & INIT' & (qs & LEN & OK' & SR' & SL') & RO' & SRC' &
    ER' & EV' & ECp' & NDT' & HCB & TX' & AT' & GG' & GN' & GO' & OB' & BK1 & BK2 & BK3).
  destruct (rp_split B API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RM PR]. rewrite SPR in RM.
  pose proof SRC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE' & LH' & _).
  destruct (g5_bstream (hs_expected h) Ls HEXP HZR) as [_ LBE].
  apply SR_ret. exists L', A', regs', mem', md', (set_exp_held h E' H').
  split; [rewrite EC, G1; reflexivity|].
  split; [exact PR|].
  apply (l2_step st (fun q => if Nat.eqb q (length hj1) then L2Mid else st q) A0
          (A0 + (if gn =? 0 then Z.of_nat (length (with_nul Ls)) else 0)) CHECK_NO_LOSS_K _ _
          (fun q => In q (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)))
          L A mem md L' A' mem' md' es hj1 h s hj2 (set_exp_held h E' H') (list_blocks H') 64 BODY
          (proj1 KV) (proj2 KV) ltac:(lia) RM).
  - intros a. lia.
  - intros a X. replace (slot_sp E + 40) with (slot_sp E + 32 + 8) by lia. exact X.
  - intros q X. unfold hs_blocks. apply in_app_iff in X as [X|X]; rewrite !in_app_iff; right; right;
      [left; unfold list_blocks; apply in_app_iff; right; exact X|right; exact X].
  - intros q X. unfold hs_blocks. apply in_app_iff in X as [X|X]; rewrite !in_app_iff; right; right;
      [left; unfold list_blocks; apply in_app_iff; right; exact X|right; exact X].
  - exact INIT'.
  - exact RO'.
  - intros q _ Hq. rewrite (proj2 (Nat.eqb_neq q (length hj1)) Hq). reflexivity.
  - rewrite Nat.eqb_refl. cbn [l2_pair]. unfold l2_mid. cbv zeta. cbn [fst snd].
    cbn [set_exp_held hs_fd hs_expected hs_held hs_pending hs_overlong hs_npartial hs_pjunk fresh_entry re_fd re_eof
      re_skip re_U re_keys].
    rewrite fresh_keys_texts. fold Ls ks.
    split; [exact SRC'|]. split; [exact Hs4|]. split; [exact HFD|]. split; [exact HEOF|].
    split; [exact ER'|]. split; [exact NDT'|]. split; [exact NDK|].
    split; [rewrite TX', TXE; exact SSK|]. split; [exact KEYS|].
    split; [exact (g5_held_n (hs_held h) H' (hs_expected h) TX' ltac:(rewrite TXE; exact HCNT))|].
    split; [exact HPN|]. split; [exact HPC|].
    split; [unfold pending_stream in *; cbn [hs_pending hs_off] in *; exact HPS|].
    split; [rewrite ECp'; exact HEC|].
    rewrite TXE in HCB. lia.
  - exact BK2.
  - exact BK3.
  - intros q X. unfold hs_blocks in X |- *. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held] in X.
    rewrite !in_app_iff in X. rewrite !in_app_iff.
    destruct X as [X|[X|[X|X]]]; [left; left; exact X|left; right; left; exact X| |right; exact X].
    left. right. right. left. unfold list_blocks in X |- *. rewrite ER', ECp', EV' in X. cbn [map] in X.
    rewrite app_nil_r in X. apply in_app_iff. left. exact X.
  - intros q X. unfold hs_blocks. cbn [set_exp_held hs_held]. rewrite !in_app_iff. right. right. right. exact X.
  - intros q m Hq Hm NF X. unfold hs_blocks in X |- *. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
    rewrite !in_app_iff in X. rewrite !in_app_iff.
    destruct X as [X|[X|[X|X]]]; [left; exact X|right; left; exact X| |exfalso; apply NF; apply in_app_iff; right; exact X].
    unfold list_blocks in X. apply in_app_iff in X as [X|X].
    + right. right. left. unfold list_blocks. rewrite ECp', EV'. apply in_app_iff. left. exact X.
    + exfalso. apply NF. apply in_app_iff. left. exact X.
  - intros X. pose proof (list_blocks_low B L' A' mem' _ _ _ 0 LH' X). lia.
  - reflexivity.
  - reflexivity.
  - replace (A0 + (if gn =? 0 then Z.of_nat (length (with_nul Ls)) else 0))
      with (if gn =? 0 then A0 + Z.of_nat (length (bstream (hs_expected h))) else A0)
      by (rewrite LBE; destruct (gn =? 0); lia).
    exact AT'.
  - exact OB'.
  - intros M' OUTA' REL'. rewrite HRI3.
    assert (NDL' : List.NoDup (map fst (blocks L' A'))) by (apply hf_nodup; exact (HNDB L' A' mem' md' M')).
    pose proof REL as (_ & GIN & _ & EOK & _ & _ & _ & _ & _ & _ & NDT0).
    pose proof REL' as (_ & GIN' & _ & EOK' & _ & _ & LH2 & _ & _ & _ & _).
    pose proof RP as (_ & _ & _ & _ & _ & ADDR & KEEP & ZERO & _).
    pose proof SR' as (SC & SV & _ & SM).
    set (V := view_of G (bv_unsigned out) es (hj1 ++ (h, s) :: hj2)) in *.
    set (V' := view_of G (bv_unsigned out) (map (fresh_entry B mem') es) (hj1 ++ (set_exp_held h E' H', s) :: hj2))
      in *.
    set (R := l2_R G (bv_unsigned out) es hj1 h hj2) in *.
    assert (P1 : Permutation (rv_nc V) (arr_nc (hs_held h) ++ R))
      by exact (l2_R_perm G (bv_unsigned out) es hj1 h s hj2).
    assert (P2 : Permutation (rv_nc V') (arr_nc H' ++ R)).
    { pose proof (l2_R_perm G (bv_unsigned out) (map (fresh_entry B mem') es) hj1 (set_exp_held h E' H') s hj2) as X.
      rewrite (l2_R_eq B mem' G (bv_unsigned out) es hj1 h (set_exp_held h E' H') hj2 eq_refl eq_refl
        ltac:(cbn [set_exp_held hs_expected]; unfold arr_nc; rewrite ECp', EV'; reflexivity)) in X.
      exact X. }
    assert (ROUT : forall q, In q R -> ~ In q (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)))
      by (intros q Hq; exact (l2_R_out G (bv_unsigned out) es hj1 h s hj2 q NDT0 Hq)).
    assert (POS : forall q, In q (rv_nc V) -> q = 0 \/ exists m, 0 < m /\ In (q, m) (blocks L A))
      by exact (l2_nc_pos B L A mem nout cap out G es (hj1 ++ (h, s) :: hj2) HOUT GIN EOK
        (l2_rel_src B P _ _ _ _ _ _ _ _ _ _ _ _ REL)).
    assert (SAME : forall q, In q R -> nc_sz L' A' q = nc_sz L A q /\ forall c0, nc_has L' A' c0 q = nc_has L A c0 q).
    { intros q Hq. apply (l2_q_same L A L' A' q NDL NDL'). intros m. split.
      - intros X. exact (BK1 q m X (ROUT q Hq)).
      - intros X. destruct (BK2 q m X) as [(Y & _)|Y]; [exact Y|exfalso].
        destruct (POS q (Permutation_in _ (Permutation_sym P1) ltac:(apply in_app_iff; right; exact Hq)))
          as [->|(m0 & Hm0 & IN0)].
        + pose proof (list_blocks_low B L' A' mem' _ _ _ 0 LH' Y). lia.
        + exact (BK3 q m0 IN0 Hm0 (ROUT q Hq) Y). }
    destruct (ncm3_core V L A V' L' A' R (arr_nc (hs_held h)) (arr_nc H') P1 P2 SAME) as (C1 & C2).
    destruct (l2_arr_sz B L A mem _ _ _ NDL LHd) as (S1 & K1).
    destruct (l2_arr_sz B L' A' mem' _ _ _ NDL' LH') as (S2 & K2).
    cbn [set_exp_held hs_held] in S2, K2. rewrite S1, S2 in C1.
    apply (RIK L' A' qs LEN OK' V').
    + unfold V'. pose proof (l2_nc_len G (bv_unsigned out) (map (fresh_entry B mem') es)
        (hj1 ++ (set_exp_held h E' H', s) :: hj2)) as NL.
      rewrite LH2, length_map in NL. unfold NC_MAX. lia.
    + intros c0 _. unfold arr_dl. change (sh_cap (sh_of (known_at L A) (hs_held h))) with (hl_cap (hs_held h)).
      rewrite <- SC. pose proof (C2 c0) as X. rewrite K1, K2 in X. lia.
    + change (sh_cap (sh_of (known_at L A) (hs_held h))) with (hl_cap (hs_held h)). rewrite <- SC. lia.
    + unfold V'. exact (l2_ncs_wt B API L' A' mem' md' G nout cap out _ _ M' OUTA' GIN' EOK'
        (l2_rel_src B P _ _ _ _ _ _ _ _ _ _ _ _ REL') ltac:(rewrite length_map; lia) LH2 NDL').
    + unfold V, V', view_of. cbn [rv_wt].
      rewrite (l2_wt_mid es (map (fresh_entry B mem') es) hj1 h (set_exp_held h E' H') s hj2 (l2_wt_fresh B mem' es)
        (length_map _ _)).
      rewrite l2_src_exp_held.
      assert (EQE : nw_list E' = Z.max (16 * hl_cap (hs_expected h)) 128).
      { unfold nw_list, hl_n. rewrite ECp', ER'. cbn [length Z.of_nat]. unfold NC_PER. lia. }
      assert (LN : Z.of_nat (length (hl_recs H')) = sh_n (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
          (map (shr (known_at L A)) (hl_recs (hs_expected h))))).
      { unfold sh_n. apply (f_equal (@length _)) in SM. rewrite !length_map in SM. rewrite SM. reflexivity. }
      assert (EQH : nw_list H' = Z.max (16 * sh_cap (check_no_loss_sh 0 (sh_of (known_at L A) (hs_held h))
          (map (shr (known_at L A)) (hl_recs (hs_expected h))))) (NC_PER * sh_n (check_no_loss_sh 0
          (sh_of (known_at L A) (hs_held h)) (map (shr (known_at L A)) (hl_recs (hs_expected h)))) + 128)).
      { unfold nw_list, hl_n. rewrite SC, LN. reflexivity. }
      rewrite EQE, EQH. unfold DATA_PER. lia.
    + unfold V, V', view_of. cbn [rv_pend]. unfold pend_view. rewrite !map_app. cbn [map]. reflexivity.
    + intros c0 _. exact (ek_view_clear G (bv_unsigned out) es G (bv_unsigned out) (map (fresh_entry B mem') es) hj1
        (h, s) (set_exp_held h E' H', s) hj2 c0 ER').
    + exact (ek_view_clear_b G (bv_unsigned out) es G (bv_unsigned out) (map (fresh_entry B mem') es) hj1
        (h, s) (set_exp_held h E' H', s) hj2 ER').
    + unfold V', view_of. cbn [rv_ek]. apply ek_view_nonneg.
    + exact NDL'.
    + intros p n Hin Hq Hg. apply (Permutation_in _ P1) in Hq. apply in_app_iff in Hq as [Hq|Hq].
      * exfalso. unfold arr_nc in Hq. destruct (Z.eqb_spec (hl_cap (hs_held h)) 0) as [C0|C0]; [destruct Hq|].
        destruct Hq as [Hq|[]]. destruct Hg as [Hg|Hg]; [exact (Hg (eq_sym Hq))|exact (C0 Hg)].
      * rewrite (l2_old_ptr L A L' A' (fun q => In q (map fst (hl_recs (hs_expected h)) ++ list_blocks (hs_held h)))
          p n ADDR KEEP ZERO HWF Hin (ROUT _ Hq)).
        apply (Permutation_in _ (Permutation_sym P2)). apply in_app_iff. right. exact Hq.
    + intros NZ. rewrite <- (SV NZ). apply (Permutation_in _ (Permutation_sym P2)). apply in_app_iff. left.
      unfold arr_nc. destruct (Z.eqb_spec (hl_cap H') 0) as [Z0|Z0]; [rewrite SC in Z0; contradiction|left; reflexivity].
Qed.

Lemma l2_call2 : forall (st : nat -> l2st) L A R2 mem md es hj1 h s hj2,
  l2_body st (g5_at gn (l2_segs P Lss kss N) (length hj1) +
              (if gn =? 0 then Z.of_nat (length (with_nul (nth (length hj1) Lss []))) else 0))
    L A mem md es (hj1 ++ (h, s) :: hj2) ->
  st (length hj1) = L2Mid ->
  getr R2 1 = Z_to_bv 64 0x14568 -> getr R2 2 = Z_to_bv 64 (slot_sp E) ->
  getr R2 4 = getr (ss_regs E) 4 -> getr R2 10 = Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat s) ->
  getr R2 11 = Z_to_bv 64 (slot_sp E + 40) -> getr R2 12 = Z_to_bv 64 (slot_sp E + 32) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' R2 (Z_to_bv 64 CHECK_SHAPE_ENDS) mem (seg_rom (ms_segs B))) md)
    (fun c' => exists L' A' regs' mem' md' h2,
       c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 0x14568) mem' (seg_rom (ms_segs B))) md' /\
       regs_preserved R2 regs' /\
       l2_body (fun q => if Nat.eqb q (length hj1) then L2Post else st q)
         (g5_at gn (l2_segs P Lss kss N) (S (length hj1)))
         L' A' mem' md' (map (fresh_entry B mem') es) (hj1 ++ (h2, s) :: hj2)).
Proof.
  intros st L A R2 mem md es hj1 h s hj2 BODY STP G1 G2 G4 G10 G11 G12.
  set (segsz := l2_segs P Lss kss N) in *.
  set (Ls := nth (length hj1) Lss []) in *. set (ks := nth (length hj1) kss []) in *.
  set (A1 := g5_at gn segsz (length hj1) + (if gn =? 0 then Z.of_nat (length (with_nul Ls)) else 0)) in *.
  pose proof BODY as (HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST0 & HDK & HGL & HOUT & REL & HLEN & HCOST & HRI &
    HAT & HPF & HOB).
  pose proof REL as (_ & _ & _ & _ & _ & _ & LH & PA & _ & _ & NDA).
  rewrite l2_ta in NDA.
  assert (Lp : (length hj1 < length es)%nat) by (rewrite <- LH, length_app; cbn [length]; lia).
  pose proof (PA _ Lp) as PE. rewrite nth_middle, STP in PE. cbn [l2_pair] in PE.
  unfold l2_mid in PE. cbv zeta in PE. cbn [fst snd] in PE. fold ks in PE.
  destruct PE as (SRC & Hs4 & HFD & HEOF & ER0 & NDH & NDK & SSK & KEYS & HN26 & HPN & HPC & HPS & HEC & HHC).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LE & LHd & _).
  pose proof LHd as (_ & LHn & _ & LHnd & _ & LHfa).
  assert (FBH : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) (hl_recs (hs_held h)))
    by (eapply Forall_impl; [|exact LHfa]; intros r X; exact (proj1 X)).
  pose proof HGL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & _).
  assert (NDL : List.NoDup (map fst (blocks L A))) by (apply hf_nodup; exact (HNDB L A mem md HMR)).
  rewrite HRI3 in HRI.
  destruct (HRSE E k k (view_of G (bv_unsigned out) es (hj1 ++ (h, s) :: hj2)) L A h gn P (skipn (Z.to_nat A1) ob)
    HRI (Z.le_refl k)) as (bnd & ROK & ROOM & RIK).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (KV : 0 <= CHECK_SHAPE_ENDS_K /\ CHECK_SHAPE_ENDS_K + SLOT_FRAME <= SLOT_STACK)
    by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (G2' : YK11.getr R2 2 = Z_to_bv 64 (slot_sp E)) by exact G2.
  assert (SPR : spZ R2 = slot_sp E).
  { unfold spZ. rewrite G2'. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (U11 : bv_unsigned (getr R2 11) = slot_sp E + 40).
  { rewrite G11. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (U12 : bv_unsigned (getr R2 12) = slot_sp E + 32).
  { rewrite G12. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (SEGJ : nth (length hj1) segsz [] = gone_segment (bzs P) Ls ks) by (apply l2_seg_nth; lia).
  assert (SEGL : (length hj1 < length segsz)%nat) by (unfold segsz; rewrite l2_seg_len; lia).
  pose proof (g5_held_nz B L A mem _ h SRC) as NZ.
  destruct (l2_ends_pre gn segsz ob nout (length hj1) P Ls ks (hs_held h) HOS HNO SEGL SEGJ NDK NDH SSK NZ)
    as [EP1 EP2].
  fold A1 in EP1, EP2.
  assert (PFB0 : bytes_at (ms_segs B) mem (slot_sp E + 40) (P ++ Z_to_bv 8 0 :: slack)).
  { destruct HPF as [[_ X] _]. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
  pose proof (HCSE L A R2 mem md bnd h s gn A1 nout out ob P slack) as HC. cbv zeta in HC.
  rewrite U11, U12, SPR in HC.
  eapply SR_bind.
  { apply HC; clear HC.
    - exact HSEG.
    - unfold call_pre_k. rewrite SPR. split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|].
      split; [change (YK11.getr R2 1) with (getr R2 1); rewrite G1; unfold YK0s.ret_ok; vm_compute; reflexivity|].
      split; [unfold slot_sp, SLOT_FRAME in *; Z.div_mod_to_equations; lia|].
      split; [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
      split; [unfold slot_sp, SLOT_FRAME in *; lia|].
      split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); left; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
      split; [change (YK11.getr R2 4) with (getr R2 4); rewrite G4; exact HTP|].
      split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); right; exact Ha|].
      intros X. rewrite HINIT in X. discriminate.
    - exact HINIT.
    - exact HRO.
    - intros a Ha. apply HPL, in_G_bss. l2_gs. lia.
    - exact Hs4.
    - exact G10.
    - exact SRC.
    - exact NDH.
    - exact HN26.
    - exact PFB0.
    - exact HP0.
    - exact HPA.
    - left. split; [lia|]. unfold slot_sp, SLOT_FRAME in *. lia.
    - unfold slot_sp, SLOT_FRAME in *. Z.div_mod_to_equations. lia.
    - lia.
    - unfold slot_sp, SLOT_FRAME in *. lia.
    - left. lia.
    - exact HAT.
    - destruct Q17 as [-> | ->]; lia.
    - exact (l2_rw1 _ _ _ _ Q5).
    - exact (proj1 (l2_outv _ _ _ _ _ _ Q11)).
    - exact (proj2 (l2_outv _ _ _ _ _ _ Q11)).
    - exact HOB.
    - exact HOBL.
    - unfold output_at in HOUT. cbv zeta in HOUT.
      destruct HOUT as ((O & junk & [(C0 & O0 & N0 & OE)|(C0 & NC & IN & FR & BY & LO & LJ)]) & CAPB).
      + left. apply length_zero_iff_nil. lia.
      + right. exists (bv_unsigned cap). split; [lia|]. split; [exact IN|]. split; [exact FR|].
        intros X. exact (nodup_mid_out _ _ _ _ NDA ltac:(apply in_app_iff; left; right; left; reflexivity) X).
    - exact EP1.
    - intros G0. destruct (EP2 G0) as (rs' & ds & ER & _). rewrite ER. discriminate.
    - exact ROK. }
  intros c' (L' & A' & regs' & mem' & md' & H' & ds & c & EC & RP & INIT' & (qs & LEN & OK') & RO' & SRC' & HV' & HC' &
    NDT' & CASE & AT' & PFB & GG' & GN' & GO' & OB' & BK1 & BK2).
  destruct (rp_split B API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RM PR]. rewrite SPR in RM.
  assert (EX : gn = 0 -> exists rs' ds' c', ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A1) ob)
                 (want_of P (hl_recs (hs_held h))) = Some (rs', ds', c') /\
               (forall y, In y (rtexts rs') <-> In y (rtexts (hl_recs (hs_held h))) /\ has_prefix (bzs P) y = false)).
  { intros G0. destruct (EP2 G0) as (rs' & ds' & ER & CH). exists rs', ds'. eexists. split; [exact ER|exact CH]. }
  destruct (l2_held_after gn P ks (hs_held h) H' ds c (skipn (Z.to_nat A1) ob) NDK SSK CASE EX) as (SSH & RIN & INC).
  pose proof (g5_ds_incl gn P (hs_held h) H' ds c _ _ CASE) as DSI.
  assert (CV : A1 + c = g5_at gn segsz (S (length hj1))).
  { unfold A1. apply (l2_at_step gn segsz (length hj1) (bzs P) Ls ks c SEGL SEGJ).
    - intros Hg. destruct CASE as [(_ & _ & _ & C0)|(G0 & _)]; [exact C0|contradiction].
    - intros G0. destruct CASE as [(G1' & _)|(_ & ER)]; [contradiction|].
      destruct (EP2 G0) as (rs' & ds' & ER' & _). rewrite ER in ER'. injection ER' as _ _ C0. exact C0. }
  apply SR_ret. exists L', A', regs', mem', md', (set_held h H').
  split; [rewrite EC, G1; reflexivity|].
  split; [exact PR|].
  apply (l2_step st (fun q => if Nat.eqb q (length hj1) then L2Post else st q) A1
          (g5_at gn segsz (S (length hj1))) CHECK_SHAPE_ENDS_K _ _ (fun q => In q (map fst ds))
          L A mem md L' A' mem' md' es hj1 h s hj2 (set_held h H') [] 88 BODY
          (proj1 KV) (proj2 KV) ltac:(lia) RM).
  - intros a. lia.
  - intros a [X|[X|X]]; [left; l2_gs; lia|right; left; lia|right; right; right; exact X].
  - intros q X. unfold hs_blocks. rewrite !in_app_iff. right. right. right. unfold list_blocks.
    apply in_app_iff. right. exact X.
  - intros q X. apply in_map_iff in X as (r & <- & Hr). unfold hs_blocks. rewrite !in_app_iff. right. right. right.
    unfold list_blocks. apply in_app_iff. right. apply in_map. exact (DSI r Hr).
  - exact INIT'.
  - exact RO'.
  - intros q _ Hq. rewrite (proj2 (Nat.eqb_neq q (length hj1)) Hq). reflexivity.
  - rewrite Nat.eqb_refl. cbn [l2_pair]. unfold pair_ok. cbv zeta. cbn [fst snd].
    cbn [set_held hs_fd hs_expected hs_held hs_pending hs_overlong hs_npartial hs_pjunk fresh_entry re_fd re_eof
      re_skip re_U re_keys].
    rewrite fresh_keys_texts, KEYS.
    split; [exact SRC'|]. split; [exact Hs4|]. split; [exact HFD|]. split; [exact HEOF|].
    split; [exact SSH|]. split; [exact NDT'|]. split; [exact ER0|].
    split; [exact HPN|]. split; [exact HPC|].
    split; [unfold pending_stream in *; cbn [hs_pending hs_off] in *; exact HPS|].
    split; [exact HEC|]. rewrite HC'. exact HHC.
  - intros q m X. left. destruct (BK2 q m X) as [Y1 Y2]. split; [exact Y1|intros _; exact Y2].
  - intros q m _ _ _ [].
  - intros q X. left. unfold hs_blocks in X |- *. cbn [set_held hs_pending hs_partial hs_expected hs_held] in X.
    rewrite !in_app_iff in X. rewrite !in_app_iff.
    destruct X as [X|[X|[X|X]]]; [left; exact X|right; left; exact X|right; right; left; exact X|].
    right. right. right. unfold list_blocks in X |- *. rewrite HV', HC' in X. apply in_app_iff in X as [X|X].
    + apply in_app_iff. left. exact X.
    + apply in_app_iff. right. apply in_map_iff in X as (r & <- & Hr). apply in_map. exact (INC r Hr).
  - intros q [].
  - intros q m Hq Hm NF X. unfold hs_blocks in X |- *. cbn [set_held hs_pending hs_partial hs_expected hs_held].
    rewrite !in_app_iff in X. rewrite !in_app_iff.
    destruct X as [X|[X|[X|X]]]; [left; exact X|right; left; exact X|right; right; left; exact X|].
    right. right. right. unfold list_blocks in X |- *. rewrite HV', HC'. apply in_app_iff in X as [X|X].
    + apply in_app_iff. left. exact X.
    + apply in_map_iff in X as (r & <- & Hr). destruct (RIN r Hr) as [Y|Y].
      * apply in_app_iff. right. apply in_map. exact Y.
      * exfalso. apply NF. apply in_map. exact Y.
  - intros [].
  - reflexivity.
  - reflexivity.
  - rewrite <- CV. exact AT'.
  - exact OB'.
  - intros M' OUTA' REL'. rewrite HRI3.
    assert (NDL' : List.NoDup (map fst (blocks L' A'))) by (apply hf_nodup; exact (HNDB L' A' mem' md' M')).
    pose proof REL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDT0).
    pose proof REL' as (_ & GIN' & _ & EOK' & _ & _ & LH2 & _ & _ & _ & _).
    pose proof RP as (_ & _ & _ & _ & _ & ADDR & KEEP & ZERO & _).
    assert (SNC : src_nc (set_held h H') = src_nc h)
      by (unfold src_nc, arr_nc; cbn [set_held hs_pending hs_partial hs_expected hs_held]; rewrite HV', HC'; reflexivity).
    assert (NCE : rv_nc (view_of G (bv_unsigned out) (map (fresh_entry B mem') es) (hj1 ++ (set_held h H', s) :: hj2)) =
                  rv_nc (view_of G (bv_unsigned out) es (hj1 ++ (h, s) :: hj2))).
    { rewrite !l2_nc_mid, SNC.
      replace (map entry_nc (map (fresh_entry B mem') es)) with (map entry_nc es); [reflexivity|].
      rewrite map_map. apply map_ext. intros e. reflexivity. }
    set (V := view_of G (bv_unsigned out) es (hj1 ++ (h, s) :: hj2)) in *.
    set (V' := view_of G (bv_unsigned out) (map (fresh_entry B mem') es) (hj1 ++ (set_held h H', s) :: hj2)) in *.
    assert (OUTQ : forall q, In q (rv_nc V) -> ~ In q (map fst ds)).
    { intros q Hq X. destruct (l2_nc_out G (bv_unsigned out) es hj1 h s hj2 q NDT0 Hq) as [_ N2]. apply N2.
      apply in_map_iff in X as (r & <- & Hr). apply in_map. exact (DSI r Hr). }
    assert (SAME : forall q, In q (rv_nc V) ->
        nc_sz L' A' q = nc_sz L A q /\ forall c0, nc_has L' A' c0 q = nc_has L A c0 q).
    { intros q Hq. apply (l2_q_same L A L' A' q NDL NDL'). intros m. split.
      - intros X. exact (BK1 q m X (OUTQ q Hq)).
      - intros X. exact (proj1 (BK2 q m X)). }
    destruct (ncm3_core V L A V' L' A' (rv_nc V) [] [] (Permutation_refl _)
      ltac:(rewrite NCE; apply Permutation_refl) SAME) as (C1 & C2).
    rewrite !AllocBound.zsum_nil in C1.
    pose proof HRI as ((b0 & al0 & alb0 & _ & _ & _ & HNC & _) & _).
    pose proof SRC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LHH & _).
    pose proof LHH as (_ & _ & _ & NDR & _).
    assert (LNH : (length (hl_recs H') <= length (hl_recs (hs_held h)))%nat).
    { apply NoDup_incl_length; [|exact INC]. apply (NoDup_map_inv fst).
      first [exact NDR | apply hf_nodup; exact NDR]. }
    apply (RIK L' A' qs LEN OK' V').
    + rewrite NCE. exact HNC.
    + intros c0 _. pose proof (C2 c0) as X. rewrite !AllocBound.zsum_nil in X. lia.
    + lia.
    + unfold V'. exact (l2_ncs_wt B API L' A' mem' md' G nout cap out _ _ M' OUTA' GIN' EOK'
        (l2_rel_src B P _ _ _ _ _ _ _ _ _ _ _ _ REL') ltac:(rewrite length_map; lia) LH2 NDL').
    + unfold V, V', view_of. cbn [rv_wt].
      rewrite (l2_wt_mid es (map (fresh_entry B mem') es) hj1 h (set_held h H') s hj2 (l2_wt_fresh B mem' es)
        (length_map _ _)).
      rewrite l2_src_held. pose proof (l2_list_le (hs_held h) H' HC' LNH). unfold DATA_PER. lia.
    + unfold V, V', view_of. cbn [rv_pend]. unfold pend_view. rewrite !map_app. cbn [map]. reflexivity.
    + unfold V, V', view_of. cbn [rv_ek]. unfold ek_view. rewrite !map_app. cbn [map]. reflexivity.
    + exact NDL'.
    + intros p n Hin Hq. rewrite NCE.
      rewrite (l2_old_ptr L A L' A' (fun q => In q (map fst (hl_recs (hs_held h)))) p n ADDR KEEP ZERO HWF Hin
        (proj2 (l2_nc_out G (bv_unsigned out) es hj1 h s hj2 _ NDT0 Hq))).
      exact Hq.
Qed.

Lemma l2_body_ext : forall st st' av L A mem md es hj, (forall q, (q < N)%nat -> st q = st' q) ->
  l2_body st av L A mem md es hj -> l2_body st' av L A mem md es hj.
Proof.
  intros st st' av L A mem md es hj HS
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & REL & HLEN & H14 & H15 & H16 & H17 & H18).
  destruct REL as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11
    (conj _ (conj HLEN (conj H14 (conj H15 (conj H16 (conj H17 H18))))))))))))))))).
  refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj _ (conj R9 (conj R10 R11)))))))))).
  intros p Hp. rewrite <- HS by lia. exact (R8 p Hp).
Qed.

Lemma l2_slot_cells : forall st av L A mem md es hj j i, l2_body st av L A mem md es hj -> (j < N)%nat ->
  (i < 4)%nat ->
  exists fd op, rw_cells (ms_segs B) mem (G_S + 96 * Z.of_nat i) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 op)] /\
    0 <= fd < 2 ^ 31 /\ 0 <= op < 2 ^ 31 /\
    (op <> 0 -> fd = re_fd (nth j es no_entry) -> snd (nth j hj no_hj) = i) /\
    (snd (nth j hj no_hj) = i -> op <> 0 /\ fd = re_fd (nth j es no_entry)).
Proof.
  intros st av L A mem md es hj j i BODY Hj Hi.
  destruct BODY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REL & HLEN & _).
  destruct REL as (_ & _ & _ & _ & NDF & _ & LH & PA & NDH & ZH & _).
  assert (Hj' : (j < length es)%nat) by lia.
  destruct (slot_open hj i) eqn:Ho.
  - pose proof Ho as Ho'. unfold slot_open in Ho'. apply existsb_exists in Ho' as (x & Hx & Ex).
    apply Nat.eqb_eq in Ex. subst x.
    apply in_map_iff in Hx as (pp & Es & Hpp). destruct (In_nth _ _ no_hj Hpp) as (q & Hq & Eq).
    rewrite LH in Hq. pose proof (PA q Hq) as PQ. rewrite Eq in PQ. destruct pp as [hq iq]. cbn [snd] in Es.
    subst iq.
    destruct (l2_pair_src B P _ _ _ _ _ _ _ _ _ _ PQ) as [S _].
    pose proof (l2_pair_fd B P _ _ _ _ _ _ _ _ _ _ PQ) as FDq.
    destruct S as (C1 & _ & _ & HO & HF & _).
    exists (hs_fd hq), (hs_open hq).
    split; [exact (proj1 (hg_cut _ _ _ [_; _] [_; _] C1))|].
    split; [lia|]. split; [lia|]. split.
    + intros _ X. rewrite FDq in X.
      assert (QJ : q = j) by exact (g5_nodup_nth re_fd es no_entry q j NDF Hq Hj' X).
      subst q. rewrite Eq. reflexivity.
    + intros X.
      assert (QJ : j = q).
      { apply (g5_nodup_nth snd hj no_hj j q NDH); [lia|lia|rewrite Eq; exact X]. }
      subst q. split; [lia|exact FDq].
  - exists 0, 0. split; [exact (l2_zero_cells _ _ _ (ZH i Hi Ho))|].
    split; [lia|]. split; [lia|]. split; [intros X; lia|].
    intros X. exfalso. unfold slot_open in Ho.
    assert (IN : In (snd (nth j hj no_hj)) (map snd hj)) by (apply in_map, nth_In; lia).
    rewrite X in IN.
    rewrite (proj2 (existsb_exists _ _) (ex_intro _ i (conj IN (Nat.eqb_refl i)))) in Ho. discriminate.
Qed.

Lemma l2_regs_rg : forall i j R, l2_regs i j R ->
  reg_get R 2 = Z_to_bv 64 (slot_sp E) /\ reg_get R 3 = getr (ss_regs E) 3 /\ reg_get R 4 = getr (ss_regs E) 4 /\
  reg_get R 8 = Z_to_bv 64 (ss_p E + k) /\ reg_get R 9 = Z_to_bv 64 (G_S + 96 * Z.of_nat i) /\
  reg_get R 18 = Z_to_bv 64 (Z.of_nat j) /\ reg_get R 19 = Z_to_bv 64 (56 * Z.of_nat j) /\
  reg_get R 20 = Z_to_bv 64 0x318a0 /\ reg_get R 21 = Z_to_bv 64 (4 - Z.of_nat i) /\ reg_get R 22 = Z_to_bv 64 t /\
  reg_get R 23 = Z_to_bv 64 (slot_sp E + 32) /\ reg_get R 24 = Z_to_bv 64 1 /\
  reg_get R 25 = Z_to_bv 64 DIV10 /\ reg_get R 26 = Z_to_bv 64 (ss_n E - k) /\
  reg_get R 27 = Z_to_bv 64 (G_S + 4).
Proof.
  intros i j R ((B2 & B3 & B4 & B20) & X23 & X25 & X27 & X24 & X8 & X26 & X22 & X9 & X18 & X19 & X21).
  split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact X8|]. split; [exact X9|].
  split; [exact X18|]. split; [exact X19|]. split; [exact B20|]. split; [exact X21|]. split; [exact X22|].
  split; [exact X23|]. split; [exact X24|]. split; [exact X25|]. split; [exact X26|]. exact X27.
Qed.

Lemma l2_regs_pres : forall i j R R', l2_regs i j R -> regs_preserved R R' -> l2_regs i j R'.
Proof.
  intros i j R R' ((B2 & B3 & B4 & B20) & X23 & X25 & X27 & X24 & X8 & X26 & X22 & X9 & X18 & X19 & X21) PR.
  unfold l2_regs, base_regs. repeat split.
  - exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) B2).
  - exact (eq_trans (PR 3 ltac:(unfold callee_saved; lia)) B3).
  - exact (eq_trans (PR 4 ltac:(unfold callee_saved; lia)) B4).
  - exact (eq_trans (PR 20 ltac:(unfold callee_saved; lia)) B20).
  - exact (eq_trans (PR 23 ltac:(unfold callee_saved; lia)) X23).
  - exact (eq_trans (PR 25 ltac:(unfold callee_saved; lia)) X25).
  - exact (eq_trans (PR 27 ltac:(unfold callee_saved; lia)) X27).
  - exact (eq_trans (PR 24 ltac:(unfold callee_saved; lia)) X24).
  - exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) X8).
  - exact (eq_trans (PR 26 ltac:(unfold callee_saved; lia)) X26).
  - exact (eq_trans (PR 22 ltac:(unfold callee_saved; lia)) X22).
  - exact (eq_trans (PR 9 ltac:(unfold callee_saved; lia)) X9).
  - exact (eq_trans (PR 18 ltac:(unfold callee_saved; lia)) X18).
  - exact (eq_trans (PR 19 ltac:(unfold callee_saved; lia)) X19).
  - exact (eq_trans (PR 21 ltac:(unfold callee_saved; lia)) X21).
Qed.

Lemma l2_rdN : forall m, rw_cells (ms_segs B) m G_NSRC [C4 (Z_to_bv 64 (Z.of_nat N)); C4 (Z_to_bv 64 16)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318b8) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat N))).
Proof.
  intros m X. destruct X as [[_ X] _]. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X.
  apply bytes_at_app in X as [X _]. rewrite HSEG in X. exact (op5_rd4 m _ _ X).
Qed.

Lemma l2_rdG : forall m, rw_cells (ms_segs B) m G_SRC [C8 (Z_to_bv 64 G)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 0x318d0) 8 = Some (le8 (Z_to_bv 64 G)).
Proof.
  intros m X. destruct X as [[_ X] _]. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. rewrite HSEG in X.
  exact (l2_rd8 m _ _ X).
Qed.

Lemma l2_rdAT : forall m v, rw_cells (ms_segs B) m (slot_sp E + 32) [C8 (Z_to_bv 64 v)] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (slot_sp E + 32)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m v X. destruct X as [[_ X] _]. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. rewrite HSEG in X.
  exact (l2_rd8 m _ _ X).
Qed.

Lemma l2_pack : forall L A regs mem md es hj, l2_core N L A mem md es hj -> tail_regs E t k regs ->
  getr regs 1 = Z_to_bv 64 0x145bc ->
  getr regs 10 = Z_to_bv 64 (g5_at gn (l2_segs P Lss kss N) N) ->
  J4 (rc := rc) B API E RI t k (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x14ca0) mem (seg_rom (ms_segs B))) md).
Proof.
  intros L A regs mem md es hj CORE TR RA R10.
  unfold l2_core in CORE.
  destruct CORE as (HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST0 & HDK & HGL & HOUT & REL & HLEN & HCOST & HRI & _).
  assert (GA : g5_at gn (l2_segs P Lss kss N) N = bv_unsigned nout).
  { rewrite HNO. unfold g5_at. rewrite firstn_all2 by (rewrite l2_seg_len; lia). reflexivity. }
  unfold J4, MI.
  exists fx', L, A, regs, mem, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj.
  split; [reflexivity|]. split; [exact HFZ|]. split; [exact HTT|]. split; [exact HKK|]. split; [exact HNN|].
  split; [split; [exact TR|]; split; [exact RA|]; rewrite R10, GA; reflexivity|].
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
  split; [exact HRO|]. split; [exact HIK|]. split; [exact HST0|]. split; [exact HDK|].
  split; [rewrite HLEN; exact HGL|].
  split; [unfold TAIL_CHECK, TAIL_STEP; cbn; lia|].
  split; [exact HOUT|].
  split.
  { replace (t + (if (0x14ca0 =? TAIL_CHECK) || (0x14ca0 =? TAIL_STEP) then 1 else 0)) with t
      by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
    destruct REL as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10' & R11).
    split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
    split; [exact R6|].
    split.
    { apply (g5_forall2_of_nth _ _ _ no_entry no_hj); [symmetry; exact R7|].
      intros q Hq. pose proof (R8 q Hq) as X. rewrite (proj2 (Nat.ltb_lt q N) ltac:(lia)) in X. exact X. }
    split; [exact R9|]. split; [exact R10'|]. exact R11. }
  split; [lia|]. split; [exact HCOST|]. exact HRI.
Qed.

Lemma l2_next_post : forall j i L A mem md es hj d v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    can ms,
  (j < N)%nat -> (i < 4)%nat ->
  l2_core d L A mem md es hj ->
  v = Z_to_bv 64 (g5_at gn (l2_segs P Lss kss N) d) ->
  ((S i < 4)%nat -> d = l2_cnt j (S i) hj) ->
  (S i = 4%nat -> d = S j) ->
  op5_l2_next (slot_sp E) (Z.of_nat N) i j v x1 (getr (ss_regs E) 3) (getr (ss_regs E) 4) x5 x6 x7
    (Z_to_bv 64 (ss_p E + k)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 t) (Z_to_bv 64 (slot_sp E + 32))
    (Z_to_bv 64 1) (Z_to_bv 64 DIV10) (Z_to_bv 64 (ss_n E - k)) (Z_to_bv 64 (G_S + 4)) x28 x29 x30 x31
    fp_regs fp_csr mem (seg_rom rsegs) can ->
  Regs6ss.ms_eqv can ms ->
  SR (ms_segs B) (mkCfg ms md) (fun c' => J4 (rc := rc) B API E RI t k c' \/
    exists w : nat * nat, (4 * N - (4 * fst w + snd w) < 4 * N - (4 * j + i))%nat /\ l2_inv (fst w) (snd w) c').
Proof.
  intros j i L A mem md es hj d v x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 can ms Hj Hi CORE HV
    D1 D2 NX EQ.
  unfold op5_l2_next in NX.
  destruct NX as [(Hlt & ->)|[(Heq & HJN & ->)|(Heq & HJN & ->)]];
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R' & -> & X); rewrite <- HSEG; apply SR_ret.
  - right. exists (j, S i). cbn [fst snd]. split; [lia|].
    exists L, A, R', mem, md, es, hj. split; [reflexivity|]. split; [exact Hj|]. split; [exact Hlt|].
    split; [unfold l2_regs, base_regs; repeat split; geq X|].
    rewrite <- (D1 Hlt). exact CORE.
  - right. exists (S j, 0%nat). cbn [fst snd]. split; [lia|].
    exists L, A, R', mem, md, es, hj. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [unfold l2_regs, base_regs; repeat split; geq X|].
    assert (C0 : l2_cnt (S j) 0 hj = S j) by (unfold l2_cnt; destruct (snd (nth (S j) hj no_hj)); reflexivity).
    rewrite C0, <- (D2 Heq). exact CORE.
  - left. assert (DN : d = N) by (rewrite (D2 Heq); lia). subst d.
    apply (l2_pack L A R' mem md es hj CORE).
    + unfold tail_regs, base_regs, fix_regs; repeat split; geq X.
    + geq X.
    + rewrite <- HV. geq X.
Qed.

Lemma l2_iter : forall j i c, l2_inv j i c ->
  SR (ms_segs B) c (fun c' => J4 (rc := rc) B API E RI t k c' \/
    exists w : nat * nat, (4 * N - (4 * fst w + snd w) < 4 * N - (4 * j + i))%nat /\ l2_inv (fst w) (snd w) c').
Proof.
  intros j i c (L & A & regs & mem & md & es & hj & -> & Hj & Hi & HRG & CORE).
  pose proof CORE as CORE0. unfold l2_core in CORE0.
  pose proof CORE0 as (HMR & _ & _ & _ & _ & _ & _ & _ & _ & HGL & _ & REL & HLEN & _ & _ & HAT & _ & _).
  pose proof REL as ((tail & TL & TC) & GIN & GFR & ES & _ & _ & LH & PA & _ & _ & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & _).
  assert (G0 : G <> 0) by (destruct GFR as (GF0 & _); lia).
  assert (GAL : G mod 8 = 0).
  { pose proof GIN as GIN0. unfold blocks in GIN0. apply in_map_iff in GIN0 as ([p k'] & EG & Hp).
    cbn [fst snd] in EG. injection EG as EG _. rewrite <- EG.
    pose proof (mr_blocks_aligned _ _ (aa_laws API) L A mem md p k' HMR Hp) as H16.
    Z.div_mod_to_equations. lia. }
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & Q8 & _ & Q10 & _).
  assert (HW : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
                   (re_eof e = 0 \/ re_eof e = 1)) es).
  { eapply Forall_impl; [|exact ES]. intros e (EO & _ & P1 & P2 & FD & _).
    split; [exact P1|]. split; [exact P2|]. split; [exact FD|exact EO]. }
  assert (Hj' : (j < length es)%nat) by lia.
  destruct (nth_error es j) as [e|] eqn:HE; [|apply nth_error_None in HE; lia].
  assert (EJ : nth j es no_entry = e) by (apply nth_error_nth; exact HE).
  destruct (l2_slot_cells _ _ L A mem md es hj j i CORE0 Hj Hi) as (fd & op & SC & Hfd & Hop & IMP1 & IMP2).
  rewrite EJ in IMP1, IMP2.
  assert (Hjh : (j < length hj)%nat) by lia.
  pose proof (PA j Hj') as PJ.
  destruct (nth j hj no_hj) as [h s] eqn:EH.
  try rewrite EH in IMP1. try rewrite EH in IMP2. try rewrite EH in PJ. cbn [snd] in IMP1, IMP2.
  destruct (l2_pair_src B P _ _ _ _ _ _ _ _ _ _ PJ) as [_ Hs4].
  destruct (l2_regs_rg i j regs HRG) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 &
    E26 & E27).
  rewrite HSEG in SC, TC.
  rewrite HSEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    apply (op5_l2_head es tail (slot_sp E) G (Z.of_nat N) fd op i j e
             (Z_to_bv 64 (g5_at gn (l2_segs P Lss kss N) (l2_cnt j i hj))));
      [exact Hi|lia|exact Hfd|exact Hop|exact HE|exact HW|exact (l2_rdN mem Q8)|exact (l2_rdG mem Q10)
      |exact (l2_rdAT mem _ HAT)|exact TC|exact SC|exact G0|exact GAL]. }
  intros ms1 (can1 & HQ & EQ1).
  destruct HQ as [(Hop0 & Hfd0 & ->)|[(Hop0 & NX)|(Hop0 & Hfd0 & NX)]].
  - destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    pose proof (IMP1 Hop0 Hfd0) as HSI. subst s.
    assert (DJ : l2_cnt j i hj = j) by (unfold l2_cnt; rewrite EH; cbn [snd]; rewrite Nat.ltb_irrefl; reflexivity).
    rewrite DJ in CORE.
    pose proof (split_at hj j no_hj Hjh) as SPL. rewrite EH in SPL.
    set (hj1 := firstn j hj) in *. set (hj2 := skipn (S j) hj) in *.
    assert (L1 : length hj1 = j) by (unfold hj1; rewrite length_firstn; lia).
    rewrite SPL in CORE. unfold l2_core in CORE. rewrite <- L1 in CORE.
    assert (HR1 : l2_regs i j R1) by (unfold l2_regs, base_regs; repeat split; geq X1).
    rewrite <- HSEG.
    eapply SR_bind.
    { apply (l2_call1 (fun p => if Nat.ltb p (length hj1) then L2Post else L2Pre) L A R1 mem md es hj1 h i hj2 CORE).
      - rewrite Nat.ltb_irrefl. reflexivity.
      - geq X1.
      - geq X1.
      - geq X1.
      - geq X1.
      - geq X1. }
    intros c2 (L2 & A2 & regs2 & mem2 & md2 & h1 & -> & PR1 & BODY2).
    pose proof (l2_regs_pres i j R1 regs2 HR1 PR1) as HR2.
    pose proof BODY2 as (HMR2 & _).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hl2 & _).
    destruct (l2_regs_rg i j regs2 HR2) as (F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 &
      F25 & F26 & F27).
    rewrite HSEG. eapply (evt_SR_canon rsegs); [|exact Hh2|exact Hl2|].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      rewrite F2, F3, F4, F8, F9, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27.
      apply op5_l2_mid. }
    intros ms2 (can2 & -> & EQ2).
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
    assert (HR3 : l2_regs i j R2) by (unfold l2_regs, base_regs; repeat split; geq X2).
    rewrite <- HSEG.
    eapply SR_bind.
    { apply (l2_call2 (fun q => if Nat.eqb q (length hj1) then L2Mid else (if Nat.ltb q (length hj1) then L2Post else L2Pre))
              L2 A2 R2 mem2 md2 (map (fresh_entry B mem2) es) hj1 h1 i hj2 BODY2).
      - rewrite Nat.eqb_refl. reflexivity.
      - geq X2.
      - geq X2.
      - geq X2.
      - geq X2.
      - geq X2.
      - geq X2. }
    intros c3 (L3 & A3 & regs3 & mem3 & md3 & h2 & -> & PR2 & BODY3).
    pose proof (l2_regs_pres i j R2 regs3 HR3 PR2) as HR4.
    set (es3 := map (fresh_entry B mem3) (map (fresh_entry B mem2) es)) in *.
    set (hj3 := hj1 ++ (h2, i) :: hj2) in *.
    assert (CORE3 : l2_core (S j) L3 A3 mem3 md3 es3 hj3).
    { unfold l2_core. rewrite <- L1. revert BODY3. apply l2_body_ext.
      intros q Hq. cbv beta.
      destruct (Nat.eqb_spec q (length hj1)) as [->|Hne].
      - rewrite (proj2 (Nat.ltb_lt _ _) (Nat.lt_succ_diag_r _)). reflexivity.
      - destruct (Nat.ltb_spec q (length hj1)) as [Q1|Q1]; destruct (Nat.ltb_spec q (S (length hj1))) as [Q2|Q2];
          first [reflexivity|lia]. }
    pose proof CORE3 as CORE3'. unfold l2_core in CORE3'.
    pose proof CORE3' as (HMR3 & _ & _ & _ & _ & _ & _ & _ & _ & HGL3 & _ & _ & _ & _ & _ & HAT3 & _ & _).
    destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR3) as (Hh3 & Hl3 & _).
    pose proof HGL3 as (_ & _ & _ & _ & _ & _ & _ & Q8' & _).
    destruct (l2_regs_rg i j regs3 HR4) as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 &
      K25 & K26 & K27).
    rewrite HSEG. eapply (evt_SR_canon rsegs); [|exact Hh3|exact Hl3|].
    { rewrite canon_mkst. unfold Regs6ss.mkR_of.
      rewrite K2, K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27.
      apply (op5_l2_adv (slot_sp E) (Z.of_nat N) i j (Z_to_bv 64 (g5_at gn (l2_segs P Lss kss N) (S j))));
        [exact Hi|lia|lia|exact (l2_rdN mem3 Q8')|exact (l2_rdAT mem3 _ HAT3)]. }
    intros ms4 (can4 & NX4 & EQ4).
    rewrite <- HSEG.
    eapply (l2_next_post j i L3 A3 mem3 md3 es3 hj3 (S j) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ can4 ms4 Hj Hi CORE3
             eq_refl); [| |exact NX4|exact EQ4].
    + intros _. unfold l2_cnt, hj3. rewrite <- L1, nth_middle. cbn [snd].
      rewrite (proj2 (Nat.ltb_lt _ _) (Nat.lt_succ_diag_r _)). reflexivity.
    + intros _. reflexivity.
  - assert (NSI : s <> i) by (intros X; destruct (IMP2 X) as [X1 _]; exact (X1 Hop0)).
    rewrite <- HSEG.
    eapply (l2_next_post j i L A mem md es hj (l2_cnt j i hj) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ can1 ms1 Hj Hi CORE
             eq_refl); [| |exact NX|exact EQ1].
    + intros Hlt. unfold l2_cnt. rewrite EH. cbn [snd]. destruct (Nat.ltb_spec s i), (Nat.ltb_spec s (S i)); lia.
    + intros Heq. unfold l2_cnt. rewrite EH. cbn [snd]. destruct (Nat.ltb_spec s i); lia.
  - assert (NSI : s <> i) by (intros X; destruct (IMP2 X) as [_ X2]; exact (Hfd0 X2)).
    rewrite <- HSEG.
    eapply (l2_next_post j i L A mem md es hj (l2_cnt j i hj) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ can1 ms1 Hj Hi CORE
             eq_refl); [| |exact NX|exact EQ1].
    + intros Hlt. unfold l2_cnt. rewrite EH. cbn [snd]. destruct (Nat.ltb_spec s i), (Nat.ltb_spec s (S i)); lia.
    + intros Heq. unfold l2_cnt. rewrite EH. cbn [snd]. destruct (Nat.ltb_spec s i); lia.
Qed.

Lemma l2_loop : forall j i c, l2_inv j i c -> SR (ms_segs B) c (J4 (rc := rc) B API E RI t k).
Proof.
  intros j i c HL.
  refine (SR_loop (ms_segs B) (nat * nat) (fun w => (4 * N - (4 * fst w + snd w))%nat)
            (fun w c => l2_inv (fst w) (snd w) c) (J4 (rc := rc) B API E RI t k) _ (j, i) c HL).
  intros [j' i'] c' HL'. cbn [fst snd] in HL' |- *. exact (l2_iter j' i' c' HL').
Qed.

Lemma l2_tail_rg : forall R, tail_regs E t k R ->
  reg_get R 2 = Z_to_bv 64 (slot_sp E) /\ reg_get R 3 = getr (ss_regs E) 3 /\ reg_get R 4 = getr (ss_regs E) 4 /\
  reg_get R 8 = Z_to_bv 64 (ss_p E + k) /\ reg_get R 19 = Z_to_bv 64 4 /\
  reg_get R 20 = Z_to_bv 64 0x318a0 /\ reg_get R 21 = Z_to_bv 64 10 /\ reg_get R 22 = Z_to_bv 64 t /\
  reg_get R 23 = Z_to_bv 64 (slot_sp E + 32) /\ reg_get R 24 = Z_to_bv 64 1 /\
  reg_get R 25 = Z_to_bv 64 DIV10 /\ reg_get R 26 = Z_to_bv 64 (ss_n E - k) /\
  reg_get R 27 = Z_to_bv 64 (G_S + 4).
Proof.
  intros R ((B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & X8 & X26 & X22).
  split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact X8|]. split; [exact F19|].
  split; [exact B20|]. split; [exact F21|]. split; [exact X22|]. split; [exact F23|]. split; [exact F24|].
  split; [exact F25|]. split; [exact X26|]. exact F27.
Qed.

Lemma l2_main : forall c, l2_s24 c -> SR (ms_segs B) c (J4 (rc := rc) B API E RI t k).
Proof.
  intros c (L & A & regs & mem & md & es & hj & -> & TR & CORE).
  pose proof CORE as CORE0. unfold l2_core in CORE0.
  pose proof CORE0 as (HMR & _ & _ & _ & _ & _ & _ & _ & _ & HGL & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & Q8 & _).
  destruct (l2_tail_rg regs TR) as (E2 & E3 & E4 & E8 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  rewrite HSEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    apply (op5_l2_start (slot_sp E) (Z.of_nat N)); [lia|exact (l2_rdN mem Q8)]. }
  intros ms1 (can1 & HQ & EQ1).
  destruct HQ as [(HN0 & ->)|(HNP & ->)];
    destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1); rewrite <- HSEG.
  - apply SR_ret. assert (N0 : N = 0%nat) by lia.
    apply (l2_pack L A R1 mem md es hj).
    + rewrite N0. exact CORE.
    + unfold tail_regs, base_regs, fix_regs; repeat split; geq X1.
    + geq X1.
    + replace (g5_at gn (l2_segs P Lss kss N) N) with 0
        by (rewrite N0; unfold g5_at; destruct (gn =? 0); reflexivity).
      geq X1.
  - apply (l2_loop 0 0).
    exists L, A, R1, mem, md, es, hj. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [unfold l2_regs, base_regs; repeat split; geq X1|].
    assert (C0 : l2_cnt 0 0 hj = 0%nat) by (unfold l2_cnt; destruct (snd (nth 0 hj no_hj)); reflexivity).
    rewrite C0. exact CORE.
Qed.

End L2.

Definition p5_s24 {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (RI : res_inv) (t k : Z)
    (c : config) : Prop :=
  exists (fx' : FPState) (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (N : nat)
         (Lss kss : list (list (list Z))) (ob P slack : list byte),
    frm_zero (@fp_csr fx') /\ 0 <= t < OPS_MAX /\ 0 <= k <= ss_n E /\ ss_n E < INPUT_MAX /\
    0 <= nfd <= t + 1 /\ (N <= 4)%nat /\
    (length P + 1 + length slack <= 48)%nat /\ ~ In (Z_to_bv 8 0) P /\
    (- (slot_sp E + 40 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) /\
    (gn = 0 -> bzs ob = concat (l2_segs P Lss kss N)) /\
    bv_unsigned nout = (if gn =? 0 then Z.of_nat (length (concat (l2_segs P Lss kss N))) else 0) /\
    Z.of_nat (length ob) = bv_unsigned nout /\
    l2_s24 (rc := rc) B API E RI t k fx' cl br gn dd ei G nfd mx nout cap out N Lss kss ob P slack c.

Theorem p5_loop2 : forall B API LS SH SK ra empty rc fx j E CS t k c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  (forall fx0 : FPState, @check_no_loss_contract fx0 rc B (API rc) pack3_ag_formT) ->
  (forall fx0 : FPState, @check_shape_ends_contract fx0 rc B (API rc) pack3_ag_formT) ->
  (l2_res_nl3P GSF RM_ag) -> (l2_res_se3P GSF RM_ag) ->
  p5_s24 (rc := rc) B (API rc) E (RI3P GSF) t k c ->
  SR (ms_segs B) c (J4 (rc := rc) B (API rc) E (RI3P GSF) t k).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS t k c HF HCNL HCSE HRNL HRSE
    (fx' & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & N & Lss & kss & ob & P & slack &
     HFZ & HTT & HKK & HNN & HNFD & HN4 & HPLEN & HP0 & HPA & HOS & HNO & HOBL & HS24).
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (SL : block_slack_present B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31b70) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (ERR : errno_addr B = 0x31acc) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  pose proof PRE as ((LPRE & _ & _ & _) & _ & _ & _ & _ & _ & NIT & _).
  pose proof LPRE as (_ & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TP & _ & _ & _ & INPUT & _).
  apply (l2_main (rc := rc) B (API rc) E (RI3P GSF) t k fx' cl br gn dd ei G nfd mx nout cap out N Lss kss ob P slack
           SEG AX BW SL NDB PL ERR).
  - intros m0. rewrite SEG. exact (CF.SlotEntry.entry_errno_cells B SEG ETP EOFF m0).
  - intros Hn0. destruct INPUT as [(X & _)|(_ & q0 & Hq0 & Eq0)]; [lia|]. exists q0. split; [exact Hq0|exact Eq0].
  - exact NIT.
  - exact SPLO.
  - exact SPHI.
  - exact HPLEN.
  - exact TP.
  - exact ALIGN.
  - exact (HCNL fx').
  - exact (HCSE fx').
  - exact HRNL.
  - exact HRSE.
  - reflexivity.
  - exact HOS.
  - exact HNO.
  - exact HOBL.
  - exact HP0.
  - exact HPA.
  - exact HFZ.
  - exact HTT.
  - exact HKK.
  - exact HNN.
  - exact HNFD.
  - exact HN4.
  - exact HS24.
Qed.
