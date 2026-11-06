(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its numbers changed; 1527 of its 1633 lines of code are new or changed and 558 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass1w.v, with its module paths, module names and addresses changed; 1120 of its 1272 lines of code are new or changed and 1481 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09
  YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import
  Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import source_reset_c check_no_loss_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import drain_b_c op_add_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadP SlotEntry RelayCap SlotExitScanAux relay_instance_gone_b_c relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import ListStep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass2Run SlotPass2Check SlotPass5Run SlotPass5Loop SlotPass5Check SlotPass1w SlotPass5T SlotPass5S SlotPass5L2 SlotEntryRun SlotExitFinAux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotNcWt SlotRI3 SlotRun3 SlotP5R3G SlotP5Res3 SlotP5Res3Full SlotDrain3 relay_instance_gone_b_lem SlotPass5M SlotPass5V SlotPass5G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocBound AllocPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPackGSF AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotRI3P SlotP5ResP SlotP5ResN.

Definition RG2 (E : sstart) (t k : Z) (regs : bvmap 5 word) : Prop := tail_regs E t k regs.

Definition J2_reads (E : sstart) (m : word -> option byte) : Prop :=
  forall i : nat, (i < 4)%nat -> exists r : Z, 0 <= r < 2 ^ 31 /\
    ov_read_bytes rsegs m (Z_to_bv 64 (slot_sp E + 16 + 4 * Z.of_nat i)) 4 = Some (le4 (Z_to_bv 64 r)) /\
    (r <> 0 -> exists n : Z, -2 ^ 31 <= n <= 0 /\
       bytes_at rsegs m (G_S + 96 * Z.of_nat i + 24) (le4 (Z_to_bv 64 n))).

Definition J2 {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (RI : res_inv) (t k : Z)
    (c : config) : Prop :=
  exists (fx' : FPState) (regs : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
         (es : list rentry) (hj : list (hsrc * nat)) (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (N : nat)
         (Lss kss : list (list (list Z))) (ob P slack : list byte),
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x13f00) mem (seg_rom (ms_segs B))) md /\
    RG2 E t k regs /\
    l2_core (rc := rc) B API E RI t k cl br gn dd ei G nfd mx nout cap out N Lss kss ob P slack 0%nat
      L A mem md es hj /\
    (length P + 1 + length slack <= 48)%nat /\
    (gn = 0 -> bzs ob = concat (l2_segs P Lss kss N)) /\
    bv_unsigned nout = (if gn =? 0 then Z.of_nat (length (concat (l2_segs P Lss kss N))) else 0) /\
    Z.of_nat (length ob) = bv_unsigned nout /\
    ~ In (Z_to_bv 8 0) P /\
    (- (slot_sp E + 40 + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) /\
    frm_zero (@fp_csr fx') /\
    0 <= t < OPS_MAX /\ 0 <= k <= ss_n E /\ ss_n E < INPUT_MAX /\ 0 <= nfd <= t + 1 /\ (N <= 4)%nat /\
    J2_reads E mem.

Lemma p5c_jal : forall
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte),
  evt rsegs (fun ms => ms = MS (mkR (Z_to_bv 64 0x13f00) x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
      x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13450) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
      x29 x30 x31) F (Z_to_bv 64 0x13efc) fc None m ro).
Proof. intros. step. apply evt_done. reflexivity. Qed.

Lemma p5c_nth_seq : forall {X} (f : nat -> X) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros X f n i d H. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma p5c_map_seq : forall {X Y} (f : X -> Y) (l : list X) d,
  map f l = map (fun i => f (nth i l d)) (seq 0 (length l)).
Proof.
  intros X Y f l d. induction l as [|x l IH]; [reflexivity|]. cbn [length seq map nth]. f_equal.
  rewrite <- seq_shift, map_map. exact IH.
Qed.

Lemma p5c_combine_seq : forall {X Y W} (f : X * Y -> W) (l1 : list X) (l2 : list Y) d1 d2,
  length l1 = length l2 ->
  map f (combine l1 l2) = map (fun i => f (nth i l1 d1, nth i l2 d2)) (seq 0 (length l1)).
Proof.
  intros X Y W f l1. induction l1 as [|x l1 IH]; intros [|y l2] d1 d2 HL; cbn [length] in HL; try discriminate;
    [reflexivity|].
  cbn [combine map length seq nth]. f_equal. rewrite <- seq_shift, map_map. rewrite (IH l2 d1 d2) by lia.
  reflexivity.
Qed.

Lemma p5c_in_cs : forall (F : nat -> list Z) n q,
  In q (concat (map F (seq 0 n))) <-> exists i, (i < n)%nat /\ In q (F i).
Proof.
  intros F n q. rewrite in_concat. split.
  - intros (l0 & Hl0 & Hq). apply in_map_iff in Hl0 as (i & <- & Hi). apply in_seq in Hi.
    exists i. split; [lia|exact Hq].
  - intros (i & Hi & Hq). exists (F i). split; [apply in_map; apply in_seq; lia|exact Hq].
Qed.

Lemma p5c_sum_le : forall (l : list nat) (f g : nat -> Z), (forall i, In i l -> f i <= g i) ->
  fold_right Z.add 0 (map f l) <= fold_right Z.add 0 (map g l).
Proof.
  intros l f g H. induction l as [|a l IH]; cbn [map fold_right]; [lia|].
  pose proof (H a (or_introl eq_refl)) as H0.
  assert (H1 : fold_right Z.add 0 (map f l) <= fold_right Z.add 0 (map g l))
    by (apply IH; intros i Hi; apply H; right; exact Hi).
  lia.
Qed.

Lemma p5c_nd_sub0 : forall (F G : nat -> list Z) (l : list nat), (forall i, In i l -> G i = F i \/ G i = []) ->
  List.NoDup (concat (map F l)) -> List.NoDup (concat (map G l)) /\
  (forall x, In x (concat (map G l)) -> In x (concat (map F l))).
Proof.
  intros F G l. induction l as [|a l IH]; intros HG ND; cbn [map concat] in *; [split; [constructor|tauto]|].
  assert (ND' := NoDup_app_remove_l _ _ ND).
  destruct (IH (fun i Hi => HG i (or_intror Hi)) ND') as [N1 S1].
  split.
  - apply hf_nodup_app.
    + destruct (HG a (or_introl eq_refl)) as [E|E]; rewrite E; [exact (hf_nodup_l _ _ ND)|constructor].
    + exact N1.
    + intros x X1 X2. destruct (HG a (or_introl eq_refl)) as [E|E]; rewrite E in X1; [|destruct X1].
      exact (hf_nodup_disj _ _ x ND X1 (S1 x X2)).
  - intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left|right; exact (S1 x Hx)].
    destruct (HG a (or_introl eq_refl)) as [E|E]; rewrite E in Hx; [exact Hx|destruct Hx].
Qed.

Lemma p5c_nd_sub : forall (X : list Z) (F G : nat -> list Z) (l : list nat),
  (forall i, In i l -> G i = F i \/ G i = []) ->
  List.NoDup (X ++ concat (map F l)) -> List.NoDup (X ++ concat (map G l)).
Proof.
  intros X F G l HG ND.
  destruct (p5c_nd_sub0 F G l HG (NoDup_app_remove_l _ _ ND)) as [N1 S1].
  apply hf_nodup_app; [exact (hf_nodup_l _ _ ND)|exact N1|].
  intros x X1 X2. exact (hf_nodup_disj _ _ x ND X1 (S1 x X2)).
Qed.

Lemma p5c_nd_idx : forall (F : nat -> list Z) (l : list nat) i i' x, List.NoDup l ->
  List.NoDup (concat (map F l)) -> In i l -> In i' l -> i <> i' -> In x (F i) -> In x (F i') -> False.
Proof.
  intros F l. induction l as [|a l IH]; intros i i' x NL ND Hi Hi' Ne X1 X2; [destruct Hi|].
  inversion NL as [|? ? NA NL']; subst. cbn [map concat] in ND.
  assert (ND' := NoDup_app_remove_l _ _ ND).
  assert (IC : forall j, In j l -> In x (F j) -> In x (concat (map F l))).
  { intros j Hj Xj. apply in_concat. exists (F j). split; [apply in_map; exact Hj|exact Xj]. }
  destruct Hi as [Ei|Hi]; destruct Hi' as [Ei'|Hi'].
  - apply Ne. rewrite <- Ei, <- Ei'. reflexivity.
  - subst i. exact (hf_nodup_disj _ _ x ND X1 (IC i' Hi' X2)).
  - subst i'. exact (hf_nodup_disj _ _ x ND X2 (IC i Hi X1)).
  - exact (IH i i' x NL' ND' Hi Hi' Ne X1 X2).
Qed.

Lemma p5c_nd_join : forall (X : list Z) (l : list nat) (f g : nat -> list Z),
  List.NoDup (X ++ concat (map f l)) -> List.NoDup (concat (map g l)) ->
  (forall q, In q (concat (map g l)) -> ~ In q X /\ ~ In q (concat (map f l))) ->
  List.NoDup (X ++ concat (map (fun i => f i ++ g i) l)).
Proof.
  intros X l f g N1 N2 D.
  assert (P : Permutation (X ++ concat (map (fun i => f i ++ g i) l))
                          ((X ++ concat (map f l)) ++ concat (map g l))).
  { rewrite <- app_assoc. apply Permutation_app_head. clear N1 N2 D.
    induction l as [|a l IH]; cbn [map concat]; [constructor|].
    rewrite <- !app_assoc. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
    rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
  apply (Permutation_NoDup (Permutation_sym P)).
  apply hf_nodup_app; [exact N1|exact N2|]. intros q Q1 Q2. destruct (D q Q2) as [D1 D2].
  apply in_app_iff in Q1 as [Q1|Q1]; [exact (D1 Q1)|exact (D2 Q1)].
Qed.

Lemma p5c_keys : forall pre (ks : list (list Z)) K K' Ls,
  NoDup ks -> same_set ks (upds (keys_texts K) Ls) -> keys_texts K' = snd (gei pre ks) ->
  keys_total K' <= keys_total K + Z.of_nat (length (with_nul Ls)).
Proof.
  intros pre ks K K' Ls ND SS EK. apply NoDup_ListNoDup in ND.
  pose proof (gei_ok pre ks ND) as G. destruct (gei pre ks) as [E0 H0]. destruct G as (_ & _ & PE & _).
  cbn [snd] in EK.
  pose proof (g5_w_perm _ _ PE) as W1. rewrite g5_w_app in W1. pose proof (g5_w_nonneg E0).
  assert (W2 : g5_w ks <= g5_w (keys_texts K ++ g5_bks Ls)).
  { apply g5_w_incl; [exact ND|]. intros y Hy. apply g5_upds_incl. apply SS. exact Hy. }
  rewrite g5_w_app in W2.
  assert (W3 : g5_w (keys_texts K) = keys_total K)
    by (unfold g5_w; rewrite concat_end5_len, <- keys_total_texts; reflexivity).
  assert (W4 : g5_w (keys_texts K') = keys_total K')
    by (unfold g5_w; rewrite concat_end5_len, <- keys_total_texts; reflexivity).
  rewrite EK in W4. pose proof (g5_bks_w Ls). lia.
Qed.

Lemma p5c_hit_range : forall fd es, 0 <= op5_hit fd es <= 1.
Proof.
  intros fd es. induction es as [|e es IH]; cbn [op5_hit]; [lia|].
  destruct (re_fd e =? fd); [destruct (re_eof e =? 0); lia|exact IH].
Qed.

Lemma p5c_rec_range : forall es fd op, 0 <= op5_rec es fd op <= 1.
Proof. intros es fd op. unfold op5_rec. destruct (op =? 0); [lia|apply p5c_hit_range]. Qed.

Lemma p5c_rd4 : forall m a e (v : word), bytes_at rsegs m a (le4 v) -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 4 = Some (le4 v).
Proof. intros m a e v H ->. exact (p2_rd4 m a v H). Qed.

Lemma p5c_da_lo : forall (es : list rentry) (hj : list (hsrc * nat)) a, drained_area es hj a -> G_S + 12 <= a.
Proof. intros es hj a (p & _ & _ & Ha). unfold SRC_SIZE in Ha. lia. Qed.

Lemma p5c_da_hi : forall (es : list rentry) (hj : list (hsrc * nat)) a,
  (forall p, In p hj -> (snd p < 4)%nat) -> drained_area es hj a -> a < G_S + 384.
Proof.
  intros es hj a HS ([e0 p] & Hp & _ & Ha). pose proof (HS _ (List.in_combine_r _ _ _ _ Hp)) as H4. cbn [snd] in *.
  unfold SRC_SIZE in Ha. lia.
Qed.

Lemma p5c_da_closed : forall (es : list rentry) (hj : list (hsrc * nat)) i a,
  slot_open hj i = false -> G_S + SRC_SIZE * Z.of_nat i <= a < G_S + SRC_SIZE * Z.of_nat i + SRC_SIZE ->
  ~ drained_area es hj a.
Proof.
  intros es hj i a SO Ha ([e0 p] & Hp & _ & Hb). cbn [fst snd] in Hb.
  assert (EJ : snd p = i) by (unfold SRC_SIZE in *; lia).
  assert (SO' : slot_open hj i = true).
  { unfold slot_open. apply existsb_exists. exists i. split; [|apply Nat.eqb_refl].
    apply in_map_iff. exists p. split; [exact EJ|exact (List.in_combine_r _ _ _ _ Hp)]. }
  rewrite SO in SO'. discriminate.
Qed.

Lemma p5c_da_src : forall (es : list rentry) (hj : list (hsrc * nat)) i a,
  length hj = length es -> NoDup (map snd hj) -> (i < length es)%nat -> re_eof (nth i es no_entry) <> 0 ->
  G_S + SRC_SIZE * Z.of_nat (snd (nth i hj no_hj)) <= a <
    G_S + SRC_SIZE * Z.of_nat (snd (nth i hj no_hj)) + SRC_SIZE ->
  ~ drained_area es hj a.
Proof.
  intros es hj i a LH ND Hi E1 Ha (p & Hp & E0 & Hb).
  destruct (In_nth _ _ (no_entry, no_hj) Hp) as (kk & Hkk & Ekk).
  rewrite length_combine, LH, Nat.min_id in Hkk.
  rewrite combine_nth in Ekk by (symmetry; exact LH). subst p. cbn [fst snd] in *.
  assert (EJ : snd (nth kk hj no_hj) = snd (nth i hj no_hj)) by (unfold SRC_SIZE in *; lia).
  pose proof (g5_nodup_nth snd hj no_hj kk i ND ltac:(lia) ltac:(lia) EJ) as EK. subst kk. exact (E1 E0).
Qed.

Lemma p5c_fds : forall (rc : RunCeil) B L A mem t (es : list rentry) (hj : list (hsrc * nat)) (fs os : list Z) i i',
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj -> NoDup (map re_fd es) ->
  (forall p, In p hj -> nth (snd p) fs 0 = hs_fd (fst p) /\ nth (snd p) os 0 = 1) ->
  (forall i, (i < 4)%nat -> slot_open hj i = false -> nth i os 0 = 0) ->
  (i < 4)%nat -> (i' < 4)%nat -> i <> i' -> nth i os 0 = 1 -> nth i' os 0 = 1 -> nth i fs 0 <> nth i' fs 0.
Proof.
  intros rc B L A mem t es hj fs os i i' PA ND HP HO Hi Hi' Ne O1 O1' EQ.
  assert (LH : length hj = length es) by (symmetry; exact (Forall2_length PA)).
  destruct (slot_open hj i) eqn:SO; [|rewrite (HO i Hi SO) in O1; discriminate].
  unfold slot_open in SO. apply existsb_exists in SO as (q & Hq & Eq). apply Nat.eqb_eq in Eq. subst q.
  apply in_map_iff in Hq as (p & Ep & Hp). destruct (In_nth _ _ no_hj Hp) as (kk & Hkk & Ekk).
  pose proof (g5_forall2_nth _ _ _ no_entry no_hj PA kk ltac:(lia)) as PK. rewrite Ekk in PK.
  unfold pair_ok in PK. cbv zeta in PK. destruct PK as (_ & _ & FD & _).
  assert (F1 : nth i fs 0 = re_fd (nth kk es no_entry)) by (rewrite <- Ep, (proj1 (HP p Hp)); exact FD).
  pose proof (g5_match B L A mem t es hj fs os i' kk PA ND (fun p Hp => proj1 (HP p Hp)) HO Hi' ltac:(lia)
    ltac:(lia) ltac:(rewrite <- EQ; exact F1)) as S'.
  apply Ne. rewrite <- S', Ekk, Ep. reflexivity.
Qed.

Lemma p5c_src_ok : forall (rc : RunCeil) B L A mem t G OUT (es : list rentry) (hj : list (hsrc * nat)) k,
  Forall (CF.RelayRep.entry_ok B L A mem) es -> Forall2 (pair_ok (rc := rc) B L A mem t) es hj ->
  slot_cost es hj <= k -> k < INPUT_MAX ->
  Forall (fun p => gone_src_ok B L A mem G OUT es (fst p) (snd p)) (combine es hj).
Proof.
  intros rc B L A mem t G OUT es hj k HF PA Hc Hk. apply Forall_forall. intros [e [h jj]] Hp. cbn [fst snd].
  unfold gone_src_ok. cbv zeta. cbn [fst snd]. intros E0.
  pose proof (g5_forall2_in _ _ _ _ _ PA Hp) as HP. unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP.
  destruct HP as (SRC & HJ & FD & SKU & _ & _ & _ & _ & _ & PS & EC & _).
  destruct (SKU E0) as [Hsk HUw].
  assert (EOK : CF.RelayRep.entry_ok B L A mem e)
    by (rewrite Forall_forall in HF; exact (HF e (List.in_combine_l _ _ _ _ Hp))).
  destruct EOK as (_ & _ & _ & _ & _ & _ & HUl & _ & _ & _ & _ & _ & _ & _ & KS).
  assert (NN : Forall (fun e0 => 0 <= re_used e0) es).
  { apply Forall_forall. intros e0 He0. rewrite Forall_forall in HF.
    destruct (HF e0 He0) as (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia. }
  pose proof (pair_cost_le_slot es hj e (h, jj) Hp NN) as PCs. unfold pair_cost in PCs. cbn [fst] in PCs.
  assert (KF' : Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e)).
  { rewrite Forall_forall in KS |- *. intros x Hx. destruct (KS x Hx) as (_ & _ & _ & _ & (K14 & _) & _). exact K14. }
  pose proof (keys_total_count (re_keys e) KF') as KT.
  assert (SK0 : 0 <= (if re_skip e =? 0 then re_used e else 0)) by (destruct (re_skip e =? 0); lia).
  unfold re_nheld, INPUT_MAX in *.
  split; [exact SRC|]. split; [exact HJ|]. split; [exact FD|]. split; [exact Hsk|]. split; [exact HUw|].
  split; [lia|]. split; [exact (proj2 (ecap_ok_lt _ EC))|]. lia.
Qed.

Lemma p5c_pre : forall (rc : RunCeil) B L A mem L' A' mem' t P (e e' : rentry) (p : hsrc * nat) (h'' : hsrc) ks
    (es : list rentry) (hjs : list (hsrc * nat)) k (ec : Z),
  Forall (CF.RelayRep.entry_ok B L A mem) es -> In (e, p) (combine es hjs) ->
  slot_cost es hjs <= k -> k < INPUT_MAX -> 0 <= t < OPS_MAX ->
  pair_ok (rc := rc) B L A mem t e p ->
  (re_eof e <> 0 -> src_at B L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd p)) (fst p)) ->
  re_fd e' = re_fd e ->
  re_eof e' = (if re_eof e =? 0 then (if hs_closed (fst p) =? 1 then 1 else 0) else 1) ->
  NoDup ks -> same_set ks (upds (keys_texts (re_keys e)) (entry_lines e p)) ->
  keys_texts (re_keys e') = snd (gei (bzs P) ks) ->
  (re_eof e = 0 ->
     src_at B L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd p)) h'' /\
     hs_fd h'' = hs_fd (fst p) /\ hs_closed h'' = hs_closed (fst p) /\
     hs_eintr h'' = 0 /\ hl_recs (hs_pending h'') = [] /\
     hl_cap (hs_pending h'') = hl_cap (hs_pending (fst p)) /\ hl_v (hs_pending h'') = hl_v (hs_pending (fst p)) /\
     hs_off h'' = 0 /\
     hs_state h'' = feed (hs_state (fst p)) (bzs (pending_stream (fst p))) /\
     map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected (fst p))) ++
       map (map (Z_to_bv 8)) (entry_lines e p) /\
     firstn (length (hl_recs (hs_expected (fst p)))) (hl_recs (hs_expected h'')) = hl_recs (hs_expected (fst p)) /\
     hs_held h'' = hs_held (fst p) /\
     re_skip e' = hs_overlong h'' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h'')) /\
     hl_cap (hs_expected h'') = ec /\
     hl_cap (hs_expected h'') <= Z.max 8 (Z.max (hl_cap (hs_expected (fst p))) (2 * hl_n (hs_expected h'')))) ->
  (re_eof e = 0 -> ecap_ok ec) ->
  l2_pre (rc := rc) B P L' A' mem' t e' (g5_src e (fst p) h'', snd p) (entry_lines e p) ks.
Proof.
  intros rc B L A mem L' A' mem' t P e e' p h'' ks es hjs k ec HF Hin Hc Hk Ht HP SRC1 FD' EOF' NDK SSK GK D0 HEC.
  destruct p as [h j]. cbn [fst snd] in *.
  pose proof HP as HP'. unfold pair_ok in HP'. cbv zeta in HP'. cbn [fst snd] in HP'.
  destruct HP' as (SRC & HJ & FD & SKU & SS & NDH & HE0 & PN & PC & PS & EC & HC).
  assert (EOK : CF.RelayRep.entry_ok B L A mem e)
    by (rewrite Forall_forall in HF; exact (HF e (List.in_combine_l _ _ _ _ Hin))).
  pose proof EOK as (_ & _ & _ & _ & _ & _ & HUl & HU6 & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hov & _).
  unfold l2_pre. cbv zeta. cbn [fst snd].
  destruct (Z.eqb_spec (re_eof e) 0) as [E0|E1].
  - destruct (D0 E0) as (SRC' & FD'' & _ & _ & PND & PCAP & _ & _ & _ & MEX & _ & HLD & SK' & SKU' & ECE & ECAP).
    assert (G5 : g5_src e h h'' = h'') by (unfold g5_src; rewrite E0; reflexivity).
    assert (EL : entry_lines e (h, j) = lines (hs_state h) (bzs (pending_stream h)))
      by (unfold entry_lines; cbn [fst]; rewrite E0; reflexivity).
    rewrite EL in MEX.
    destruct (g5_counts B L A mem t es hjs e (h, j) h'' k k HF Hin HP Hc (Z.le_refl k) Hk
      (fun _ => conj MEX HLD)) as (GC1 & _ & GC3).
    cbn [fst] in GC1, GC3. rewrite G5 in GC1, GC3 |- *. rewrite EL in SSK |- *.
    set (Ls := lines (hs_state h) (bzs (pending_stream h))) in *.
    assert (MX : map snd (hl_recs (hs_expected h'')) = map (map (Z_to_bv 8)) Ls) by (rewrite MEX, HE0; reflexivity).
    assert (ZR : Forall zrange Ls) by exact (dc_lines_range h).
    assert (TX : texts (hs_expected h'') = Ls) by exact (texts_lines _ _ MX ZR).
    destruct (SKU E0) as [Hsk HUw].
    pose proof (reads_bound e h Hsk HUw Hov HUl) as RB. fold Ls in RB.
    pose proof (lines_count Ls) as LC.
    assert (LN : hl_n (hs_expected h'') = Z.of_nat (length Ls)).
    { unfold hl_n. apply (f_equal (@length _)) in MX. rewrite !length_map in MX. rewrite MX. reflexivity. }
    assert (SK6 : (if re_skip e =? 0 then re_used e else 0) <= 6000) by (destruct (re_skip e =? 0); lia).
    split; [exact SRC'|]. split; [exact HJ|]. split; [rewrite FD'', FD'; exact FD|].
    split; [intros _; split; [exact SK'|exact SKU']|].
    split; [exact MX|]. split; [exact ZR|]. split; [exact GC1|]. split; [exact NDK|].
    split; [rewrite HLD; eapply same_set_trans; [exact SSK|apply upds_same_set; exact SS]|].
    split; [exact GK|]. split; [rewrite TX in GC3; exact GC3|].
    split; [unfold hl_n; rewrite PND; cbn [length Z.of_nat]; lia|].
    split; [rewrite PCAP; exact PC|].
    split; [unfold pending_stream; rewrite PND; cbn [length Z.of_nat]; unfold WRITE_MAX; lia|].
    split; [rewrite ECE; exact (HEC E0)|].
    rewrite HLD. exact HC.
  - assert (G5 : g5_src e h h'' = h) by (unfold g5_src; rewrite (proj2 (Z.eqb_neq _ _) E1); reflexivity).
    assert (EL : entry_lines e (h, j) = []) by (unfold entry_lines; cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) E1); reflexivity).
    assert (EOF1 : re_eof e' = 1) by (rewrite EOF'; reflexivity).
    destruct (g5_counts B L A mem t es hjs e (h, j) h'' k k HF Hin HP Hc (Z.le_refl k) Hk
      (fun X => False_ind _ (E1 X))) as (GC1 & _ & GC3).
    cbn [fst] in GC1, GC3. rewrite G5 in GC1, GC3 |- *. rewrite EL in SSK |- *.
    unfold texts in GC3. rewrite HE0 in GC3. cbn [map] in GC3.
    split; [exact (SRC1 E1)|]. split; [exact HJ|]. split; [rewrite FD'; exact FD|].
    split; [intros X; rewrite EOF1 in X; discriminate|].
    split; [rewrite HE0; reflexivity|]. split; [constructor|]. split; [exact GC1|]. split; [exact NDK|].
    split; [eapply same_set_trans; [exact SSK|apply upds_same_set; exact SS]|].
    split; [exact GK|]. split; [exact GC3|].
    split; [exact PN|]. split; [exact PC|]. split; [exact PS|]. split; [exact EC|]. exact HC.
Qed.

Lemma p5c_cost : forall (rc : RunCeil) B L A mem L' A' mem' t pre (e e' : rentry) (p : hsrc * nat) (h'' : hsrc) ks
    (ec : Z),
  CF.RelayRep.entry_ok B L A mem e -> CF.RelayRep.entry_ok B L' A' mem' e' ->
  pair_ok (rc := rc) B L A mem t e p ->
  NoDup ks -> same_set ks (upds (keys_texts (re_keys e)) (entry_lines e p)) ->
  keys_texts (re_keys e') = snd (gei pre ks) ->
  (re_eof e = 0 ->
     src_at B L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd p)) h'' /\
     hs_fd h'' = hs_fd (fst p) /\ hs_closed h'' = hs_closed (fst p) /\
     hs_eintr h'' = 0 /\ hl_recs (hs_pending h'') = [] /\
     hl_cap (hs_pending h'') = hl_cap (hs_pending (fst p)) /\ hl_v (hs_pending h'') = hl_v (hs_pending (fst p)) /\
     hs_off h'' = 0 /\
     hs_state h'' = feed (hs_state (fst p)) (bzs (pending_stream (fst p))) /\
     map snd (hl_recs (hs_expected h'')) = map snd (hl_recs (hs_expected (fst p))) ++
       map (map (Z_to_bv 8)) (entry_lines e p) /\
     firstn (length (hl_recs (hs_expected (fst p)))) (hl_recs (hs_expected h'')) = hl_recs (hs_expected (fst p)) /\
     hs_held h'' = hs_held (fst p) /\
     re_skip e' = hs_overlong h'' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h'')) /\
     hl_cap (hs_expected h'') = ec /\
     hl_cap (hs_expected h'') <= Z.max 8 (Z.max (hl_cap (hs_expected (fst p))) (2 * hl_n (hs_expected h'')))) ->
  (re_eof e = 1 -> re_skip e' = re_skip e /\ re_U e' = re_U e /\ re_buf e' = re_buf e /\ re_used e' = re_used e /\
     re_cap e' = re_cap e) ->
  pair_cost e' (g5_src e (fst p) h'', snd p) <= pair_cost e p.
Proof.
  intros rc B L A mem L' A' mem' t pre e e' p h'' ks ec EOK EOK' HP NDK SSK GK D0 D1.
  destruct p as [h j]. cbn [fst snd] in *.
  pose proof HP as HP'. unfold pair_ok in HP'. cbv zeta in HP'. cbn [fst snd] in HP'.
  destruct HP' as (SRC & HJ & FD & SKU & SS & NDH & HE0 & _).
  pose proof (p5c_keys pre ks (re_keys e) (re_keys e') (entry_lines e (h, j)) NDK SSK GK) as KB.
  pose proof EOK as (EF & _ & _ & _ & _ & _ & HUl & _).
  pose proof EOK' as (_ & _ & _ & _ & _ & _ & HUl' & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hov & _).
  unfold pair_cost. cbn [fst].
  destruct EF as [E0|E1].
  - destruct (D0 E0) as (SRC' & _ & _ & _ & PND & _ & _ & _ & HST & _ & _ & _ & SK' & SKU' & _ & _).
    assert (G5 : g5_src e h h'' = h'') by (unfold g5_src; rewrite E0; reflexivity). rewrite G5.
    unfold entry_lines in KB. cbn [fst] in KB. rewrite E0 in KB. cbn [Z.eqb] in KB.
    pose proof SRC' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hov' & _).
    destruct (SKU E0) as [Hsk HUw].
    rewrite <- (hs_wcost e' h'' SK' SKU' Hov' HUl'), <- (hs_wcost e h Hsk HUw Hov HUl), HST.
    assert (PS0 : pending_stream h'' = []) by (unfold pending_stream; rewrite PND; reflexivity).
    rewrite PS0. pose proof (lines_bytes (bzs (pending_stream h)) (hs_state h)) as LB. rewrite bzs_length in LB.
    cbn [length Z.of_nat]. lia.
  - destruct (D1 E1) as (SK1 & _ & _ & U1 & _).
    assert (G5 : g5_src e h h'' = h) by (unfold g5_src; rewrite E1; reflexivity). rewrite G5.
    unfold entry_lines in KB. cbn [fst] in KB. rewrite E1 in KB. cbn [Z.eqb with_nul map concat length Z.of_nat] in KB.
    rewrite SK1, U1. lia.
Qed.

Section P5K.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BW : blocks_writable B API.
Hypothesis IMG : forall a, 0x30fc0 <= a < 0x311c0 -> in_img B a.

Definition p5c_E (OUT CAP G : Z) (es : list rentry) (hs : list (hsrc * nat)) (L : layout) (A : astate) (a : Z)
    : Prop :=
  send_writes true OUT CAP a \/ relay_event_c.G_LOCK + 4 <= a < relay_event_c.G_LOCK + 8 \/
  G <= a < G + SRC_TABLE \/ drained_area es hs a \/
  (exists q m, In q (concat (map entry_blocks es) ++ drained_blocks es hs) /\ In (q, m) (blocks L A) /\
               q <= a < q + m).

Definition p5c_F (live : bool) (OUT : Z) (es : list rentry) (hs : list (hsrc * nat)) (q : Z) : Prop :=
  (live = true /\ q = OUT) \/ In q (concat (map entry_blocks es)) \/ In q (drained_blocks es hs).

Lemma p5c_Ew : forall L A mem md OUT CAP G es hs a,
  aa_MR API L A mem md -> (0 < CAP -> fresh_block B OUT CAP) -> fresh_block B G SRC_TABLE ->
  (forall p, In p hs -> (snd p < 4)%nat) ->
  p5c_E OUT CAP G es hs L A a -> (0x30fc0 <= a < 0x311c0) \/ (~ in_img B a /\ a < YM05.alloc_ceiling).
Proof.
  intros L A mem md OUT CAP G es hs a HM OFR GFR HS X.
  destruct X as [X|[X|[X|[X|(q & m & Hq & Hin & Ha)]]]].
  - unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]];
      try (left; unfold G_BROKEN, G_EINTR, G_OUTV in X; lia).
    destruct (OFR ltac:(lia)) as (F1 & F2 & F3). right.
    split; [replace a with (OUT + (a - OUT)) by lia; apply F3; lia|lia].
  - left. unfold relay_event_c.G_LOCK in X. lia.
  - destruct GFR as (F1 & F2 & F3). right.
    split; [replace a with (G + (a - G)) by lia; apply F3; lia|lia].
  - left. pose proof (p5c_da_lo es hs a X). pose proof (p5c_da_hi es hs a HS X). unfold G_S in *. lia.
  - right. split; [replace a with (q + (a - q)) by lia; exact (hf_blk_img B API AX L A mem md q m (a - q) HM Hin ltac:(lia))|].
    unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & EQ & Hp). cbn [fst snd] in EQ.
    injection EQ as EQ1 EQ2. subst q m.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n (a - ptr_addr L p) HM Hp ltac:(lia)) as (_ & B0 & B1 & _).
    lia.
Qed.

Lemma p5c_E_img : forall L A mem md OUT CAP G es hs a,
  aa_MR API L A mem md -> (0 < CAP -> fresh_block B OUT CAP) -> fresh_block B G SRC_TABLE ->
  p5c_E OUT CAP G es hs L A a -> in_img B a ->
  a = 0x30fc4 \/ a = 0x30fd0 \/ 0x31000 <= a < 0x31018 \/ 0x3101c <= a < 0x31020 \/ drained_area es hs a.
Proof.
  intros L A mem md OUT CAP G es hs a HM OFR GFR X HI.
  destruct X as [X|[X|[X|[X|(q & m & Hq & Hin & Ha)]]]].
  - unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]];
      try (unfold G_BROKEN, G_EINTR, G_OUTV in X; lia).
    destruct (OFR ltac:(lia)) as (F1 & F2 & F3). exfalso. apply (F3 (a - OUT)); [lia|].
    replace (OUT + (a - OUT)) with a by lia. exact HI.
  - unfold relay_event_c.G_LOCK in X. lia.
  - destruct GFR as (F1 & F2 & F3). exfalso. apply (F3 (a - G)); [lia|].
    replace (G + (a - G)) with a by lia. exact HI.
  - right. right. right. right. exact X.
  - exfalso. apply (hf_blk_img B API AX L A mem md q m (a - q) HM Hin ltac:(lia)).
    replace (q + (a - q)) with a by lia. exact HI.
Qed.

Lemma p5c_kept : forall L A mem md OUT CAP G es hs live q,
  aa_MR API L A mem md ->
  In (G, SRC_TABLE) (blocks L A) -> (0 < CAP -> In (OUT, CAP) (blocks L A)) ->
  (forall p, In p hs -> (snd p < 4)%nat) ->
  q <> G -> q <> OUT -> ~ In q (concat (map entry_blocks es)) -> ~ In q (drained_blocks es hs) ->
  kept_block (p5c_E OUT CAP G es hs L A) (p5c_F live OUT es hs) L A q.
Proof.
  intros L A mem md OUT CAP G es hs live q HM GIN OIN HS NG NO NE ND.
  split.
  { intros [(_ & X)|[X|X]]; [exact (NO X)|exact (NE X)|exact (ND X)]. }
  intros m i Hin Hi X.
  assert (NI : ~ in_img B (q + i)) by exact (hf_blk_img B API AX L A mem md q m i HM Hin Hi).
  destruct X as [X|[X|[X|[X|(q' & m' & Hq' & Hin' & Ha)]]]].
  - unfold send_writes in X. destruct X as [X|[X|[X|(_ & X)]]];
      try (apply NI, IMG; unfold G_BROKEN, G_EINTR, G_OUTV in X; lia).
    destruct (blocks_disjoint B API L A mem md q m OUT CAP HM Hin (OIN ltac:(lia)) NO); lia.
  - apply NI, IMG. unfold relay_event_c.G_LOCK in X. lia.
  - destruct (blocks_disjoint B API L A mem md q m G SRC_TABLE HM Hin GIN NG); lia.
  - apply NI, IMG. pose proof (p5c_da_lo es hs (q + i) X). pose proof (p5c_da_hi es hs (q + i) HS X).
    unfold G_S in *. lia.
  - assert (Nq : q <> q') by (intros ->; apply in_app_iff in Hq' as [Y|Y]; [exact (NE Y)|exact (ND Y)]).
    destruct (blocks_disjoint B API L A mem md q m q' m' HM Hin Hin' Nq); lia.
Qed.

Lemma p5c_eb_pos : forall L A mem (es : list rentry) q, Forall (CF.RelayRep.entry_ok B L A mem) es ->
  In q (concat (map entry_blocks es)) -> exists k, 0 < k /\ In (q, k) (blocks L A).
Proof.
  intros L A mem es q ES HQ. apply in_concat in HQ as (l0 & Hl0 & Hq). apply in_map_iff in Hl0 as (e & <- & He).
  rewrite Forall_forall in ES. destruct (ES e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BU & _ & HP & _ & _ & KS).
  unfold entry_blocks in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (Z.eqb_spec (re_cap e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct BU as [(X & _)|(HC & IN & _)]; [lia|]. exists (re_cap e). split; [exact HC|exact IN].
  - apply in_app_iff in Hq as [Hq|Hq].
    + destruct (Z.eqb_spec (re_hp e) 0) as [C0|C0]; [destruct Hq|]. destruct Hq as [<-|[]].
      destruct HP as [(X & _)|(IN & _ & _ & HH & _)]; [lia|]. exists (re_kh e). split; [lia|exact IN].
    + apply in_map_iff in Hq as (kk & <- & Hk). rewrite Forall_forall in KS. destruct (KS kk Hk) as (IN & _).
      exists (Z.of_nat (length (key_text kk)) + 1). split; [lia|exact IN].
Qed.

Lemma p5c_driver : forall E0 TA TA' K sp Ew Fw L A mem md L' A' mem' md' (lb lb' : list Z),
  WF A -> List.NoDup (map fst (blocks L A)) ->
  driver_kept B E0 TA L A mem ->
  rmid B API K sp Ew Fw L A mem md L' A' mem' md' ->
  (0 < ss_n E0 -> exists q, In (q, ss_n E0) (user_blocks (ss_A E0)) /\ ptr_addr (ss_L E0) q = ss_p E0) ->
  (0 < ss_n E0 -> ~ In (ss_p E0, ss_n E0) (ss_T E0)) ->
  (forall q, In q lb -> In q TA) ->
  (forall q, In q lb' -> In q TA') ->
  (forall q m, In (q, m) (blocks L A) -> In q TA -> ~ In q lb -> In q TA') ->
  (forall q, In q TA' -> In q TA \/ In q lb') ->
  (forall q, In q lb -> exists k, 0 < k /\ In (q, k) (blocks L A)) ->
  (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ (0 < m -> ~ In q lb)) \/ In q lb') ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q lb -> ~ In q lb') ->
  (forall q, ~ In q TA -> kept_block Ew Fw L A q) ->
  driver_kept B E0 TA' L' A' mem'.
Proof.
  intros E0 TA TA' K sp Ew Fw L A mem md L' A' mem' md' lb lb' HW NDB (D1 & D2 & D3 & D4) R INP INT
    LBT LBT' KEEP BACK LBP NEWB NEWN KPT.
  pose proof R as (_ & _ & _ & _ & _ & PA & SV & Z0 & _ & _ & _ & BK & _).
  assert (BL : forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A)).
  { intros p n Hp. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hp). }
  assert (KB : forall X m i, In (X, m) (blocks L A) -> ~ In X TA -> 0 <= i < m ->
      mbyte (ms_segs B) mem' (X + i) = mbyte (ms_segs B) mem (X + i)).
  { intros X m i Hin NT Hi. destruct (KPT X NT) as (NF & NE).
    exact (proj1 (proj2 (rmid_block B API BW K sp Ew Fw L A mem md L' A' mem' md' X m i R Hin ltac:(lia) NF Hi
                           (NE m i Hin Hi)))). }
  split.
  { intros q m Hq HT. destruct (D1 q m Hq HT) as (HN & q' & Hq' & Eq').
    pose proof (CF.SlotEntry.entry_ub_nonneg _ _ _ HW Hq') as M0.
    split.
    - intros Hm X. destruct (BACK _ X) as [X1|X1]; [exact (HN Hm X1)|].
      apply (NEWN (ptr_addr (ss_L E0) q) m); [rewrite <- Eq'; exact (BL q' m Hq')|exact Hm| |exact X1].
      intros X2. exact (HN Hm (LBT _ X2)).
    - destruct (Z.eq_dec m 0) as [->|NZ].
      + destruct (Z0 q' Hq') as (Hq'' & Ep). exists q'. split; [exact Hq''|]. rewrite Ep. exact Eq'.
      + assert (Hm : 0 < m) by lia.
        destruct (KPT _ (HN Hm)) as (NF & _). rewrite <- Eq' in NF.
        pose proof (SV q' m Hq' Hm NF) as Hq''. exists q'. split; [exact Hq''|].
        rewrite (PA q' m Hq' Hq'' NF). exact Eq'. }
  split.
  { intros q m i Hq HT HP Hi. destruct (D1 q m Hq HT) as (HN & q' & Hq' & Eq').
    rewrite (KB (ptr_addr (ss_L E0) q) m i ltac:(rewrite <- Eq'; exact (BL q' m Hq')) (HN ltac:(lia)) Hi).
    exact (D2 q m i Hq HT HP Hi). }
  split.
  { intros i Hi. destruct (INP ltac:(lia)) as (q & Hq & Eq).
    destruct (D1 q (ss_n E0) Hq ltac:(rewrite Eq; exact (INT ltac:(lia)))) as (HN & q' & Hq' & Eq').
    rewrite Eq in Eq', HN.
    rewrite (KB (ss_p E0) (ss_n E0) i ltac:(rewrite <- Eq'; exact (BL q' _ Hq')) (HN ltac:(lia)) Hi).
    exact (D3 i Hi). }
  intros q m Hq. destruct (NEWB q m Hq) as [(Hold & Hm)|Hn]; [|right; exact (LBT' q Hn)].
  destruct (D4 q m Hold) as [X|X]; [left; exact X|right].
  destruct (in_dec Z.eq_dec q lb) as [IL|IL]; [|exact (KEEP q m Hold X IL)].
  exfalso. destruct (LBP q IL) as (kk & Hk & Hin).
  pose proof (hg_nodup_fst _ q m kk NDB Hold Hin) as ->. exact (Hm Hk IL).
Qed.

End P5K.

Definition p5c_lss (es : list rentry) (hj : list (hsrc * nat)) : list (list (list Z)) :=
  map (fun i => entry_lines (nth i es no_entry) (nth i hj no_hj)) (seq 0 (length es)).

Lemma p5c_hj_nth : forall es hj hs' i, (i < length es)%nat ->
  nth i (p5c_hj es hj hs') no_hj =
    (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj)), snd (nth i hj no_hj)).
Proof. intros es hj hs' i Hi. unfold p5c_hj. rewrite p5c_nth_seq by exact Hi. reflexivity. Qed.

Lemma p5c_hj_len : forall es hj hs', length (p5c_hj es hj hs') = length es.
Proof. intros. unfold p5c_hj. rewrite length_map, length_seq. reflexivity. Qed.

Lemma p5c_hj_snd : forall es hj hs', length hj = length es -> map snd (p5c_hj es hj hs') = map snd hj.
Proof.
  intros es hj hs' LH. unfold p5c_hj. rewrite map_map. rewrite (p5c_map_seq snd hj no_hj), LH. reflexivity.
Qed.

Lemma p5c_hj_blocks : forall es hj hs',
  concat (map (fun p => hs_blocks (fst p)) (p5c_hj es hj hs')) =
  concat (map (fun i => hs_blocks (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj))))
    (seq 0 (length es))).
Proof. intros. unfold p5c_hj. rewrite map_map. reflexivity. Qed.

Lemma p5c_hj_pend : forall es hj hs',
  pend_view (p5c_hj es hj hs') =
  map (fun i => map snd (hl_recs (hs_pending (g5_src (nth i es no_entry) (fst (nth i hj no_hj))
    (nth i hs' (fst no_hj)))))) (seq 0 (length es)).
Proof. intros. unfold pend_view, p5c_hj. rewrite map_map. reflexivity. Qed.

Lemma p5c_lss_nth : forall es hj i, (i < length es)%nat ->
  nth i (p5c_lss es hj) [] = entry_lines (nth i es no_entry) (nth i hj no_hj).
Proof. intros es hj i Hi. unfold p5c_lss. rewrite p5c_nth_seq by exact Hi. reflexivity. Qed.

Lemma p5c_segs : forall P es hj kss, l2_segs P (p5c_lss es hj) kss (length es) = g5_segs (bzs P) es hj kss.
Proof.
  intros P es hj kss. unfold l2_segs, g5_segs. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  rewrite p5c_lss_nth by lia. reflexivity.
Qed.

Lemma p5c_in_opt : forall (c : bool) (x q : Z) R, In q ((if c then [x] else []) ++ R) <-> (c = true /\ q = x) \/ In q R.
Proof.
  intros c x q R. destruct c; cbn [app In].
  - split; [intros [<-|H]; [left; split; reflexivity|right; exact H]|intros [(_ & ->)|H]; [left; reflexivity|right; exact H]].
  - split; [intros H; right; exact H|intros [(X & _)|H]; [discriminate|exact H]].
Qed.

Lemma p5c_nd3 : forall (a b q : Z) X Y, List.NoDup (a :: b :: X ++ Y) -> In q Y -> q <> a /\ q <> b /\ ~ In q X.
Proof.
  intros a b q X Y ND HY. inversion ND as [|? ? N0 N1]; subst. inversion N1 as [|? ? N2 N3]; subst.
  split; [intros ->; apply N0; right; apply in_or_app; right; exact HY|].
  split; [intros ->; apply N2; apply in_or_app; right; exact HY|].
  intros HX. exact (hf_nodup_disj X Y q N3 HX HY).
Qed.

Lemma p5c_old_src : forall (G OUT : Z) (es : list rentry) (hj : list (hsrc * nat)) i q,
  List.NoDup (G :: OUT :: concat (map entry_blocks es) ++
    concat (map (fun i0 => hs_blocks (fst (nth i0 hj no_hj))) (seq 0 (length es)))) ->
  (i < length es)%nat -> re_eof (nth i es no_entry) <> 0 -> In q (hs_blocks (fst (nth i hj no_hj))) ->
  q <> G /\ q <> OUT /\ ~ In q (concat (map entry_blocks es)) /\
  ~ In q (concat (map (fun i0 => if re_eof (nth i0 es no_entry) =? 0 then hs_blocks (fst (nth i0 hj no_hj)) else [])
    (seq 0 (length es)))).
Proof.
  intros G OUT es hj i q ND Hi E1 Hq.
  assert (QC : In q (concat (map (fun i0 => hs_blocks (fst (nth i0 hj no_hj))) (seq 0 (length es)))))
    by (apply p5c_in_cs; exists i; split; [exact Hi|exact Hq]).
  destruct (p5c_nd3 G OUT q _ _ ND QC) as (N1 & N2 & N3).
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
  intros QD. apply p5c_in_cs in QD as (i0 & Hi0 & Q0).
  destruct (Z.eqb_spec (re_eof (nth i0 es no_entry)) 0) as [E0|E0]; [|destruct Q0].
  assert (Ne : i0 <> i) by (intros ->; exact (E1 E0)).
  exact (p5c_nd_idx (fun i0 => hs_blocks (fst (nth i0 hj no_hj))) (seq 0 (length es)) i0 i q (seq_NoDup _ _)
    (NoDup_app_remove_l (G :: OUT :: concat (map entry_blocks es)) _ ND) ltac:(apply in_seq; lia)
    ltac:(apply in_seq; lia) Ne Q0 Hq).
Qed.

Ltac p5c_gunf := unfold CF.relay_finish_b_c.G_LISTEN, G_CLIENT, G_WAKE0, Statement.G_THREAD_UP,
  CF.relay_finish_b_c.G_THREAD_UP, G_BROKEN, CheckRep.G_GONE, G_DEAD, G_EINTR, Statement.G_NSRC, CF.relay_add_b_c.G_NSRC,
  CF.op_add_c.G_NFD, CF.StatementKept.G_SRC, CF.relay_add_b_c.G_SRC, G_OUTV, Statement.G_LOCK, relay_event_c.G_LOCK,
  Statement.G_S, HarnessRep.G_S, G_RELAY_LO.

Ltac p5c_frame PLG NEg :=
  let i0 := fresh "i" in let Hi0 := fresh "Hi" in
  intros i0 Hi0; cbn [cells_size csize Nat.add] in Hi0; p5c_gunf;
  match goal with |- img_plain ?B ?a /\ _ =>
    let HPx := fresh "HPx" in assert (HPx : img_plain B a) by (apply PLG; lia);
    split; [exact HPx|]; apply NEg; [exact (proj1 HPx)|lia..] end.

Lemma p5c_ecap_fin : forall (rc : RunCeil) B L A mem t lv mx NO CAP pre (es : list rentry) (hj : list (hsrc * nat)) i,
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj -> 0 <= t < OPS_MAX ->
  (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
  ecap_ok (ds_ecap (nth i (gone_states lv mx NO CAP pre es hj)
    (drain_init NO CAP (nth i es no_entry) (fst (nth i hj no_hj))))).
Proof.
  intros rc B L A mem t lv mx NO CAP pre es hj i PA Ht Hi E0.
  pose proof (Forall2_length PA) as LH.
  pose proof (g5_forall2_nth _ _ _ no_entry no_hj PA i Hi) as PK.
  unfold gone_states.
  destruct (g5m_gs_after lv mx pre (combine es hj) NO CAP (fun _ => adr0) 0%nat adr0 i
    (drain_init NO CAP (nth i es no_entry) (fst (nth i hj no_hj))) ltac:(rewrite length_combine; lia))
    as (no' & cap' & EQ).
  rewrite EQ, combine_nth by exact LH. cbn [fst snd].
  rewrite (after_drain_fin lv mx no' cap' _ _ E0).
  revert PK. destruct (nth i hj no_hj) as [h jj]. cbn [fst]. intros PK.
  unfold pair_ok in PK. cbv zeta in PK. cbn [fst snd] in PK.
  destruct PK as (SRC & _ & _ & _ & _ & _ & HE0 & _ & _ & PS & EC & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & OFF & _).
  apply drain3_ecap; [destruct OFF as [(_ & ->)|(r & rs & _ & O1 & _)]; lia|exact EC|].
  unfold hl_n. rewrite HE0. cbn [length Z.of_nat]. unfold WRITE_MAX, OPS_MAX in *. lia.
Qed.

Section P5C.
Hypothesis HRES : (p5c_res3_fullN GSF RM_ag).
Hypothesis HV1 : p5v_cnt_S.
Hypothesis HV2 : p5v_ncs_S.
Hypothesis HV3 : p5v_wt_S.
Hypothesis HV4 : p5v_pend_S.
Hypothesis HV5 : p5v_ekc_S.
Hypothesis HV6 : p5v_ekb_S.
Hypothesis HV7 : p5v_old_S.
Hypothesis HV8 : p5v_out_S.
Hypothesis HV9 : p5v_chain_S.

Lemma p5_call : forall B API LS SH SK ra empty rc fx j E CS t k c,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  gone_partial_S rc B (API rc) ->
  J1 (rc := rc) B (API rc) E (RI3P GSF) t k c ->
  SR (ms_segs B) c (J2 (rc := rc) B (API rc) E (RI3P GSF) t k).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS t k c HF HRG HJ.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (FG : forall a, in_globals frame_G a -> img_plain B a) by (unfold frame_facts, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL rc fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (BLOW : blocks_low B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31290) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (GD : ms_got_guard B = 0x1fcf8) by (unfold frame_facts in FF; tauto).
  assert (GG : ms_guard B = 0x51500) by (unfold frame_facts in FF; tauto).
  assert (EA : errno_addr B = 0x311ec) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by exact FG.
  assert (PLG : forall a, 0x30fc0 <= a < 0x311c0 \/ 0x20d38 <= a < 0x20d48 -> img_plain B a).
  { intros a [Ha|Ha]; apply FG; [apply in_G_bss; lia|exists 0x20d38, 16; split; [left; reflexivity|lia]]. }
  assert (IMG : forall a, 0x30fc0 <= a < 0x311c0 -> in_img B a)
    by (intros a Ha; exact (proj1 (PLG a (or_introl Ha)))).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof PRE as ((LPRE & LEN & BD & _) & _ & _ & _ & _ & _ & NIT & _).
  pose proof LPRE as (_ & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TP & _ & _ & _ & INPUT & _).
  assert (TS : spZ (ss_regs E) <= TASK_SIZE).
  { pose proof PRE as PT. do 9 (destruct PT as [_ PT]). destruct PT as (TS & _). exact TS. }
  assert (KV : 0 <= RELAY_INSTANCE_GONE_K <= 20000) by (split; apply Z.leb_le; vm_compute; reflexivity).
  assert (INP : 0 < ss_n E -> exists q, In (q, ss_n E) (user_blocks (ss_A E)) /\ ptr_addr (ss_L E) q = ss_p E).
  { intros HN. destruct INPUT as [(X & _)|(_ & q0 & Hq0 & Eq0)]; [lia|exists q0; split; assumption]. }
  destruct HJ as (id & fs & os & rs & junk & HM & HST1).
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x13efc =? TAIL_CHECK) || (0x13efc =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  assert (Hnfd' : 0 <= nfd <= t + 1) by (revert Hnfd; unfold TAIL_CHECK, TAIL_STEP; cbn; lia). clear Hnfd.
  destruct HR as (Hno & TR & Hid & R9 & R10 & HRS).
  pose proof TR as ((B2 & B3 & B4 & B20) & (F19 & F21 & F24 & F25 & F26 & F27) & R8 & R23 & R22).
  destruct HST1 as (SLW & SLR & REC & Z32 & C40).
  cbn [cfg_ms ms_mem YK11.mkst] in SLW, SLR, REC, Z32, C40.
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HREL as ((tail & TAB) & GIN & GFR & HES & HND & HFD & HPA & NDH & ZH & NDA).
  pose proof HGL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & ER & RCL & RBR & RGN &
    RDD & REI & GNC & MXB).
  pose proof HOUT as ((O & junk0 & HO) & HCAPB).
  assert (LHJ : length hj = length es) by (symmetry; exact (Forall2_length HPA)).
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply p5c_jal. }
  intros ms1 (can1 & -> & EQ1).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  rewrite <- SEG.
  assert (G1 : getr R1 1 = Z_to_bv 64 0x13f00) by geq X1.
  assert (GR : forall r, callee_saved r -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. unfold callee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r; geq X1|]); subst r; geq X1. }
  assert (G10 : getr R1 10 = Z_to_bv 64 id) by (rewrite <- R10; geq X1).
  assert (G1y : YK11.getr R1 1 = Z_to_bv 64 0x13f00) by exact G1.
  assert (G2 : getr R1 2 = Z_to_bv 64 (slot_sp E)) by (rewrite <- B2; exact (GR 2 ltac:(unfold callee_saved; lia))).
  assert (G2y : YK11.getr R1 2 = Z_to_bv 64 (slot_sp E)) by exact G2.
  assert (G4 : getr R1 4 = getr (ss_regs E) 4) by (rewrite <- B4; exact (GR 4 ltac:(unfold callee_saved; lia))).
  assert (G4y : YK11.getr R1 4 = getr (ss_regs E) 4) by exact G4.
  assert (SPR : spZ R1 = slot_sp E)
    by (unfold spZ; rewrite G2y; apply unsigned_lit; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (SID : bv_signed (getr R1 10) = id).
  { rewrite G10, ZBridge.zb_signed, unsigned_lit by lia.
    replace (id <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  assert (SIDy : bv_signed (YK11.getr R1 10) = id) by exact SID.
  set (fs4 := map (fun i => nth i fs 0) (seq 0 4)).
  set (os4 := map (fun i => nth i os 0) (seq 0 4)).
  assert (NF4 : forall i, (i < 4)%nat -> nth i fs4 0 = nth i fs 0)
    by (intros i Hi; exact (p5c_nth_seq (fun i => nth i fs 0) 4 i 0 Hi)).
  assert (NO4 : forall i, (i < 4)%nat -> nth i os4 0 = nth i os 0)
    by (intros i Hi; exact (p5c_nth_seq (fun i => nth i os 0) 4 i 0 Hi)).
  destruct (g5_slot_words B L A mem t nfd G (bv_unsigned out) es hj fs os HREL SLW SLR) as [SW1 SW2].
  assert (CAPR : 0 <= bv_unsigned cap <= TBBYTES)
    by (pose proof (bv_unsigned_in_range 64 cap) as CR; unfold bv_modulus in CR; lia).
  assert (MXR : 0 <= bv_unsigned mx <= 255)
    by (pose proof (bv_unsigned_in_range 64 mx) as CR; unfold bv_modulus in CR; lia).
  assert (NDL : List.NoDup (map fst (blocks L A))) by exact (proj1 (hf_nodup _) (NDB L A mem md HMR)).
  destruct (HRES E k k L A G (bv_unsigned out) es hj (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout)
    (bv_unsigned cap) (instance_prefix id) HRI (Z.le_refl k) LHJ Hes (proj1 MXR) (proj1 CAPR)
    (g5m_d3_facts (rc := rc) B L A mem t G (bv_unsigned out) es hj k HES HPA Hcost ltac:(lia) Ht
      (p5c_src_ok rc B L A mem t G (bv_unsigned out) es hj k HES HPA Hcost ltac:(lia)))
    ltac:(rewrite Hno; exact (g5m_gone_cap (rc := rc) B L A mem t (send_live cl br dd 1) (bv_unsigned mx)
      (bv_unsigned cap) (instance_prefix id) es hj k HES HPA Hcost ltac:(lia) CAPR))
    (g5m_hp_kh (rc := rc) B L A mem es hj HES) NDL
    ltac:(intros HC0 m0 X0; destruct HO as [(_ & XO & _)|(XC & _)];
      [rewrite XO in X0; exact (nw_no_zero B (API rc) L A mem md HMR m0 X0)|lia])
    ltac:(lia) GIN
    ltac:(destruct HO as [(XC & _)|(_ & _ & XI & _)]; [left; exact XC|right; exact XI])
    ltac:(eapply Forall_impl; [|exact HES]; intros e0 He0; exact (CF.SlotPass4.p4_ent_blk_of B L A mem e0 He0))
    ltac:(clear - HPA; induction HPA as [|e0 p0 es0 hj0 HP0 _ IH]; constructor;
      [destruct HP0 as (HS0 & _); exact (CF.SlotPass4.p4_src_blk_of B L A mem _ (fst p0) HS0)|exact IH]))
    as (bnd & ROK & ROOM & RIK).
  eapply SR_bind.
  { apply (HRG fx' L A R1 mem md bnd es G tail hj fs4 os4 O junk0 cl br dd ei mx nout cap out).
    - exact SEG.
    - split.
      + unfold call_pre_k. rewrite ?SPR.
        split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|].
        split; [rewrite ?G1, ?G1y; unfold YK0s.ret_ok; vm_compute; reflexivity|].
        split; [unfold slot_sp, SLOT_FRAME; lia|].
        split; [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|].
        split; [unfold slot_sp, SLOT_FRAME in *; lia|].
        split.
        { intros a Ha. apply (proj2 (proj2 (proj2 HIK))). left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
        split; [rewrite ?G4, ?G4y; exact TP|].
        split; [intros a Ha; apply (proj2 (proj2 (proj2 HIK))); right; exact Ha|].
        intros X. rewrite HINIT in X. discriminate.
      + rewrite SPR. unfold slot_sp, SLOT_FRAME in *. lia.
    - exact HINIT.
    - unfold errno_addr, ERRNO_OFF. rewrite EOFF. reflexivity.
    - rewrite EA. unfold G_LOCK_HI. lia.
    - exact HRO.
    - exact FZ.
    - rewrite GD. reflexivity.
    - rewrite GG. reflexivity.
    - intros a Ha. apply PLG. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in Ha. lia.
    - intros a Ha. apply PLG. unfold G_CLIENT in Ha. lia.
    - intros a Ha. exact (proj1 (entry_errno_image B SEG ETP EOFF a Ha)).
    - exact (fin_end5 B API LS SH SK ra empty FF).
    - rewrite ?SID, ?SIDy. lia.
    - exact Q12.
    - exact Q8.
    - exact Q10.
    - lia.
    - exact GIN.
    - exact GFR.
    - exact TAB.
    - exact HES.
    - exact HND.
    - exact LHJ.
    - unfold fs4. rewrite length_map, length_seq. reflexivity.
    - unfold os4. rewrite length_map, length_seq. reflexivity.
    - intros i Hi. rewrite NF4, NO4 by exact Hi. exact (SLW i Hi).
    - intros i i' Hi Hi' Ne. rewrite !NF4, !NO4 by assumption.
      exact (p5c_fds rc B L A mem t es hj fs os i i' HPA HND SW1 SW2 Hi Hi' Ne).
    - intros i Hi. rewrite NF4, NO4 by exact Hi. exact (SLR i Hi).
    - exact (p5c_src_ok rc B L A mem t G (bv_unsigned out) es hj k HES HPA Hcost ltac:(lia)).
    - apply hf_nodup. apply hf_nodup in NDA. unfold target_addrs in NDA.
      rewrite (p5c_combine_seq (fun p => if re_eof (fst p) =? 0 then hs_blocks (fst (snd p)) else []) es hj
        no_entry no_hj (eq_sym LHJ)).
      rewrite (p5c_map_seq (fun p => hs_blocks (fst p)) hj no_hj), LHJ in NDA.
      apply (p5c_nd_sub (G :: bv_unsigned out :: concat (map entry_blocks es))
        (fun i => hs_blocks (fst (nth i hj no_hj)))); [|exact NDA].
      intros i _. cbn beta. cbn [fst snd]. destruct (re_eof (nth i es no_entry) =? 0); [left|right]; reflexivity.
    - exact RCL.
    - exact RBR.
    - exact RDD.
    - exact REI.
    - pose proof (hg_cut _ _ _ [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)] Q1) as [_ Q1b].
      replace G_CLIENT with (CF.relay_finish_b_c.G_LISTEN + Z.of_nat (cells_size [C4 (Z_to_bv 64 (-1))]))
        by reflexivity.
      exact Q1b.
    - exact Q4.
    - exact Q6.
    - exact Q7.
    - exact Q11.
    - exact ER.
    - exact HO.
    - exact ROK.
    - rewrite ?SID, ?SIDy. exact ROOM. }
  intros c' HP.
  destruct HP as (fx2 & L' & A' & regs' & mem' & md' & OUT' & CAP' & junk' & LB & es' & hs' & kss & tail' & HP).
  cbv zeta in HP. rewrite ?SID, ?SIDy in HP.
  fold (g5_segs (instance_prefix id) es hj kss) in HP.
  set (TOT := Z.of_nat (length (concat (g5_segs (instance_prefix id) es hj kss)))) in HP.
  destruct HP as (-> & FZ2 & RP & INIT' & (qs & LENQ & OK' & LVQ & LNK) & RO' & LCK' & NSRC' & GSRC' & GIN' & LES' &
    TAB' & EOK' & LKS & LHS' & PER & PART & LBE & CCL' & CBR' & CDD' & CEI' & CER' & SLW' & ND' & BK1 & BK2 & BK3 & NLV &
    YLV).
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RM PR]. rewrite SPR in RM.
  pose proof RM as (M' & W' & BD' & _ & _ & _ & _ & _ & _ & VM' & _).
  assert (HK : YM05.alloc_ceiling <= slot_sp E - RELAY_INSTANCE_GONE_K)
    by (unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (HS4 : forall p, In p hj -> (snd p < 4)%nat).
  { intros p Hp. destruct (In_nth _ _ no_hj Hp) as (i & Hi & Ei).
    pose proof (g5_forall2_nth _ _ _ no_entry no_hj HPA i ltac:(lia)) as PK. rewrite Ei in PK.
    unfold pair_ok in PK. cbv zeta in PK. exact (proj1 (proj2 PK)). }
  assert (OFR : 0 < bv_unsigned cap -> fresh_block B (bv_unsigned out) (bv_unsigned cap)).
  { intros HC. destruct HO as [(X & _)|(_ & _ & _ & FRo & _)]; [lia|exact FRo]. }
  assert (OIN : 0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L A)).
  { intros HC. destruct HO as [(X & _)|(_ & _ & IN & _)]; [lia|exact IN]. }
  assert (O0 : bv_unsigned cap = 0 -> bv_unsigned out = 0).
  { intros HC. destruct HO as [(_ & X & _)|(X & _)]; [exact X|lia]. }
  assert (OE : O = []).
  { destruct HO as [(_ & _ & _ & X)|(_ & _ & _ & _ & _ & LO & _)]; [exact X|].
    apply length_zero_iff_nil. lia. }
  assert (RMw : rmid B (API rc) RELAY_INSTANCE_GONE_K (slot_sp E)
      (p5c_E (bv_unsigned out) (bv_unsigned cap) G es hj L A) (p5c_F (send_live cl br dd TOT) (bv_unsigned out) es hj)
      L A mem md L' A' mem' md') by exact RM.
  assert (NEh : forall a, YM05.alloc_ceiling <= a -> ~ p5c_E (bv_unsigned out) (bv_unsigned cap) G es hj L A a).
  { intros a Ha X. destruct (p5c_Ew B (API rc) AX L A mem md _ _ G es hj a HMR OFR GFR HS4 X) as [Y|(_ & Y)]; lia. }
  assert (KH : forall a cs, rw_cells (ms_segs B) mem a cs -> slot_sp E <= a ->
      a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> rw_cells (ms_segs B) mem' a cs).
  { intros a cs H H1 H2.
    apply (rmid_rw_hi B (API rc) RELAY_INSTANCE_GONE_K (slot_sp E) (p5c_E (bv_unsigned out) (bv_unsigned cap) G es hj L A)
      (p5c_F (send_live cl br dd TOT) (bv_unsigned out) es hj) L A mem md L' A' mem' md' a cs);
      [unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia|rewrite EA; unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia
      |exact HMR|exact RMw|exact H|exact H1|exact H2|].
    intros i Hi. apply NEh. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (KG : forall a cs, rw_cells (ms_segs B) mem a cs ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain B (a + i) /\
         ~ p5c_E (bv_unsigned out) (bv_unsigned cap) G es hj L A (a + i)) ->
      rw_cells (ms_segs B) mem' a cs).
  { intros a cs H D. exact (rmid_rw_img B (API rc) AX RELAY_INSTANCE_GONE_K (slot_sp E) _ _ L A mem md L' A' mem' md'
      a cs (hg_img_low B SEG) HK HMR RMw H D). }
  assert (NEg : forall a, in_img B a -> a < 0x31040 -> a <> 0x30fc4 -> a <> 0x30fd0 -> ~ (0x31000 <= a < 0x31018) ->
      ~ (0x3101c <= a < 0x31020) -> ~ p5c_E (bv_unsigned out) (bv_unsigned cap) G es hj L A a).
  { intros a HI H1 H2 H3 H4 H5 X.
    destruct (p5c_E_img B (API rc) AX L A mem md _ _ G es hj a HMR OFR GFR X HI) as [Y|[Y|[Y|[Y|Y]]]]; try lia.
    pose proof (p5c_da_lo es hj a Y) as DL. unfold Statement.G_S, HarnessRep.G_S in DL. lia. }
  assert (NDAi : List.NoDup (G :: bv_unsigned out :: concat (map entry_blocks es) ++
      concat (map (fun i0 => hs_blocks (fst (nth i0 hj no_hj))) (seq 0 (length es))))).
  { apply hf_nodup in NDA. unfold target_addrs in NDA.
    rewrite (p5c_map_seq (fun p => hs_blocks (fst p)) hj no_hj), LHJ in NDA. exact NDA. }
  assert (DBI : drained_blocks es hj = concat (map (fun i0 => if re_eof (nth i0 es no_entry) =? 0 then
      hs_blocks (fst (nth i0 hj no_hj)) else []) (seq 0 (length es)))).
  { unfold drained_blocks. rewrite (p5c_combine_seq (fun p => if re_eof (fst p) =? 0 then hs_blocks (fst (snd p)) else [])
      es hj no_entry no_hj (eq_sym LHJ)). reflexivity. }
  assert (TAI : target_addrs G (bv_unsigned out) es hj = G :: bv_unsigned out :: concat (map entry_blocks es) ++
      concat (map (fun i => hs_blocks (fst (nth i hj no_hj))) (seq 0 (length es)))).
  { unfold target_addrs. rewrite (p5c_map_seq (fun p => hs_blocks (fst p)) hj no_hj), LHJ. reflexivity. }
  assert (NDI : concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs')) =
      concat (map (fun i => if re_eof (nth i es no_entry) =? 0 then hs_blocks (nth i hs' (fst no_hj)) else [])
        (seq 0 (length es)))).
  { rewrite (p5c_combine_seq (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) es hs' no_entry
      (fst no_hj) (eq_sym LHS')). reflexivity. }
  assert (TAI' : target_addrs G OUT' es' (p5c_hj es hj hs') = G :: OUT' :: concat (map entry_blocks es') ++
      concat (map (fun i => hs_blocks (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj))))
        (seq 0 (length es)))).
  { unfold target_addrs. rewrite p5c_hj_blocks. reflexivity. }
  assert (HBS : forall i, hs_blocks (g5_src (nth i es no_entry) (fst (nth i hj no_hj)) (nth i hs' (fst no_hj))) =
      (if re_eof (nth i es no_entry) =? 0 then hs_blocks (nth i hs' (fst no_hj)) else []) ++
      (if re_eof (nth i es no_entry) =? 0 then [] else hs_blocks (fst (nth i hj no_hj)))).
  { intros i. unfold g5_src. destruct (re_eof (nth i es no_entry) =? 0); [rewrite app_nil_r|]; reflexivity. }
  assert (PI : forall i, (i < length es)%nat -> re_eof (nth i es no_entry) <> 0 ->
      src_at B L' A' mem' (G_S + SRC_SIZE * Z.of_nat (snd (nth i hj no_hj))) (fst (nth i hj no_hj))).
  { intros i Hi E1.
    pose proof (g5_forall2_nth _ _ _ no_entry no_hj HPA i ltac:(lia)) as PK.
    unfold pair_ok in PK. cbv zeta in PK. destruct PK as (SRCi & HJi & _).
    apply (src_at_rmid B (API rc) AX BW RELAY_INSTANCE_GONE_K (slot_sp E) _ _ L A mem md L' A' mem' md' _ _ SEG HK HMR
      RMw SRCi).
    - intros x Hx.
      assert (HPx : img_plain B (G_S + SRC_SIZE * Z.of_nat (snd (nth i hj no_hj)) + x))
        by (apply PLG; left; p5c_gunf; unfold SRC_SIZE; lia).
      split; [exact HPx|].
      intros X. destruct (p5c_E_img B (API rc) AX L A mem md _ _ G es hj _ HMR OFR GFR X (proj1 HPx))
        as [Y|[Y|[Y|[Y|Y]]]]; try (revert Y; p5c_gunf; unfold SRC_SIZE; intros Y; lia).
      refine (p5c_da_src es hj i _ LHJ NDH Hi E1 _ Y). unfold SRC_SIZE in *. lia.
    - intros q Hq.
      destruct (p5c_old_src G (bv_unsigned out) es hj i q NDAi Hi E1 Hq) as (N1 & N2 & N3 & N4).
      apply (p5c_kept B (API rc) AX IMG L A mem md _ _ G es hj _ q HMR GIN OIN HS4 N1 N2 N3).
      rewrite DBI. exact N4. }
  assert (PREi : forall i, (i < length es)%nat ->
      l2_pre (rc := rc) B (pf_bytes (instance_prefix id)) L' A' mem' t (nth i es' no_entry)
        (nth i (p5c_hj es hj hs') no_hj) (nth i (p5c_lss es hj) []) (nth i kss [])).
  { intros i Hi. rewrite p5c_hj_nth, p5c_lss_nth by exact Hi.
    destruct (PER i Hi) as (FDe & EOFe & NDK & SSK & GK & _ & _ & _ & _ & _ & D0 & _).
    rewrite (nth_indep hs' (fst (nth i hj no_hj)) (fst no_hj)) in D0 by lia.
    pose proof (g5_forall2_nth _ _ _ no_entry no_hj HPA i ltac:(lia)) as PK.
    pose proof (g5_in_combine es hj i no_entry no_hj LHJ Hi) as IC.
    pose proof (PI i Hi) as PIi.
    exact (p5c_pre rc B L A mem L' A' mem' t (pf_bytes (instance_prefix id)) _ _ _ _ _ es hj k _ HES IC Hcost
      ltac:(lia) Ht PK PIi FDe EOFe NDK SSK ltac:(rewrite (proj1 (g5_pre_bytes id)); exact GK) D0
      (fun E0 => p5c_ecap_fin rc B L A mem t (send_live cl br dd 1) (bv_unsigned mx) (bv_unsigned nout)
        (bv_unsigned cap) (instance_prefix id) es hj i HPA Ht Hi E0)). }
  assert (MRF : map re_fd es' = map re_fd es).
  { rewrite (p5c_map_seq re_fd es' no_entry), (p5c_map_seq re_fd es no_entry), LES'. apply map_ext_in.
    intros i Hi. apply in_seq in Hi. destruct (PER i ltac:(lia)) as (FDe & _). exact FDe. }
  assert (NDT' : NoDup (target_addrs G OUT' es' (p5c_hj es hj hs'))).
  { apply hf_nodup. rewrite TAI', (map_ext _ _ HBS).
    apply hf_nodup in ND'. rewrite NDI in ND'.
    apply (p5c_nd_join (G :: OUT' :: concat (map entry_blocks es')) (seq 0 (length es))
      (fun i => if re_eof (nth i es no_entry) =? 0 then hs_blocks (nth i hs' (fst no_hj)) else [])
      (fun i => if re_eof (nth i es no_entry) =? 0 then [] else hs_blocks (fst (nth i hj no_hj))) ND').
    - apply (proj1 (p5c_nd_sub0 (fun i => hs_blocks (fst (nth i hj no_hj)))
        (fun i => if re_eof (nth i es no_entry) =? 0 then [] else hs_blocks (fst (nth i hj no_hj))) (seq 0 (length es))
        ltac:(intros i _; cbn beta; destruct (re_eof (nth i es no_entry) =? 0); [right|left]; reflexivity)
        (NoDup_app_remove_l (G :: bv_unsigned out :: concat (map entry_blocks es)) _ NDAi))).
    - intros q Hq. apply p5c_in_cs in Hq as (i & Hi & Hq). cbv beta in Hq.
      destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E1]; [destruct Hq|].
      destruct (p5c_old_src G (bv_unsigned out) es hj i q NDAi Hi E1 Hq) as (N1 & N2 & N3 & N4).
      pose proof (g5_forall2_nth _ _ _ no_entry no_hj HPA i ltac:(lia)) as PK.
      unfold pair_ok in PK. cbv zeta in PK. destruct PK as (SRCi & _).
      destruct (g5_src_blocks B L A mem _ _ q SRCi Hq) as (m & Hm & Hin).
      rewrite <- DBI in N4.
      destruct (BK2 q m Hin Hm N2 N3 N4) as (M1 & M2 & M3).
      rewrite NDI in M3.
      split; [intros [X|[X|X]]; [exact (N1 (eq_sym X))|exact (M1 (eq_sym X))|exact (M2 X)]|exact M3]. }
  assert (REL' : l2_rel (rc := rc) B (pf_bytes (instance_prefix id)) (fun p => if Nat.ltb p 0 then L2Post else L2Pre)
      L' A' mem' t nfd G OUT' es' (p5c_hj es hj hs') (p5c_lss es hj) kss).
  { split; [exists tail'; exact TAB'|]. split; [exact GIN'|]. split; [exact GFR|]. split; [exact EOK'|].
    split; [rewrite MRF; exact HND|].
    split.
    { apply Forall_forall. intros e He. apply (in_map re_fd) in He. rewrite MRF in He.
      apply in_map_iff in He as (e0 & Ee & He0). rewrite Forall_forall in HFD. rewrite <- Ee. exact (HFD e0 He0). }
    split; [rewrite p5c_hj_len, LES'; reflexivity|].
    split.
    { intros p Hp. rewrite LES' in Hp. exact (PREi p Hp). }
    split; [rewrite p5c_hj_snd by exact LHJ; exact NDH|].
    split.
    { intros i Hi SO. unfold slot_open in SO. rewrite p5c_hj_snd in SO by exact LHJ.
      apply KG; [exact (ZH i Hi SO)|]. intros x Hx. cbn [cells_size csize] in Hx.
      assert (HPx : img_plain B (G_S + SRC_SIZE * Z.of_nat i + x))
        by (apply PLG; left; p5c_gunf; unfold SRC_SIZE; lia).
      split; [exact HPx|].
      intros X. destruct (p5c_E_img B (API rc) AX L A mem md _ _ G es hj _ HMR OFR GFR X (proj1 HPx))
        as [Y|[Y|[Y|[Y|Y]]]]; try (revert Y; p5c_gunf; unfold SRC_SIZE; intros Y; lia).
      refine (p5c_da_closed es hj i _ SO _ Y). unfold SRC_SIZE in *. lia. }
    exact NDT'. }
  assert (DK' : driver_kept B E (target_addrs G OUT' es' (p5c_hj es hj hs')) L' A' mem').
  { apply (p5c_driver B (API rc) BW E (target_addrs G (bv_unsigned out) es hj)
      (target_addrs G OUT' es' (p5c_hj es hj hs')) RELAY_INSTANCE_GONE_K (slot_sp E) _ _ L A mem md L' A' mem' md'
      ((if 0 <? bv_unsigned cap then [bv_unsigned out] else []) ++ concat (map entry_blocks es) ++ drained_blocks es hj)
      ((if send_live cl br dd TOT || (0 <? bv_unsigned cap) then [OUT'] else []) ++ concat (map entry_blocks es') ++
        concat (map (fun p => if re_eof (fst p) =? 0 then hs_blocks (snd p) else []) (combine es hs')))
      HWF (proj1 (hf_nodup _) (NDB L A mem md HMR)) HDK RMw INP NIT).
    - intros q Hq. rewrite TAI. apply p5c_in_opt in Hq as [(_ & ->)|Hq]; [right; left; reflexivity|].
      right; right. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|right].
      rewrite DBI in Hq. apply p5c_in_cs in Hq as (i & Hi & Hq). apply p5c_in_cs. exists i. split; [exact Hi|].
      destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0); [exact Hq|destruct Hq].
    - intros q Hq. rewrite TAI'. apply p5c_in_opt in Hq as [(_ & ->)|Hq]; [right; left; reflexivity|].
      right; right. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left; exact Hq|right].
      rewrite NDI in Hq. apply p5c_in_cs in Hq as (i & Hi & Hq). apply p5c_in_cs. exists i. split; [exact Hi|].
      rewrite HBS. apply in_or_app. left. exact Hq.
    - intros q m Hin Hq NL. rewrite TAI in Hq. rewrite TAI'.
      destruct Hq as [<-|[<-|Hq]]; [left; reflexivity| |].
      + exfalso. destruct (Z.ltb_spec 0 (bv_unsigned cap)) as [CP|CZ].
        * apply NL. apply in_or_app. left. left. reflexivity.
        * pose proof (BLOW L A mem md _ _ HMR Hin) as BL0. rewrite (O0 ltac:(lia)) in BL0. lia.
      + right; right. apply in_app_iff in Hq as [Hq|Hq].
        * exfalso. apply NL. apply in_or_app. right. apply in_or_app. left. exact Hq.
        * apply in_app_iff. right. apply p5c_in_cs in Hq as (i & Hi & Hq). apply p5c_in_cs. exists i.
          split; [exact Hi|]. rewrite HBS. destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E1].
          -- exfalso. apply NL. apply in_or_app. right. apply in_or_app. right. rewrite DBI.
             apply p5c_in_cs. exists i. split; [exact Hi|]. rewrite E0. exact Hq.
          -- apply in_or_app. right. exact Hq.
    - intros q Hq. rewrite TAI' in Hq. rewrite TAI.
      destruct Hq as [<-|[<-|Hq]]; [left; left; reflexivity| |].
      + destruct (send_live cl br dd TOT || (0 <? bv_unsigned cap)) eqn:LC.
        * right. apply in_or_app. left. left. reflexivity.
        * left. right. left. apply orb_false_iff in LC as [LV CZ].
          destruct (NLV LV) as (_ & EO & _). rewrite EO. reflexivity.
      + apply in_app_iff in Hq as [Hq|Hq].
        * right. apply in_or_app. right. apply in_or_app. left. exact Hq.
        * apply p5c_in_cs in Hq as (i & Hi & Hq). rewrite HBS in Hq. apply in_app_iff in Hq as [Hq|Hq].
          -- right. apply in_or_app. right. apply in_or_app. right. rewrite NDI. apply p5c_in_cs. exists i.
             split; [exact Hi|exact Hq].
          -- left. right. right. apply in_or_app. right. apply p5c_in_cs. exists i. split; [exact Hi|].
             destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0); [destruct Hq|exact Hq].
    - intros q Hq. apply p5c_in_opt in Hq as [(CP & ->)|Hq].
      + apply Z.ltb_lt in CP. exists (bv_unsigned cap). split; [exact CP|exact (OIN CP)].
      + apply in_app_iff in Hq as [Hq|Hq]; [exact (p5c_eb_pos B L A mem es q HES Hq)|].
        rewrite DBI in Hq. apply p5c_in_cs in Hq as (i & Hi & Hq).
        destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E1]; [|destruct Hq].
        pose proof (g5_forall2_nth _ _ _ no_entry no_hj HPA i ltac:(lia)) as PK.
        unfold pair_ok in PK. cbv zeta in PK. destruct PK as (SRCi & _).
        exact (g5_src_blocks B L A mem _ _ q SRCi Hq).
    - intros q m Hq. destruct (BK3 q m Hq) as [(Hold & NO1 & NE1 & ND1)|[Hq'|[Hq'|EQ]]].
      + left. split; [exact Hold|]. intros _ X. apply p5c_in_opt in X as [(_ & X)|X]; [exact (NO1 X)|].
        apply in_app_iff in X as [X|X]; [exact (NE1 X)|exact (ND1 X)].
      + right. apply in_or_app. right. apply in_or_app. left. exact Hq'.
      + right. apply in_or_app. right. apply in_or_app. right. exact Hq'.
      + subst q. destruct (send_live cl br dd TOT || (0 <? bv_unsigned cap)) eqn:LC.
        * right. apply in_or_app. left. left. reflexivity.
        * exfalso. apply orb_false_iff in LC as [LV CZ]. apply Z.ltb_ge in CZ.
          destruct (NLV LV) as (_ & EO & _). rewrite EO, (O0 ltac:(lia)) in Hq.
          pose proof (BLOW L' A' mem' md' _ _ M' Hq) as BL0. lia.
    - intros q m Hin Hm NL X.
      assert (NO1 : q <> bv_unsigned out).
      { intros ->. destruct (Z.ltb_spec 0 (bv_unsigned cap)) as [CP|CZ].
        - apply NL. apply in_or_app. left. left. reflexivity.
        - pose proof (BLOW L A mem md _ _ HMR Hin) as BL0. rewrite (O0 ltac:(lia)) in BL0. lia. }
      assert (NE1 : ~ In q (concat (map entry_blocks es)))
        by (intros Y; apply NL; apply in_or_app; right; apply in_or_app; left; exact Y).
      assert (ND1 : ~ In q (drained_blocks es hj))
        by (intros Y; apply NL; apply in_or_app; right; apply in_or_app; right; exact Y).
      destruct (BK2 q m Hin Hm NO1 NE1 ND1) as (M1 & M2 & M3).
      apply p5c_in_opt in X as [(_ & X)|X]; [exact (M1 X)|].
      apply in_app_iff in X as [X|X]; [exact (M2 X)|exact (M3 X)].
    - intros q NT. rewrite TAI in NT.
      apply (p5c_kept B (API rc) AX IMG L A mem md _ _ G es hj _ q HMR GIN OIN HS4).
      + intros ->. apply NT. left. reflexivity.
      + intros ->. apply NT. right. left. reflexivity.
      + intros Y. apply NT. right. right. apply in_or_app. left. exact Y.
      + intros Y. apply NT. right. right. apply in_or_app. right. rewrite DBI in Y.
        apply p5c_in_cs in Y as (i & Hi & Y). apply p5c_in_cs. exists i. split; [exact Hi|].
        destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0); [exact Y|destruct Y]. }
  assert (COST' : slot_cost es' (p5c_hj es hj hs') <= k).
  { eapply Z.le_trans; [|exact Hcost]. unfold slot_cost.
    rewrite (p5c_combine_seq (fun q => pair_cost (fst q) (snd q)) es' (p5c_hj es hj hs') no_entry no_hj
      ltac:(rewrite p5c_hj_len; exact LES')).
    rewrite (p5c_combine_seq (fun q => pair_cost (fst q) (snd q)) es hj no_entry no_hj (eq_sym LHJ)).
    rewrite LES'. apply p5c_sum_le. intros i Hi. apply in_seq in Hi. cbn [fst snd].
    rewrite p5c_hj_nth by lia.
    destruct (PER i ltac:(lia)) as (_ & _ & NDK & SSK & GK & _ & _ & _ & _ & _ & D0 & D1).
    rewrite (nth_indep hs' (fst (nth i hj no_hj)) (fst no_hj)) in D0 by lia.
    pose proof (g5_forall2_nth _ _ _ no_entry no_hj HPA i ltac:(lia)) as PK.
    assert (EOKi : CF.RelayRep.entry_ok B L A mem (nth i es no_entry))
      by (rewrite Forall_forall in HES; apply HES; apply nth_In; lia).
    assert (EOKi' : CF.RelayRep.entry_ok B L' A' mem' (nth i es' no_entry))
      by (rewrite Forall_forall in EOK'; apply EOK'; apply nth_In; lia).
    exact (p5c_cost rc B L A mem L' A' mem' t (instance_prefix id) _ _ _ _ _ _ EOKi EOKi' PK NDK SSK GK D0 D1). }
  destruct (g5_tot0 gn cl br dd (send_live cl br dd TOT) (g5_segs (instance_prefix id) es hj kss) RGN (proj1 GNC)
    (proj2 GNC) eq_refl) as [T1 T2].
  destruct (g5_words B gn cl br dd (send_live cl br dd TOT) (g5_segs (instance_prefix id) es hj kss) LB O junk'
    (if send_live cl br dd TOT then LB else []) nout out
    (if send_live cl br dd TOT then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
    (if send_live cl br dd TOT then Z_to_bv 64 OUT' else out) OUT' CAP' L' A' mem'
    RGN (proj1 GNC) (proj2 GNC) eq_refl LBE Hno OE eq_refl eq_refl eq_refl
    (fun LV => proj1 (proj2 (NLV LV)))
    ltac:(intros LV; destruct (YLV LV) as (Y1 & _ & Y3 & Y4 & Y5 & _); exact (conj Y1 (conj Y3 (conj Y4 Y5)))))
    as (WN1 & WN2 & WN3 & WN4 & WN5 & WN6).
  assert (LLB : Z.of_nat (length LB) = TOT) by (rewrite <- (bzs_length LB), LBE; reflexivity).
  assert (GL' : globals_at B mem' cl (if send_off cl br TOT then br else dd) gn dd
      (if send_off cl br TOT then ei else 0) (Z.of_nat (length es)) G nfd mx
      (if send_live cl br dd TOT then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
      (if send_live cl br dd TOT then Z_to_bv 64 CAP' else cap)
      (if send_live cl br dd TOT then Z_to_bv 64 OUT' else out)).
  { unfold globals_at.
    split.
    { pose proof (hg_cut _ _ _ [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)] Q1) as [Q1a _].
      apply (hg_join _ _ CF.relay_finish_b_c.G_LISTEN G_CLIENT [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 cl)]);
        [|exact CCL'|reflexivity].
      apply KG; [exact Q1a|]. p5c_frame PLG NEg. }
    split.
    { apply KG; [exact Q2|]. p5c_frame PLG NEg. }
    split.
    { apply KG; [exact Q3|]. p5c_frame PLG NEg. }
    split; [exact CBR'|].
    split.
    { apply KG; [exact Q5|]. p5c_frame PLG NEg. }
    split; [exact CDD'|]. split; [exact CEI'|]. split; [exact NSRC'|].
    split.
    { apply KG; [exact Q9|]. p5c_frame PLG NEg. }
    split; [exact GSRC'|].
    split.
    { destruct (send_live cl br dd TOT) eqn:LV.
      - destruct (YLV ltac:(first [exact LV|reflexivity])) as (_ & _ & _ & _ & _ & _ & Y7). exact Y7.
      - exact (proj1 (NLV ltac:(first [exact LV|reflexivity]))). }
    split; [exact LCK'|].
    split.
    { apply KG; [exact Q13|]. p5c_frame PLG NEg. }
    split; [exact CER'|]. split; [exact RCL|].
    split; [destruct (send_off cl br TOT); [exact RBR|exact RDD]|].
    split; [exact RGN|]. split; [exact RDD|].
    split; [destruct (send_off cl br TOT); [exact REI|left; reflexivity]|].
    split.
    { destruct GNC as [GN0 GN1]. split.
      - intros Hg. destruct (GN0 Hg) as (C3 & B0 & D0). split; [exact C3|]. split; [|exact D0].
        destruct (send_off cl br TOT); cbv iota; lia.
      - intros Hg. destruct (GN1 Hg) as [C|[Bq|D]]; [left; exact C| |right; right; exact D].
        assert (OFF : send_off cl br TOT = true)
          by (unfold send_off; rewrite Bq; cbn [Z.eqb]; destruct (cl <? 0); reflexivity).
        rewrite OFF. right; left; exact Bq. }
    exact MXB. }
  assert (OUTA : output_at (rc := rc) B L' A' mem'
      (if send_live cl br dd TOT then Z_to_bv 64 (bv_unsigned nout + TOT) else nout)
      (if send_live cl br dd TOT then Z_to_bv 64 CAP' else cap)
      (if send_live cl br dd TOT then Z_to_bv 64 OUT' else out)).
  { unfold output_at. cbv zeta. destruct (send_live cl br dd TOT) eqn:LV; cbv iota.
    - destruct (YLV ltac:(first [exact LV|reflexivity])) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _).
      destruct (T1 ltac:(first [exact LV|reflexivity])) as [Hg TZ].
      pose proof Y4 as (F1 & F2 & _).
      assert (TP0 : 0 < TOT) by (rewrite <- LLB, <- (bzs_length LB), LBE; lia).
      assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned nout + TOT)) = bv_unsigned nout + TOT)
        by (apply unsigned_lit; lia).
      assert (U2 : bv_unsigned (Z_to_bv 64 CAP') = CAP') by (apply unsigned_lit; lia).
      assert (U3 : bv_unsigned (Z_to_bv 64 OUT') = OUT') by (apply unsigned_lit; lia).
      rewrite U1, U2, U3. split.
      + exists LB, junk'. right. split; [lia|]. split; [lia|]. split; [exact Y3|]. split; [exact Y4|].
        split; [rewrite OE in Y5; exact Y5|]. split; [lia|lia].
      + rewrite Y2. exact (g5_cap B L A mem t _ _ _ _ _ _ es hj kss k k HES HPA Hcost (Z.le_refl k) ltac:(lia) LKS Hno
          HCAPB ltac:(intros i Hi; destruct (PER i Hi) as (_ & _ & NDK & SSK & _ & KHs & _); exact (conj NDK (conj SSK KHs)))
          eq_refl).
    - destruct (NLV ltac:(first [exact LV|reflexivity])) as (N1 & N2 & N3 & N4). split; [|exact HCAPB].
      exists O, junk0. destruct HO as [HO1|(HC & HN & IN & FR & BY & LO & LJ)]; [left; exact HO1|right].
      destruct (N4 HC) as (IN' & BY'). split; [exact HC|]. split; [exact HN|]. split; [exact IN'|].
      split; [exact FR|]. split; [exact BY'|]. split; [exact LO|exact LJ]. }
  assert (RI' : (RI3P GSF) E k (view_of G OUT' es' (p5c_hj es hj hs')) L' A').
  { assert (NDL' : List.NoDup (map fst (blocks L' A'))) by exact (proj1 (hf_nodup _) (NDB L' A' mem' md' M')).
    assert (SRC' : forall p, In p (p5c_hj es hj hs') -> exists HA, src_at B L' A' mem' HA (fst p))
      by exact (l2_rel_src B _ _ _ _ _ _ _ _ _ _ _ _ _ REL').
    assert (CTX : p5v_ctx B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id)
        L' A' regs' mem' md' OUT' CAP' es' hs' kss qs).
    { unfold p5v_ctx. cbv zeta.
      split; [exact HMR|]. split; [exact NDL|]. split; [exact HOUT|]. split; [exact GIN|]. split; [exact HES|].
      split; [exact HPA|]. split; [exact NDA|]. split; [exact LHJ|]. split; [exact Hes|]. split; [exact Hcost|].
      split; [lia|]. split; [exact Ht|]. split; [exact Hno|]. split; [exact RCL|]. split; [exact RBR|].
      split; [exact RDD|]. split; [exact RP|]. split; [exact LENQ|]. split; [exact LVQ|]. split; [exact LNK|].
      split; [exact GIN'|]. split; [exact LES'|]. split; [exact EOK'|]. split; [exact LKS|]. split; [exact LHS'|].
      split; [exact PER|]. split; [exact ND'|]. split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
      split.
      { intros LV. destruct (NLV LV) as (_ & NV1 & NV2 & NV3). split; [exact NV1|]. split; [exact NV2|].
        intros HC. exact (proj1 (NV3 HC)). }
      split.
      { intros LV. destruct (YLV LV) as (YV1 & YV2 & YV3 & _). split; [exact YV1|]. split; [exact YV2|]. exact YV3. }
      split; [exact M'|]. split; [exact NDL'|]. split; [exact SRC'|]. split; [exact NDT'|]. exact PART. }
    apply (RIK L' A' qs LENQ OK' (view_of G OUT' es' (p5c_hj es hj hs'))).
    - pose proof (l2_nc_len G OUT' es' (p5c_hj es hj hs')) as NL. rewrite p5c_hj_len, LES' in NL.
      unfold NC_MAX. lia.
    - exact (HV1 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - exact (HV2 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - pose proof (l2_ncs_wt B (API rc) L' A' mem' md' G _ _ _ es' (p5c_hj es hj hs') M' OUTA GIN' EOK' SRC'
        ltac:(rewrite LES'; exact Hes) ltac:(rewrite p5c_hj_len, LES'; reflexivity) NDL') as X.
      rewrite WN3 in X. exact X.
    - pose proof (HV3 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX) as X. cbv zeta in X.
      rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r. exact X.
    - exact (HV4 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - exact (HV5 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - exact (HV6 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - unfold view_of. cbn [rv_ek]. apply ek_view_nonneg.
    - exact NDL'.
    - exact (HV7 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - exact (HV8 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX).
    - exact (HV9 rc B (API rc) L A R1 mem md t k G es hj cl br dd mx nout cap out (instance_prefix id) L' A' regs' mem' md' OUT' CAP' es' hs' kss qs CTX). }
  assert (IK' : image_kept (rc := rc) B E mem').
  { apply (l2_img_keep B (API rc) AX SEG PL E RELAY_INSTANCE_GONE_K (slot_sp E) _ _ L A mem md L' A' mem' md'
      0x30fc0 512 HIK RMw HMR HK).
    - intros a X. destruct (p5c_Ew B (API rc) AX L A mem md _ _ G es hj a HMR OFR GFR HS4 X) as [Y|Y];
        [left; lia|right; exact Y].
    - intros a Ha. split; [apply in_G_bss; lia|]. rewrite SEG.
      split; [exact (proj1 (entry_global_access mem a (in_G_bss a ltac:(lia))))
             |exact (proj1 (entry_global_access mem' a (in_G_bss a ltac:(lia))))].
    - intros a Ha. unfold sk in Ha. unfold lib_scratch. destruct Ha as [Ha|Ha]; [left|right; exact Ha].
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - intros a Ha. unfold lib_scratch in Ha. unfold sk. destruct Ha as [Ha|Ha]; [right|left; right; exact Ha].
      unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (ST' : stack_mid B E mem').
  { destruct HST as (ST1 & ST2 & ST3). unfold stack_mid.
    split; [apply KH; [exact ST1|lia|unfold saved_cells; cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]|].
    split; [apply KH; [exact ST2|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]|].
    apply KH; [exact ST3|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]. }
  assert (Z32' : rw_cells (ms_segs B) mem' (slot_sp E + 32) [C8 (Z_to_bv 64 0)])
    by (apply KH; [exact Z32|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]).
  assert (WF40 : (length (pf_bytes (instance_prefix id)) + 1 +
      length (skipn (length (instance_prefix id) + 1) junk) = 48)%nat).
  { pose proof C40 as ((W40 & _) & _). cbn [cells_wf cell_wf] in W40. destruct W40 as [W40 _].
    unfold pf_bytes in W40 |- *. rewrite map_app, !length_app in W40. cbn [length map] in W40. lia. }
  assert (C40' : rw_cells (ms_segs B) mem' (slot_sp E + 40)
      [CB (length (pf_bytes (instance_prefix id)) + 1 + length (skipn (length (instance_prefix id) + 1) junk))
          (pf_bytes (instance_prefix id) ++ Z_to_bv 8 0 :: skipn (length (instance_prefix id) + 1) junk)]).
  { assert (EQB : pf_bytes (instance_prefix id ++ [0]) ++ skipn (length (instance_prefix id) + 1) junk =
        pf_bytes (instance_prefix id) ++ Z_to_bv 8 0 :: skipn (length (instance_prefix id) + 1) junk)
      by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
    rewrite WF40, <- EQB. apply KH; [exact C40|lia|cbn [cells_size csize]; unfold slot_sp, SLOT_FRAME in *; lia]. }
  assert (RD : J2_reads E mem').
  { intros i Hi.
    assert (REC' : rw_cells (ms_segs B) mem' (slot_sp E + 16) [C4 (Z_to_bv 64 (nth 0 rs 0)); C4 (Z_to_bv 64 (nth 1 rs 0));
        C4 (Z_to_bv 64 (nth 2 rs 0)); C4 (Z_to_bv 64 (nth 3 rs 0))])
      by (apply KH; [exact REC|lia|cbn [cells_size csize Nat.add]; unfold slot_sp, SLOT_FRAME in *; lia]).
    destruct REC' as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite SEG in BY.
    rewrite !bytes_at_app in BY. destruct BY as (BY0 & BY1 & BY2 & BY3 & _).
    exists (nth i rs 0).
    split; [rewrite (HRS i Hi); pose proof (p5c_rec_range es (nth i fs 0) (nth i os 0)); lia|].
    split.
    - destruct i as [|[|[|[|i]]]]; [| | | |lia]; cbn [nth].
      + apply (p5c_rd4 _ _ _ _ BY0). lia.
      + apply (p5c_rd4 _ _ _ _ BY1). rewrite ?length_le4. lia.
      + apply (p5c_rd4 _ _ _ _ BY2). rewrite ?length_le4. lia.
      + apply (p5c_rd4 _ _ _ _ BY3). rewrite ?length_le4. lia.
    - intros HR0. rewrite (HRS i Hi) in HR0.
      destruct (g5_read B L A mem t es hj fs os i HPA HND (fun p Hp => proj1 (SW1 p Hp)) SW2 Hi HR0)
        as (kk & Hkk & Ekk & Ekk0).
      destruct (PER kk Hkk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D0 & _).
      destruct (D0 Ekk0) as (SRC' & _ & _ & _ & PND & _). rewrite Ekk in SRC'.
      destruct (g5_read_cell B L' A' mem' i _ SEG SRC' PND) as (Hn0 & BY0').
      exists 0. split; [lia|]. rewrite unsigned_lit in BY0' by (p5c_gunf; lia). exact BY0'. }
  apply SR_ret.
  exists fx2, regs', L', A', mem', md', es', (p5c_hj es hj hs'), cl, (if send_off cl br TOT then br else dd), gn, dd,
    (if send_off cl br TOT then ei else 0), G, nfd, mx,
    (if send_live cl br dd TOT then Z_to_bv 64 (bv_unsigned nout + TOT) else nout),
    (if send_live cl br dd TOT then Z_to_bv 64 CAP' else cap),
    (if send_live cl br dd TOT then Z_to_bv 64 OUT' else out), (length es), (p5c_lss es hj), kss,
    (if send_live cl br dd TOT then LB else []), (pf_bytes (instance_prefix id)),
    (skipn (length (instance_prefix id) + 1) junk).
  split; [rewrite ?G1, ?G1y; reflexivity|].
  split.
  { assert (KP : forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (PR r Hr) (GR r Hr))).
    unfold RG2, tail_regs, base_regs, fix_regs.
    split; [split; [|split; [|split]]|split; [split; [|split; [|split; [|split; [|split]]]]|split; [|split]]].
    - exact (eq_trans (KP 2 ltac:(unfold callee_saved; lia)) B2).
    - exact (eq_trans (KP 3 ltac:(unfold callee_saved; lia)) B3).
    - exact (eq_trans (KP 4 ltac:(unfold callee_saved; lia)) B4).
    - exact (eq_trans (KP 20 ltac:(unfold callee_saved; lia)) B20).
    - exact (eq_trans (KP 19 ltac:(unfold callee_saved; lia)) F19).
    - exact (eq_trans (KP 21 ltac:(unfold callee_saved; lia)) F21).
    - exact (eq_trans (KP 24 ltac:(unfold callee_saved; lia)) F24).
    - exact (eq_trans (KP 25 ltac:(unfold callee_saved; lia)) F25).
    - exact (eq_trans (KP 26 ltac:(unfold callee_saved; lia)) F26).
    - exact (eq_trans (KP 27 ltac:(unfold callee_saved; lia)) F27).
    - exact (eq_trans (KP 8 ltac:(unfold callee_saved; lia)) R8).
    - exact (eq_trans (KP 23 ltac:(unfold callee_saved; lia)) R23).
    - exact (eq_trans (KP 22 ltac:(unfold callee_saved; lia)) R22). }
  split.
  { unfold l2_core, l2_body.
    replace (g5_at gn (l2_segs (pf_bytes (instance_prefix id)) (p5c_lss es hj) kss (length es)) 0) with 0
      by (unfold g5_at; destruct (gn =? 0); reflexivity).
    rewrite WN3.
    split; [exact M'|]. split; [exact W'|]. split; [exact BD'|]. split; [exact INIT'|].
    split; [destruct HVM as (vm & ->); destruct VM' as (vm' & ->); exists vm'; apply YI04.with_vmmaps_twice|].
    split; [exact RO'|]. split; [exact IK'|]. split; [exact ST'|]. split; [exact DK'|]. split; [exact GL'|].
    split; [exact OUTA|]. split; [exact REL'|]. split; [exact LES'|]. split; [exact COST'|]. split; [exact RI'|].
    split; [exact Z32'|]. split; [exact C40'|]. rewrite WN3 in WN5. exact WN5. }
  split; [lia|].
  split.
  { intros G0. rewrite p5c_segs, (proj1 (g5_pre_bytes id)).
    destruct (send_live cl br dd TOT) eqn:LV; [exact LBE|].
    pose proof (T2 ltac:(first [exact LV|reflexivity]) G0) as T0. apply length_zero_iff_nil in T0. rewrite T0.
    reflexivity. }
  split; [rewrite p5c_segs, (proj1 (g5_pre_bytes id)); exact WN2|].
  split; [exact WN4|].
  split; [exact (proj1 (proj2 (g5_pre_bytes id)))|].
  split.
  { pose proof (Z.mod_pos_bound (- (slot_sp E + 40 + Z.of_nat (length (pf_bytes (instance_prefix id))) + 1)) 8
      ltac:(lia)) as MB.
    pose proof (proj2 (proj2 (g5_pre_bytes id))) as PB. lia. }
  split; [exact FZ2|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Hnfd'|].
  split; [exact Hes|]. exact RD.
Qed.

End P5C.
