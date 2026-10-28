(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image Arr Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition links (m : mem) (Hs : list Z) : Prop :=
  forall k H, nth_error Hs k = Some H ->
    rw_cells bgusegs m (H + 384) [C8 (wz (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz (nth (S k) Hs 0))].

Definition item_blocks (st : ST) (OW : list block) (Hs : list Z) : Prop :=
  forall k q, nth_error (gx_items (st_ctx st)) k = Some q -> In (q, nth k Hs 0, ITEM_SZ) OW.

Lemma cx_view_some : forall m OW PL st Hs Ia ac qc, pl_ctx PL = Some (ac, qc) ->
  cx_view m OW PL st Hs Ia <->
  (In (qc, ac, BN_CTX_SZ) OW /\ length Hs = length (gx_items (st_ctx st))
   /\ rw_cells bgusegs m ac (ctx_cells (hd 0 Hs) (cur_addr Hs (st_ctx st)) (last Hs 0) Ia (st_ctx st))
   /\ stack_rep m OW Ia (st_ctx st) /\ item_blocks st OW Hs /\ links m Hs).
Proof. intros m OW PL st Hs Ia ac qc E. unfold cx_view, item_blocks, links. rewrite E. tauto. Qed.

Lemma links_keep : forall s OW LB m m' st PL EA ac qc Hs W,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> pl_ctx PL = Some (ac, qc) ->
  length Hs = length (gx_items (st_ctx st)) -> item_blocks st OW Hs ->
  links m Hs -> munch W m m' -> wmono bgusegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv \/ (ac <= fst iv /\ snd iv <= ac + BN_CTX_SZ)
                            \/ (exists q A n, In (q, A, n) (OW ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ ~ In q (gx_items (st_ctx st)))) W ->
  links m' Hs.
Proof.
  intros s OW LB m m' st PL EA ac qc Hs W HEAP PARTS EC LHs HI HL MU WM HW k H Hk.
  pose proof PARTS as (WFS & PWF & IDS & (PB & PC & PM) & ERRB). rewrite EC in PC.
  assert (Hk' : (k < length (gx_items (st_ctx st)))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
  destruct (nth_error (gx_items (st_ctx st)) k) as [q|] eqn:Eq; [|apply nth_error_None in Eq; lia].
  pose proof (HI k q Eq) as HinH. rewrite (nth_error_nth _ _ _ Hk) in HinH.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HinH) as (_ & _ & _ & HC & _).
  assert (NEc : qc <> q).
  { eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply item_in_m; eapply nth_error_In; exact Eq]. }
  pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP PC HinH NEc) as DJc.
  eapply rw_cells_transport; [exact (HL k H Hk)| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. clear MU.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  cbn [fst snd] in Hiv. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE, BN_CTX_SZ in *.
  destruct Hiv as [Hs0|[Hc|(q' & A & n & Hq' & H1 & H2 & NE)]]; [lia| lia|].
  assert (NEq : q' <> q) by (intros ->; apply NE; eapply nth_error_In; exact Eq).
  pose proof (LH_disjoint _ _ _ (q', A, n) (q, H, 400) HEAP Hq' ltac:(apply in_or_app; left; exact HinH) NEq) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

Lemma links_transport : forall m m' Hs W,
  links m Hs -> munch W m m' -> wmono bgusegs m m' -> (forall k H, nth_error Hs k = Some H -> disjoint_from W (H + 384) 16) -> links m' Hs.
Proof.
  intros m m' Hs W HL MU WM HD k H Hk. eapply rw_cells_transport; [exact (HL k H Hk)| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact (HD k H Hk).
Qed.

Lemma links_heap_pres : forall st OW L SP m m' Hs,
  length Hs = length (gx_items (st_ctx st)) -> item_blocks st OW Hs -> (forall b, In b OW -> In b L) ->
  links m Hs -> rheap_pres L SP m m' -> links m' Hs.
Proof.
  intros st OW L SP m m' Hs LHs HI HIL HL HP k H Hk.
  assert (Hk' : (k < length (gx_items (st_ctx st)))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
  destruct (nth_error (gx_items (st_ctx st)) k) as [q|] eqn:Eq; [|apply nth_error_None in Eq; lia].
  pose proof (HI k q Eq) as HinH. rewrite (nth_error_nth _ _ _ Hk) in HinH.
  eapply rw_cells_agree; [apply agree_of_heap_pres; exact HP| exact (HL k H Hk)|]. intros x Hx. cbn in Hx.
  right; right. exists (q, H, ITEM_SZ). split; [apply HIL; exact HinH|]. cbn [blk_addr blk_size fst snd]. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE. lia.
Qed.

Lemma item_blocks_ow : forall st OW OW' Hs, item_blocks st OW Hs -> (forall b, In b OW -> In b OW') -> item_blocks st OW' Hs.
Proof. intros st OW OW' Hs HI HOW k q Hk. apply HOW. apply HI. exact Hk. Qed.

Lemma item_blocks_set_ctx : forall st c OW Hs, gx_items c = gx_items (st_ctx st) -> item_blocks st OW Hs -> item_blocks (set_ctx c st) OW Hs.
Proof. intros st c OW Hs E HI k q Hk. cbn [st_ctx set_ctx] in Hk. rewrite E in Hk. apply HI. exact Hk. Qed.

Lemma st_wf_set_ctx : forall (st : ST) c, st_wf st -> gx_items c = gx_items (st_ctx st) -> ctx_wf c -> st_wf (set_ctx c st).
Proof.
  intros st c (EL & BOK & EONE & _) EI CW. unfold st_wf. cbn [st_bns st_ctx set_ctx]. rewrite EI.
  split; [exact EL|]. split; [exact BOK|]. split; [exact EONE| exact CW].
Qed.

Lemma item_facts : forall s OW LB m st PL EA ac qc Hs j H,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> pl_ctx PL = Some (ac, qc) ->
  length Hs = length (gx_items (st_ctx st)) -> item_blocks st OW Hs -> nth_error Hs j = Some H ->
  0 < H /\ H + 400 <= alloc_ceiling /\ (H + 400 <= 0x10000 \/ 0x353000 <= H) /\ (H + 400 <= ac \/ ac + BN_CTX_SZ <= H)
  /\ (forall j' H', nth_error Hs j' = Some H' -> j' <> j -> H + 400 <= H' \/ H' + 400 <= H)
  /\ (forall q I, gx_indexes (st_ctx st) = Some q -> In (q, I, FRAMES_SZ) OW -> H + 400 <= I \/ I + FRAMES_SZ <= H).
Proof.
  intros s OW LB m st PL EA ac qc Hs j H HEAP PARTS EC LHs HI Hj.
  pose proof PARTS as (WFS & PWF & IDS & (PB & PC & PM) & ERRB). rewrite EC in PC.
  assert (Hj' : (j < length (gx_items (st_ctx st)))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
  destruct (nth_error (gx_items (st_ctx st)) j) as [q|] eqn:Eq; [|apply nth_error_None in Eq; lia].
  pose proof (HI j q Eq) as Hin. rewrite (nth_error_nth _ _ _ Hj) in Hin. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in Hin.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). split; [exact B0|]. split; [exact BC|]. split; [exact BI|].
  split. { assert (NE : qc <> q) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply item_in_m; eapply nth_error_In; exact Eq]).
           pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP PC Hin NE). unfold BN_CTX_SZ in *. lia. }
  split.
  - intros j' H' Hj2 NEj.
    assert (Hj2' : (j' < length (gx_items (st_ctx st)))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
    destruct (nth_error (gx_items (st_ctx st)) j') as [q'|] eqn:Eq'; [|apply nth_error_None in Eq'; lia].
    pose proof (HI j' q' Eq') as Hin'. rewrite (nth_error_nth _ _ _ Hj2) in Hin'. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in Hin'.
    assert (NE : q <> q').
    { intros <-. apply NEj. symmetry. eapply (nth_error_nodup_inj (gx_items (st_ctx st))); [eapply ids_items_nodup; eapply ids_m_nodup; exact IDS| exact Eq| exact Eq']. }
    exact (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin Hin' NE).
  - intros qi Ix EI HinI.
    assert (NE : q <> qi) by (eapply ids_item_idx_neq; [eapply ids_m_nodup; exact IDS| eapply nth_error_In; exact Eq| exact EI]).
    exact (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin HinI NE).
Qed.

Lemma item_align : forall s OW LB m st Hs j H,
  RHEAP s (OW ++ LB) m -> length Hs = length (gx_items (st_ctx st)) -> item_blocks st OW Hs -> nth_error Hs j = Some H ->
  H mod 8 = 0.
Proof.
  intros s OW LB m st Hs j H HEAP LHs HI Hj.
  assert (Hj' : (j < length (gx_items (st_ctx st)))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
  destruct (nth_error (gx_items (st_ctx st)) j) as [q|] eqn:Eq; [|apply nth_error_None in Eq; lia].
  pose proof (HI j q Eq) as Hin. rewrite (nth_error_nth _ _ _ Hj) in Hin.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & B16 & _). clear - B16. Z.div_mod_to_equations. lia.
Qed.

Lemma stack_rep_same : forall m OW I (c c' : bg_ctx bptr),
  gx_indexes c' = gx_indexes c -> gx_ssize c' = gx_ssize c -> gx_frames c' = gx_frames c -> stack_rep m OW I c -> stack_rep m OW I c'.
Proof. intros m OW I c c' E1 E2 E3 H. unfold stack_rep in *. rewrite E1, E2, E3. exact H. Qed.

Lemma stack_rep_keep : forall s OW LB m m' st PL EA ac qc I W,
  RHEAP s (OW ++ LB) m -> lib_parts st OW PL EA -> pl_ctx PL = Some (ac, qc) ->
  stack_rep m OW I (st_ctx st) -> munch W m m' -> wmono bgusegs m m' ->
  Forall (fun iv : Z * Z => alloc_ceiling <= fst iv \/ (ac <= fst iv /\ snd iv <= ac + BN_CTX_SZ)
                            \/ (exists q A n, In (q, A, n) (OW ++ LB) /\ A <= fst iv /\ snd iv <= A + n /\ Some q <> gx_indexes (st_ctx st))) W ->
  stack_rep m' OW I (st_ctx st).
Proof.
  intros s OW LB m m' st PL EA ac qc Ix W HEAP PARTS EC STK MU WM HW. unfold stack_rep in *.
  pose proof PARTS as (WFS & PWF & IDS & (PB & PC & PM) & ERRB). rewrite EC in PC.
  destruct (gx_indexes (st_ctx st)) as [q|] eqn:EI; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
  assert (NEI : qc <> q) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply idx_in_m; exact EI]).
  pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP PC HinI NEI) as CXI.
  assert (LWS : Z.of_nat (length (map (fun k : nat => wz (Z.of_nat k)) (gx_frames (st_ctx st)) ++ stale)) = 32) by (rewrite length_app, length_map; unfold BN_CTX_START_FRAMES in LEN; lia).
  eapply u32arr_transport; [exact ARRI| exact MU| exact WM|]. rewrite LWS. clear MU ARRI.
  unfold FRAMES_SZ, BN_CTX_START_FRAMES, BN_CTX_SZ in *.
  induction HW as [|[x y] W Hiv HW IH]; [exact I|]. cbn [disjoint_from]. split; [|exact IH].
  cbn [fst snd] in Hiv. destruct Hiv as [Hs|[Hc|(q' & A & n & Hq & H1 & H2 & NE)]]; [lia| lia|].
  assert (NEq : q' <> q) by congruence.
  pose proof (LH_disjoint _ _ _ (q', A, n) (q, Ix, 4 * Z.of_nat 32) HEAP Hq ltac:(apply in_or_app; left; exact HinI) NEq) as DJ.
  cbn [blk_addr blk_size fst snd] in DJ. lia.
Qed.

Lemma stack_rep_heap_pres : forall (OW : list block) L SP m m' I (c : bg_ctx bptr),
  (forall b, In b OW -> In b L) -> stack_rep m OW I c -> rheap_pres L SP m m' -> stack_rep m' OW I c.
Proof.
  intros OW L SP m m' Ix c HI STK HP. unfold stack_rep in *. destruct (gx_indexes c) as [q|]; [|exact STK].
  destruct STK as (HinI & SZ32 & stale & LEN & ARRI). split; [exact HinI|]. split; [exact SZ32|]. exists stale. split; [exact LEN|].
  eapply BnRep.u32arr_agree; [apply agree_of_heap_pres; exact HP| exact ARRI|]. intros x Hx.
  right; right. exists (q, Ix, FRAMES_SZ). split; [apply HI; exact HinI|]. cbn [blk_addr blk_size fst snd].
  rewrite length_app, length_map in Hx. unfold FRAMES_SZ, BN_CTX_START_FRAMES in *. lia.
Qed.

Lemma stack_rep_ow : forall (OW OW' : list block) m I (c : bg_ctx bptr),
  (forall b, In b OW -> In b OW') -> stack_rep m OW I c -> stack_rep m OW' I c.
Proof.
  intros OW OW' m Ix c HI STK. unfold stack_rep in *. destruct (gx_indexes c) as [q|]; [|exact STK].
  destruct STK as (HinI & REST). split; [apply HI; exact HinI| exact REST].
Qed.

Lemma last_nth : forall (l : list Z) d, l <> [] -> last l d = nth (length l - 1) l d.
Proof.
  induction l as [|x l IH]; intros d Hn; [congruence|]. destruct l as [|y l']; [reflexivity|].
  change (last (x :: y :: l') d) with (last (y :: l') d). rewrite (IH d) by discriminate.
  replace (length (x :: y :: l') - 1)%nat with (S (length (y :: l') - 1))%nat by (cbn; lia). reflexivity.
Qed.

Lemma links_snoc : forall m Hs Hn,
  (forall k H, nth_error Hs k = Some H -> (S k < length Hs)%nat ->
     rw_cells bgusegs m (H + 384) [C8 (wz (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz (nth (S k) Hs 0))]) ->
  (forall k H, nth_error Hs k = Some H -> S k = length Hs ->
     rw_cells bgusegs m (H + 384) [C8 (wz (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz Hn)]) ->
  rw_cells bgusegs m (Hn + 384) [C8 (wz (last Hs 0)); C8 (wz 0)] ->
  links m (Hs ++ [Hn]).
Proof.
  intros m Hs Hn HA HB HC k H Hk.
  destruct (Nat.lt_ge_cases k (length Hs)) as [LT|GE].
  - rewrite nth_error_app1 in Hk by exact LT.
    destruct (Nat.eq_dec (S k) (length Hs)) as [E|NE].
    + rewrite app_nth2 by lia. rewrite E, Nat.sub_diag. cbn [nth].
      specialize (HB k H Hk E). destruct k as [|k']; [exact HB|]. rewrite app_nth1 by lia. exact HB.
    + rewrite (app_nth1 Hs [Hn] 0) by lia.
      specialize (HA k H Hk ltac:(lia)). destruct k as [|k']; [exact HA|]. rewrite app_nth1 by lia. exact HA.
  - assert (K : (k < length (Hs ++ [Hn]))%nat) by (apply (proj1 (nth_error_Some _ _)); congruence).
    rewrite length_app in K. cbn [length] in K. assert (k = length Hs) as -> by lia.
    rewrite nth_error_app2, Nat.sub_diag in Hk by lia. cbn [nth_error] in Hk. injection Hk as <-.
    rewrite (nth_overflow (Hs ++ [Hn])) by (rewrite length_app; cbn [length]; lia).
    destruct Hs as [|h0 Hs']; [cbn [length last] in HC |- *; exact HC|].
    cbn [length]. rewrite app_nth1 by (cbn [length]; lia). rewrite last_nth in HC by discriminate.
    replace (length (h0 :: Hs') - 1)%nat with (length Hs') in HC by (cbn; lia). exact HC.
Qed.

Lemma div16_of_lt : forall i n, (i < 16 * n)%nat -> (i / 16 < n)%nat.
Proof. intros i n H. apply Nat.Div0.div_lt_upper_bound. lia. Qed.
Lemma div16_pred_in : forall i, (i mod 16 <> 0)%nat -> ((i - 1) / 16 = i / 16)%nat.
Proof.
  intros i H. pose proof (Nat.div_mod_eq i 16) as DM. pose proof (Nat.mod_upper_bound i 16 ltac:(lia)) as MB.
  symmetry. apply (Nat.div_unique (i - 1) 16 (i / 16) (i mod 16 - 1)); lia.
Qed.
Lemma div16_pred_bd : forall i, (i <> 0)%nat -> (i mod 16 = 0)%nat -> (S ((i - 1) / 16) = i / 16)%nat /\ (1 <= i / 16)%nat.
Proof.
  intros i H0 HM. pose proof (Nat.div_mod_eq i 16) as DM.
  assert (1 <= i / 16)%nat by lia. split; [|lia].
  enough ((i - 1) / 16 = i / 16 - 1)%nat by lia.
  symmetry. apply (Nat.div_unique (i - 1) 16 (i / 16 - 1) 15); lia.
Qed.
Lemma div16_mul : forall n, ((16 * n) / 16 = n)%nat.
Proof. intros n. rewrite Nat.mul_comm. apply Nat.div_mul. lia. Qed.
Lemma mod16_mul : forall n, ((16 * n) mod 16 = 0)%nat.
Proof. intros n. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. Qed.
Lemma div16_mod_eq : forall i, (16 * (i / 16) + i mod 16 = i)%nat.
Proof. intros i. symmetry. apply Nat.div_mod_eq. Qed.

End WithCeiling0.
