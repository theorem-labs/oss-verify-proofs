(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_get_object_walk W_c2i_ibuf W_c2i_int.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sk_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma disjoint_from_forall : forall W a n, Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof. induction W as [|[x y] W IH]; intros a n H; cbn; [exact I|]. apply Forall_cons_iff in H. destruct H as [H1 H2]. cbn [fst snd] in H1. split; [lia| apply IH; exact H2]. Qed.

Lemma rin_ivs_In : forall X a iv, In iv X -> fst iv <= a < snd iv -> rin_ivs X a.
Proof. induction X as [|y X IH]; intros a iv Hin Ha; [destruct Hin|]. cbn. destruct Hin as [->|Hin]; [left; exact Ha| right; eapply IH; eassumption]. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cb_split2 : forall m A a b bs,
  rw_cells ctusegs m A [CB (Z.to_nat (a + b)) bs] -> 0 <= a -> 0 <= b ->
  rw_cells ctusegs m A [CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] /\ rw_cells ctusegs m (A + a) [CB (Z.to_nat b) (skipn (Z.to_nat a) bs)].
Proof.
  intros m A a b bs H Ha Hb.
  pose proof (cells_at_wf _ _ _ _ (proj1 H)) as [WF _]. cbn in WF.
  assert (H2 : rw_cells ctusegs m A ([CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] ++ [CB (Z.to_nat b) (skipn (Z.to_nat a) bs)])).
  { eapply rw_cells_recast; [exact H| | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn. rewrite !app_nil_r, firstn_skipn. reflexivity.
    - cbn. lia. }
  apply rw_cells_app in H2. destruct H2 as [H3 H4]. split; [exact H3|].
  cbn [cells_size csize] in H4. rewrite Nat.add_0_r, Z2Nat.id in H4 by lia. exact H4.
Qed.

Lemma cb_join2 : forall m A a b bs1 bs2,
  rw_cells ctusegs m A [CB (Z.to_nat a) bs1] -> rw_cells ctusegs m (A + a) [CB (Z.to_nat b) bs2] -> 0 <= a -> 0 <= b ->
  rw_cells ctusegs m A [CB (Z.to_nat (a + b)) (bs1 ++ bs2)].
Proof.
  intros m A a b bs1 bs2 H1 H2 Ha Hb.
  pose proof (cells_at_wf _ _ _ _ (proj1 H1)) as [W1 _]. pose proof (cells_at_wf _ _ _ _ (proj1 H2)) as [W2 _]. cbn in W1, W2.
  assert (H : rw_cells ctusegs m A ([CB (Z.to_nat a) bs1] ++ [CB (Z.to_nat b) bs2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact H2. }
  eapply rw_cells_recast; [exact H| | |].
  - cbn. rewrite length_app. repeat split; lia.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma cells_blob : forall m A cs, rw_cells ctusegs m A cs -> rw_cells ctusegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (cells_at_wf _ _ _ _ (proj1 H)) as WF.
  eapply rw_cells_recast; [exact H| cbn; split; [apply cells_bytes_length; exact WF| exact I]| cbn; rewrite app_nil_r; reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma cells_pick : forall m A k pre c post,
  rw_cells ctusegs m A (pre ++ c :: post) -> Z.of_nat (cells_size pre) = k -> ro_cells ctusegs m (A + k) [c].
Proof.
  intros m A k pre c post H Hk. apply rw_cells_app in H. destruct H as [_ H2]. rewrite Hk in H2.
  change (c :: post) with ([c] ++ post) in H2. apply rw_cells_app in H2. destruct H2 as [H3 _]. exact (proj1 H3).
Qed.
Lemma cells_pick_rw : forall m A k pre c post,
  rw_cells ctusegs m A (pre ++ c :: post) -> Z.of_nat (cells_size pre) = k -> rw_cells ctusegs m (A + k) [c].
Proof.
  intros m A k pre c post H Hk. apply rw_cells_app in H. destruct H as [_ H2]. rewrite Hk in H2.
  change (c :: post) with ([c] ++ post) in H2. apply rw_cells_app in H2. destruct H2 as [H3 _]. exact H3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arr_rep_agree : forall P m m' L adr o,
  agree_on P m m' -> (forall q n a, o = Some (q, n) -> adr q <= a < adr q + n -> P a) -> arr_rep m L adr o -> arr_rep m' L adr o.
Proof.
  intros P m m' L adr [[q n]|] AG HP H; cbn in *; [| exact I]. destruct H as (Hn & HL & bs & HB). split; [exact Hn|]. split; [exact HL|]. exists bs.
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. eapply HP; [reflexivity| lia].
Qed.

Lemma sct_rep_agree : forall P m m' L adr x,
  agree_on P m m' -> (forall b a, In b (sct_blocks adr x) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sct_rep m L adr x -> sct_rep m' L adr x.
Proof.
  intros P m m' L adr x AG HP (H1 & H2 & H3 & H4 & H5 & H6 & REST).
  assert (BL : forall b, (In b (oblk adr (osz32 (sc_logid x))) \/ In b (oblk adr (sc_ext x)) \/ In b (oblk adr (sc_sig x)) \/ In b (oblk adr (sc_blob x))
                          \/ b = (sc_blk x, adr (sc_blk x), SCT_SIZE)) -> In b (sct_blocks adr x)).
  { intros b Hb. unfold sct_blocks. rewrite !in_app_iff. cbn. destruct Hb as [Hb|[Hb|[Hb|[Hb| ->]]]]; tauto. }
  split; [exact H1|]. split.
  { eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply (HP (sc_blk x, adr (sc_blk x), SCT_SIZE)); [apply BL; right; right; right; right; reflexivity|].
    cbn. rewrite sct_cells_size in Ha. unfold SCT_SIZE in *. lia. }
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H3]|].
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H4]|].
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H5]|].
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H6]|].
  exact REST.
Qed.

(* [comment removed for export] *)
Definition sk_allblocks (adr : bptr -> Z) (k : skr bptr) : list block :=
  scts_blocks adr (sk_items k) ++ dblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)].

Lemma sk_allblocks_in : forall m L adr k b, sk_rep m L adr k -> In b (sk_allblocks adr k) -> In b L.
Proof.
  intros m L adr k b (HIN & _ & HD & HF & _) Hb. unfold sk_allblocks in Hb. rewrite !in_app_iff in Hb.
  assert (ITEMS : forall l, Forall (sct_rep m L adr) l -> In b (scts_blocks adr l) -> In b L).
  { intros l HFl. induction HFl as [|x t Hx HFt IH]; intros Hbl; [destruct Hbl|]. cbn in Hbl. apply in_app_iff in Hbl.
    destruct Hbl as [Hbl|Hbl]; [exact (sct_rep_blocks_in _ _ _ _ Hx _ Hbl)| exact (IH Hbl)]. }
  destruct Hb as [Hb|[Hb|Hb]].
  - exact (ITEMS _ HF Hb).
  - destruct (sk_data k) as [[q na]|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj1 HD).
  - destruct Hb as [<-|[]]. exact HIN.
Qed.

Lemma sk_rep_agree : forall P m m' L adr k,
  agree_on P m m' -> (forall b a, In b (sk_allblocks adr k) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sk_rep m L adr k -> sk_rep m' L adr k.
Proof.
  intros P m m' L adr k AG HP (HIN & (sorted & SR & HC) & HD & HF & ND).
  split; [exact HIN|]. split.
  { exists sorted. split; [exact SR|]. eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. rewrite sk_cells_size in Ha.
    apply (HP (sk_blk k, adr (sk_blk k), STACK_SIZE)); [unfold sk_allblocks; rewrite !in_app_iff; right; right; left; reflexivity| cbn; exact Ha]. }
  split.
  { destruct (sk_data k) as [[q na]|] eqn:ED; [| exact HD]. destruct HD as (H1 & H2 & H3 & jb & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    exists jb. split; [exact H4|]. eapply rw_cells_agree; [exact AG| exact H5|]. intros a Ha. rewrite data_block_size in Ha.
    apply (HP (q, adr q, 8 * na)); [unfold sk_allblocks; rewrite ED, !in_app_iff; right; left; left; reflexivity| cbn]. unfold sk_num in *. lia. }
  split; [| exact ND].
  apply Forall_forall. intros x Hx. eapply sct_rep_agree; [exact AG| | exact (proj1 (Forall_forall _ _) HF x Hx)].
  intros b a Hb Ha. apply (HP b); [| exact Ha]. unfold sk_allblocks. rewrite !in_app_iff. left.
  clear - Hx Hb. induction (sk_items k) as [|y t IH]; [destruct Hx|]. cbn. apply in_app_iff. destruct Hx as [<-|Hx]; [left; exact Hb| right; exact (IH Hx)].
Qed.


Lemma sct_rep_mono : forall m L L' adr x, (forall b, In b L -> In b L') -> sct_rep m L adr x -> sct_rep m L' adr x.
Proof.
  intros m L L' adr x HL (H1 & H2 & H3 & H4 & H5 & H6 & REST).
  assert (AR : forall o, arr_rep m L adr o -> arr_rep m L' adr o) by (intros [[q n]|] H; cbn in *; [| exact I]; destruct H as (A1 & A2 & A3); split; [exact A1| split; [apply HL; exact A2| exact A3]]).
  split; [apply HL; exact H1|]. split; [exact H2|]. split; [apply AR; exact H3|]. split; [apply AR; exact H4|]. split; [apply AR; exact H5|]. split; [apply AR; exact H6|]. exact REST.
Qed.


Lemma EA : errno_addr (Z_to_bv 64 RATP) = 3355012.
Proof. unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block) (XC : list (Z * Z)).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis XCB : Forall (fun iv => bv_unsigned sp <= fst iv /\ snd iv <= B) XC.

  Local Notation X0 := (XC ++ LIBW_AP) (only parsing).

  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.

  Definition einv (q : Z) (sX : PState) (stX : ap_st bptr) (mX : mem) (OWX : list block) (errvX : word) (boX : Z * Z) (NEW : list block) : Prop :=
    (RHEAP sX (OWX ++ NEW ++ LB) mX /\ ap_state stX mX OWX E boX /\ ids_ok E stX /\ ApIface.data_cells mX OWX stX
     /\ rauxv_ok mX B /\ lo <= q <= bv_unsigned sp /\ stk ctusegs mX lo q
     /\ rw_cells ctusegs mX 3355012 [C4 errvX] /\ ssp_cells mX canary /\ mem_inv ctusegs mX)
    /\ lx_pres LB (bv_unsigned sp) X0 m mX
    /\ (forall b, In b K -> In b OWX) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids stX ++ env_ids E)) /\ kept K m mX
    /\ ps_so sX = ps_so s /\ ps_fa sX = ps_fa s.

  (* [comment removed for export] *)
  Lemma einv_entry : forall st OW bo errv stack,
    ap_pre s st m OW LB E bo sp lo B errv canary stack -> 0 <= stack ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    einv (bv_unsigned sp) s st m OW errv bo [] /\ lo <= bv_unsigned sp - stack /\ bv_unsigned sp mod 16 = 0.
  Proof.
    intros st OW bo errv stack PRE ST0 KOW KIDS. pose proof SPR as SPR.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16').
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    split; [| split; [exact LO'| exact SP16']].
    split; [| split; [apply lx_pres_refl| split; [exact KOW| split; [exact KIDS| split; [apply kept_refl| split; reflexivity]]]]].
    cbn [app]. split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact AUX|]. split; [lia|].
    split; [exact ST|]. split; [exact ERR|]. split; [exact SSP| exact MI].
  Qed.

  (* [comment removed for export] *)
  Lemma einv_facts : forall q sX stX mX OWX errvX boX NEW,
    einv q sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ List.NoDup (map blk_id (OWX ++ NEW ++ LB))
    /\ (forall p Ap n, In (p, Ap, n) (OWX ++ NEW ++ LB) -> 0 < Ap /\ 0 <= n /\ Ap + n <= alloc_ceiling /\ (Ap + n <= 0x10000 \/ 0x355000 <= Ap) /\ Ap mod 16 = 0)
    /\ (forall p Ap n, In (p, Ap, n) NEW -> ~ In p (map blk_id (OWX ++ LB)))
    /\ (forall p Ap n pb PA psz, In (p, Ap, n) NEW -> In (pb, PA, psz) LB -> Ap + n <= PA \/ PA + psz <= Ap)
    /\ (forall p Ap n pb PA psz, In (p, Ap, n) NEW -> In (pb, PA, psz) OWX -> Ap + n <= PA \/ PA + psz <= Ap)
    /\ (forall p Ap n pb PA psz, In (p, Ap, n) NEW -> In (pb, PA, psz) NEW -> p <> pb -> Ap + n <= PA \/ PA + psz <= Ap).
  Proof.
    intros until NEW. intros ((HEAP & _) & _).
    pose proof (LH_nodup _ _ _ HEAP) as ND.
    assert (FR : forall p Ap n, In (p, Ap, n) NEW -> ~ In p (map blk_id (OWX ++ LB))).
    { intros p Ap n Hq Hin. rewrite !map_app in ND. rewrite map_app in Hin. apply in_app_iff in Hin.
      pose proof (in_ids _ _ _ _ Hq) as IQ.
      destruct Hin as [Hin|Hin].
      - exact (NoDup_app_disjoint _ _ _ ND Hin ltac:(apply in_app_iff; left; exact IQ)).
      - destruct (NoDup_app_split _ _ ND) as (N23 & _ & _). exact (NoDup_app_disjoint _ _ _ N23 IQ Hin). }
    split; [exact HEAP|]. split; [exact ND|]. split; [intros p Ap n Hq; exact (blk_bounds _ _ _ p Ap n HEAP Hq)|]. split; [exact FR|]. split; [| split].
    - intros p Ap n pb PA psz Hq Hb. eapply (blk_disjoint _ _ _ p Ap n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; right; apply in_app_iff; right; exact Hb|].
      intros ->. apply (FR pb Ap n Hq). rewrite map_app. apply in_app_iff. right. exact (in_ids _ _ _ _ Hb).
    - intros p Ap n pb PA psz Hq Hb. eapply (blk_disjoint _ _ _ p Ap n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; left; exact Hb|].
      intros ->. apply (FR pb Ap n Hq). rewrite map_app. apply in_app_iff. left. exact (in_ids _ _ _ _ Hb).
    - intros p Ap n pb PA psz Hq Hb NE. eapply (blk_disjoint _ _ _ p Ap n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; right; apply in_app_iff; left; exact Hb| exact NE].
  Qed.

  (* [comment removed for export] *)
  Definition own_iv (NEW : list block) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ In iv XC \/ (exists p Ap n, In (p, Ap, n) NEW /\ Ap <= fst iv /\ snd iv <= Ap + n).

  Lemma einv_munch : forall q q' sX stX mX OWX errvX boX NEW mY W,
    einv q sX stX mX OWX errvX boX NEW ->
    munch W mX mY -> wmono ctusegs mX mY -> mem_inv ctusegs mY -> stk ctusegs mY lo q' -> lo <= q' <= bv_unsigned sp ->
    Forall (own_iv NEW) W ->
    einv q' sX stX mY OWX errvX boX NEW.
  Proof.
    intros until W. intros OI MU WM MI ST LOQ HW. pose proof SPR as SPR.
    pose proof (einv_facts _ _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO & _).
    destruct OI as ((HEAP & AS & IDS & DC & AUX & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    assert (INCL : forall b, In b OWX -> In b (OWX ++ NEW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW3 : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016)
               \/ (exists p Ap n, In (p, Ap, n) (OWX ++ NEW ++ LB) /\ ~ In p (map blk_id OWX) /\ Ap <= fst iv /\ snd iv <= Ap + n)) W).
    { eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[HX|(p & Ap & n & Hq & H1 & H2)]]; [left; exact H1| left| right; right].
      - pose proof (proj1 (Forall_forall _ _) XCB iv HX) as [X1 X2]. lia.
      - exists p, Ap, n. split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq|]. split; [| split; [exact H1| exact H2]].
        intros Hin. apply (FRESH p Ap n Hq). rewrite map_app. apply in_app_iff. left. exact Hin. }
    assert (HEAPY : RHEAP sX (OWX ++ NEW ++ LB) mY).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros [x y] [[H1 H2]|[HX|(p & Ap & n & Hq & H1 & H2)]]; cbn [fst snd] in *.
      - left. cbn. lia.
      - pose proof (proj1 (Forall_forall _ _) XCB _ HX) as [X1 X2]. cbn [fst snd] in X1, X2. left. cbn. lia.
      - right. right. exists (p, Ap, n). split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq| cbn; lia]. }
    assert (ERRY : rw_cells ctusegs mY 3355012 [C4 errvX]).
    { eapply rw_cells_transport; [exact ERR0| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply disjoint_from_forall.
      eapply Forall_impl; [| exact HW]. intros [x y] [[H1 H2]|[HX|(p & Ap & n & Hq & H1 & H2)]]; cbn [fst snd] in *; [lia| |].
      - pose proof (proj1 (Forall_forall _ _) XCB _ HX) as [X1 X2]. cbn [fst snd] in X1, X2. lia.
      - pose proof (BND p Ap n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). lia. }
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [exact SO| exact FA]]]]]].
    - split; [exact HEAPY|].
      split. { eapply (ap_state_of_munch_blk stX mX mY OWX E boX sX (OWX ++ NEW ++ LB)); [exact AS| exact HEAP| exact INCL| exact MU| exact WM| exact CEIL| unfold GLOBALS_TOP; exact GLO| exact HW3]. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch sX (OWX ++ NEW ++ LB) _ mX mY); [exact DC| intros i p k Hd; apply INCL; exact (proj1 (optb_ok_nth OWX _ i p k OD Hd))| exact HEAP| exact CEIL| exact MU| exact WM|].
               eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(p & Ap & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists p, Ap, n. split; [exact H1|]. split; [| exact H3]. intros i p' k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OWX _ i p' k OD Hd)). }
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
               intros iv [[H1 H2]|[HX|(p & Ap & n & Hq & H1 & H2)]]; cbn [fst snd] in *; [unfold RAUXV_CELL, GLOBALS_TOP in *; lia| |].
               - pose proof (proj1 (Forall_forall _ _) XCB _ HX) as [X1 X2]. unfold RAUXV_CELL. lia.
               - pose proof (BND p Ap n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). unfold RAUXV_CELL. lia. }
      split; [exact LOQ|]. split; [exact ST|]. split; [exact ERRY|].
      split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY| exact MI].
    - eapply lx_pres_trans; [exact LX|].
      eapply (lx_pres_munch_gen sX (OWX ++ NEW) LB W mX mY (bv_unsigned sp) X0 lo); [rewrite <- app_assoc; exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[HX|(p & Ap & n & Hq & H1 & H2)]]; [left; split; assumption| right; left| right; right].
      + pose proof (proj1 (Forall_forall _ _) XCB _ HX) as [X1 X2]. split; [lia|]. intros a Ha. apply rin_ivs_app. left. eapply rin_ivs_In; [exact HX| lia].
      + exists p, Ap, n. split; [apply in_app_iff; right; exact Hq| split; assumption].
    - eapply kept_trans; [exact KP|].
      eapply (kept_of_munch sX (OWX ++ NEW ++ LB) _ mX mY K lo); [exact HEAP| intros b Hb; apply INCL; apply KO; exact Hb| exact CEIL| exact MU|].
      eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(p & Ap & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
      exists p, Ap, n. split; [exact H1|]. split; [| exact H3]. intros Hin. apply H2. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). rewrite <- Eb. apply in_map. apply KO. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma einv_alloc : forall q sX stX mX OWX errvX boX NEW sY mY (errvY : word) pn A n,
    einv q sX stX mX OWX errvX boX NEW ->
    rheap_pres (OWX ++ NEW ++ LB) q mX mY ->
    RHEAP sY ((pn, A, n) :: OWX ++ NEW ++ LB) mY ->
    mem_inv ctusegs mY -> stk ctusegs mY lo q -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    einv q sY stX mY OWX errvY boX ((pn, A, n) :: NEW).
  Proof.
    intros until n. intros OI HP HEAPY MI ST ERR AUX FA' SO'. pose proof SPR as SPR.
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (HEAPY' : RHEAP sY (OWX ++ ((pn, A, n) :: NEW) ++ LB) mY) by (eapply RHEAP_perm; [exact HEAPY| apply Permutation_middle]).
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [rewrite SO'; exact SO| rewrite FA'; exact FA]]]]]].
    - split; [exact HEAPY'|].
      split; [eapply ap_state_heap_pres_app; [exact AS| exact HP]|].
      split; [exact IDS|].
      split. { eapply data_cells_heap_pres; [exact DC| exact HP|]. intros i p k Hd. apply in_app_iff. left. exact (proj1 (optb_ok_nth OWX _ i p k OD Hd)). }
      split; [exact AUX|]. split; [exact LOQ0|]. split; [exact ST|]. split; [exact ERR|].
      split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY'| exact MI].
    - eapply lx_pres_trans; [exact LX|]. eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HP| lia| | intros a Ha; exact Ha].
      intros b Hb. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
    - eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HP|]. intros b Hb. apply in_app_iff. left. apply KO. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma einv_heap : forall q sX stX mX OWX errvX boX NEW sY mY (errvY : word) L1 LY NEW',
    einv q sX stX mX OWX errvX boX NEW ->
    rheap_pres L1 q mX mY -> (forall b, In b OWX \/ In b LB -> In b L1) ->
    RHEAP sY LY mY -> Permutation LY (OWX ++ NEW' ++ LB) ->
    mem_inv ctusegs mY -> stk ctusegs mY lo q -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    einv q sY stX mY OWX errvY boX NEW'.
  Proof.
    intros until NEW'. intros OI HP HL1 HEAPY PM MI ST ERR AUX FA' SO'. pose proof SPR as SPR.
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (HEAPY' : RHEAP sY (OWX ++ NEW' ++ LB) mY) by (eapply RHEAP_perm; [exact HEAPY| exact PM]).
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [rewrite SO'; exact SO| rewrite FA'; exact FA]]]]]].
    - split; [exact HEAPY'|].
      split; [eapply ap_state_heap_pres; [exact AS| exact HP| intros b Hb; apply HL1; left; exact Hb]|].
      split; [exact IDS|].
      split. { eapply data_cells_heap_pres; [exact DC| exact HP|]. intros i p k Hd. apply HL1. left. exact (proj1 (optb_ok_nth OWX _ i p k OD Hd)). }
      split; [exact AUX|]. split; [exact LOQ0|]. split; [exact ST|]. split; [exact ERR|].
      split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY'| exact MI].
    - eapply lx_pres_trans; [exact LX|]. eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HP| lia| | intros a Ha; exact Ha].
      intros b Hb. apply HL1. right. exact Hb.
    - eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HP|]. intros b Hb. apply HL1. left. apply KO. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma einv_call : forall q sX stX mX OWX errvX boX NEW,
    einv q sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ rauxv_ok mX B /\ q <= B
    /\ stk ctusegs mX lo q /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
    /\ rw_cells ctusegs mX LX_ERRNO [C4 errvX] /\ mem_inv ctusegs mX /\ crypto_statics mX /\ realloc_statics mX /\ ap_state stX mX OWX E boX /\ ap_img mX
    /\ bv_unsigned (Z_to_bv 64 q) = q.
  Proof.
    intros until NEW. intros ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & _). pose proof SPR as SPR.
    pose proof AS as (_ & IMG & (CS & RS & _) & _).
    unfold LX_ERRNO, RATP. change (3355176 - 164) with 3355012.
    repeat (split; [first [assumption| unfold GLOBALS_TOP; lia]|]). apply unsigned_lit. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma einv_ap_pre : forall q sX stX mX OWX errvX boX NEW stack,
    einv q sX stX mX OWX errvX boX NEW -> q mod 16 = 0 -> lo <= q - stack ->
    ap_pre sX stX mX OWX (NEW ++ LB) E boX (Z_to_bv 64 q) lo B errvX canary stack
    /\ (forall b, In b K -> In b OWX) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids stX ++ env_ids E)).
  Proof.
    intros until stack. intros ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & _) Q16 LOS. pose proof SPR as SPR.
    assert (ESP : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    split; [| split; [exact KO| exact KI]].
    unfold ap_pre. rewrite ESP. unfold MallocRep.wz. rewrite EA.
    repeat (split; [first [assumption| unfold GLOBALS_TOP; lia]|]). exact Q16.
  Qed.

  (* [comment removed for export] *)
  Lemma einv_after : forall q sX stX mX OWX errvX boX NEW sY stY mY OWY (errvY : word) boY XX NEW2,
    einv q sX stX mX OWX errvX boX NEW ->
    ap_pre sY stY mY OWY (NEW2 ++ NEW ++ LB) E boY (Z_to_bv 64 q) lo B errvY canary 0 ->
    lx_pres (NEW ++ LB) (bv_unsigned (Z_to_bv 64 q)) (XX ++ LIBW_AP) mX mY ->
    (forall a, rin_ivs XX a -> (lo <= a < bv_unsigned sp) \/ rin_ivs XC a \/ (exists p Ap n, In (p, Ap, n) NEW /\ Ap <= a < Ap + n)) ->
    ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX ->
    blocks_kept K stY OWY mX mY ->
    einv q sY stY mY OWY errvY boY (NEW2 ++ NEW).
  Proof.
    intros until NEW2. intros OI PREY LXY HXX SO' FA' (BK1 & BK2 & BK3). pose proof SPR as SPR.
    pose proof (einv_facts _ _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO & _).
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    assert (ESP : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia). rewrite ESP in LXY.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXY) as AG.
    destruct PREY as (HEAPY & ASY & IDSY & DCY & AUXY & _ & _ & STY & _ & _ & _ & ERRY & SSPY & MIY & _). rewrite ESP in STY.
    unfold MallocRep.wz in ERRY. rewrite EA in ERRY.
    split; [| split; [| split; [exact BK1| split; [| split; [eapply kept_trans; [exact KP| exact BK3]| split; [rewrite SO'; exact SO| rewrite FA'; exact FA]]]]]].
    - split; [rewrite <- (app_assoc NEW2 NEW LB); exact HEAPY|]. split; [exact ASY|]. split; [exact IDSY|]. split; [exact DCY|]. split; [exact AUXY|]. split; [exact LOQ0|].
      split; [exact STY|]. split; [exact ERRY|]. split; [exact SSPY| exact MIY].
    - eapply lx_pres_trans; [exact LX|]. intros a Ha [HXa Hc]. apply (LXY a Ha).
      assert (NX : ~ rin_ivs (XX ++ LIBW_AP) a).
      { intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| apply HXa; apply rin_ivs_app; right; exact HIN].
        destruct (HXX a HIN) as [Hs|[Hs|(p & Ap & n & Hq & Hq2)]]; [| apply HXa; apply rin_ivs_app; left; exact Hs|].
        - destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | unfold GLOBALS_TOP in *; lia].
          destruct b as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in Hr.
          pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)). lia.
        - pose proof (BND p Ap n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)) as (B1 & B2 & B3 & B4 & B5).
          destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | unfold ralloc_static in Hc; lia].
          destruct b as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in Hr. pose proof (DJL p Ap n pb PA psz Hq Hb). lia. }
      split; [exact NX|].
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [left; lia| right; left; exists b; split; [apply in_app_iff; right; exact Hb| exact Hr]| right; right; exact Hc].
    - intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (BK2 b Hb Hin)|]. apply (KI b Hb). apply in_app_iff. right. exact Hin.
  Qed.

  Lemma einv_perm : forall q sX stX mX OWX errvX boX NEW NEW',
    Permutation NEW NEW' -> einv q sX stX mX OWX errvX boX NEW -> einv q sX stX mX OWX errvX boX NEW'.
  Proof.
    intros until NEW'. intros HPm ((HEAP & REST2) & REST). split; [| exact REST]. split; [| exact REST2].
    eapply RHEAP_perm; [exact HEAP|]. apply Permutation_app_head. apply Permutation_app_tail. exact HPm.
  Qed.

  (* [comment removed for export] *)
  Lemma einv_exit : forall sX stX mX OWX errvX boX NEW,
    einv (bv_unsigned sp) sX stX mX OWX errvX boX NEW -> bv_unsigned sp mod 16 = 0 ->
    ap_pre sX stX mX OWX (NEW ++ LB) E boX sp lo B errvX canary 0
    /\ lx_pres LB (bv_unsigned sp) X0 m mX /\ blocks_kept K stX OWX m mX /\ ps_so sX = ps_so s /\ ps_fa sX = ps_fa s
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB))).
  Proof.
    intros until NEW. intros OI SP16. pose proof SPR as SPR.
    pose proof (einv_facts _ _ _ _ _ _ _ _ OI) as (_ & _ & _ & FRESH & _).
    destruct OI as ((HEAP & AS & IDS & DC & AUX0 & LOQ0 & ST0 & ERR0 & SSP & MI0) & LX & KO & KI & KP & SO & FA).
    split; [| split; [exact LX| split; [split; [exact KO| split; [| exact KP]]| split; [exact SO| split; [exact FA|]]]]].
    - unfold ap_pre. unfold MallocRep.wz. rewrite EA. repeat (split; [first [assumption| unfold GLOBALS_TOP; lia]|]). exact SP16.
    - intros b Hb Hin. apply (KI b Hb). apply in_app_iff. left. exact Hin.
    - intros [[p Ap] n] Hb. exact (FRESH p Ap n Hb).
  Qed.
End Act.
End WithCeiling0.
