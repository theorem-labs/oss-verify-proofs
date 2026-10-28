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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk W_c2i_ibuf W_c2i_int W_prefix_create.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_free W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_ones64_neg : forall x, - 2 ^ 64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2 ^ 64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.
Lemma land_ones64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint afrees {A} (qs : list bptr) (t : aprog bptr A) : aprog bptr A := match qs with [] => t | q :: qs' => AFree q (afrees qs' t) end.
Fixpoint lfrees {A} (qs : list bptr) (t : lprog A) : lprog A := match qs with [] => t | q :: qs' => LFree q (lfrees qs' t) end.
Definition oid (o : option bptr) : list bptr := match o with Some q => [q] | None => [] end.
Definition sct_ids (x : sctr bptr) : list bptr :=
  oid (sc_logid x) ++ oid (option_map fst (sc_ext x)) ++ oid (option_map fst (sc_sig x)) ++ oid (option_map fst (sc_blob x)) ++ [sc_blk x].
Fixpoint scts_ids (l : list (sctr bptr)) : list bptr := match l with [] => [] | x :: t => sct_ids x ++ scts_ids t end.

Lemma afrees_app : forall {A} qs qs' (t : aprog bptr A), afrees (qs ++ qs') t = afrees qs (afrees qs' t).
Proof. intros A qs qs' t. induction qs as [|q qs IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma lfrees_app : forall {A} qs qs' (t : lprog A), lfrees (qs ++ qs') t = lfrees qs (lfrees qs' t).
Proof. intros A qs qs' t. induction qs as [|q qs IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma apbind_afrees : forall {A B} qs (t : aprog bptr A) (f : A -> aprog bptr B), apbind (afrees qs t) f = afrees qs (apbind t f).
Proof. intros A B qs t f. induction qs as [|q qs IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma ap_embed_afrees : forall {A} qs (t : aprog bptr A), ap_embed (afrees qs t) = lfrees qs (ap_embed t).
Proof. intros A qs t. induction qs as [|q qs IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma afree_opt_tree : forall (o : option bptr) (st0 : ap_st bptr), afree_opt o st0 = afrees (oid o) (ARet (tt, st0)).
Proof. intros [q|] st0; reflexivity. Qed.

Lemma sct_free_tree : forall (x : sctr bptr) (st0 : ap_st bptr), sct_free x st0 = afrees (sct_ids x) (ARet (tt, st0)).
Proof.
  intros x st0. unfold sct_free, sct_ids, abind. rewrite !afree_opt_tree, !apbind_afrees. cbn [apbind fst snd].
  rewrite !afree_opt_tree, !apbind_afrees. cbn [apbind fst snd]. rewrite !afree_opt_tree, !apbind_afrees. cbn [apbind fst snd].
  rewrite !afree_opt_tree, !apbind_afrees. cbn [apbind fst snd]. unfold afree. rewrite !afrees_app. reflexivity.
Qed.

Lemma scts_free_tree : forall (l : list (sctr bptr)) (st0 : ap_st bptr), scts_free l st0 = afrees (scts_ids l) (ARet (tt, st0)).
Proof.
  induction l as [|x t IH]; intros st0; cbn [scts_free scts_ids]; [reflexivity|].
  unfold abind. rewrite sct_free_tree, apbind_afrees. cbn [apbind fst snd]. rewrite IH, afrees_app. reflexivity.
Qed.

Lemma sk_free_all_tree : forall (k : skr bptr) (st0 : ap_st bptr),
  sk_free_all k st0 = afrees (scts_ids (sk_items k) ++ oid (option_map fst (sk_data k)) ++ [sk_blk k]) (ARet (tt, st0)).
Proof.
  intros k st0. unfold sk_free_all, abind. rewrite scts_free_tree, apbind_afrees. cbn [apbind fst snd].
  rewrite afree_opt_tree, apbind_afrees. cbn [apbind fst snd]. unfold afree. rewrite !afrees_app. reflexivity.
Qed.

Lemma lfree_sct_lfrees : forall {A} (x : sctr bptr) (t : lprog A), lfree_sct x t = lfrees (sct_ids x) t.
Proof.
  intros A x t. unfold lfree_sct, sct_ids. rewrite !lfrees_app.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|]; reflexivity.
Qed.
Lemma lfree_scts_lfrees : forall {A} (l : list (sctr bptr)) (t : lprog A), lfree_scts l t = lfrees (scts_ids l) t.
Proof. intros A l t. induction l as [|x r IH]; cbn [lfree_scts scts_ids]; [reflexivity|]. rewrite IH, lfree_sct_lfrees, lfrees_app. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ap_embed_sct_free : forall {A} (x : sctr bptr) (k : unit -> AM A) (st0 : ap_st bptr),
  ap_embed (abind (sct_free x) k st0) = lfree_sct x (ap_embed (k tt st0)).
Proof. intros A x k st0. unfold abind. rewrite sct_free_tree, apbind_afrees, ap_embed_afrees, lfree_sct_lfrees. reflexivity. Qed.

Lemma ap_embed_sk_free_all : forall {A} (k : skr bptr) (K : unit -> AM A) (st0 : ap_st bptr),
  ap_embed (abind (sk_free_all k) K st0) = lfree_scts (sk_items k) (lofree (option_map fst (sk_data k)) (LFree (sk_blk k) (ap_embed (K tt st0)))).
Proof.
  intros A k K st0. unfold abind at 1. rewrite sk_free_all_tree, apbind_afrees, ap_embed_afrees, !lfrees_app, lfree_scts_lfrees. cbn [apbind fst snd lfrees].
  destruct (sk_data k) as [[q n]|]; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lremove_app : forall od L1 L2, lremove od (L1 ++ L2) = lremove od L1 ++ lremove od L2.
Proof. intros [[q n]|] L1 L2; cbn [lremove]; [apply lb_remove_app| reflexivity]. Qed.

Lemma remove_sct_app : forall x L1 L2, remove_sct x (L1 ++ L2) = remove_sct x L1 ++ remove_sct x L2.
Proof. intros x L1 L2. unfold remove_sct. rewrite !lremove_app, lb_remove_app. reflexivity. Qed.

Lemma lremove_notin : forall od L, (match od with Some (q, _) => ~ In q (map blk_id L) | None => True end) -> lremove od L = L.
Proof. intros [[q n]|] L H; cbn [lremove]; [apply lb_remove_notin; exact H| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma remove_sct_notin : forall adr x L,
  (forall q, In q (map blk_id (sct_blocks adr x)) -> ~ In q (map blk_id L)) -> remove_sct x L = L.
Proof.
  intros adr x L H. unfold remove_sct. unfold sct_blocks in H. rewrite !map_app in H. cbn [map oblk blk_id fst snd app] in H.
  assert (HL : lremove (osz32 (sc_logid x)) L = L).
  { apply lremove_notin. destruct (sc_logid x) as [l|]; cbn; [| exact I]. apply H. left. reflexivity. }
  rewrite HL.
  assert (HE : lremove (sc_ext x) L = L).
  { apply lremove_notin. destruct (sc_ext x) as [[e en]|]; [| exact I]. apply H. rewrite !in_app_iff. right. left. left. reflexivity. }
  rewrite HE.
  assert (HG : lremove (sc_sig x) L = L).
  { apply lremove_notin. destruct (sc_sig x) as [[g gn]|]; [| exact I]. apply H. rewrite !in_app_iff. right. right. left. left. reflexivity. }
  rewrite HG.
  assert (HB : lremove (sc_blob x) L = L).
  { apply lremove_notin. destruct (sc_blob x) as [[b bn]|]; [| exact I]. apply H. rewrite !in_app_iff. right. right. right. left. left. reflexivity. }
  rewrite HB. apply lb_remove_notin. apply H. rewrite !in_app_iff. right. right. right. right. left. reflexivity.
Qed.

Lemma remove_sct_self : forall adr x, List.NoDup (map blk_id (sct_blocks adr x)) -> remove_sct x (sct_blocks adr x) = [].
Proof.
  intros adr x ND. unfold remove_sct, sct_blocks in *.
  destruct (sc_logid x) as [l|]; destruct (sc_ext x) as [[e en]|]; destruct (sc_sig x) as [[g gn]|]; destruct (sc_blob x) as [[b bn]|];
    cbn [osz32 option_map oblk app lremove map blk_id fst snd] in *;
    repeat (rewrite lb_remove_hd; [| assumption]; match goal with H : List.NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H; destruct H as [_ H] end);
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma remove_sct_fresh : forall adr x (OWX LB : list block),
  List.NoDup (map blk_id (OWX ++ sct_blocks adr x ++ LB)) -> remove_sct x (OWX ++ sct_blocks adr x ++ LB) = OWX ++ LB.
Proof.
  intros adr x OWX LB ND. rewrite (remove_sct_app x OWX), (remove_sct_app x (sct_blocks adr x) LB).
  rewrite (map_app blk_id OWX), (map_app blk_id (sct_blocks adr x) LB) in ND.
  pose proof (NoDup_app_split _ _ ND) as (N23 & D1 & N1). pose proof (NoDup_app_split _ _ N23) as (N3 & D2 & N2).
  rewrite (remove_sct_notin adr x OWX), (remove_sct_self adr x N2), (remove_sct_notin adr x LB); [reflexivity| |].
  - intros q Hq Hin. exact (D2 q Hq Hin).
  - intros q Hq Hin. apply (D1 q Hin). apply in_app_iff. left. exact Hq.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma got_of_state : forall st m OW E bo, ap_state st m OW E bo -> ro_cells ctusegs m SCT_FREE_GOT [C8 (wz SCT_FREE_VA)].
Proof.
  intros st m OW E bo (_ & _ & SF & _). destruct SF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G). exact G.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Act.
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block).
  Variables (c : list Z) (D PIN OFS STK : Z).      (* [comment removed for export] *)
  Hypothesis DF : Forall (fun b => 0 <= b < 256) c.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LO : lo <= bv_unsigned sp + OFS - STK.
  Hypothesis STK0 : 0 <= STK.
  Hypothesis OFS0 : OFS <= 0.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis OFS16 : OFS mod 16 = 0.
  Hypothesis PINlo : bv_unsigned sp <= PIN.
  Hypothesis PINhi : PIN + 8 <= B.
  Hypothesis PBX : c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz.
  Hypothesis D0 : 0 <= D.

  Local Notation X0 := ([(PIN, PIN + 8)] ++ LIBW_AP) (only parsing).

  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma DLEN : Z.of_nat (length (to_bytes c)) = zlength c.
  Proof. apply zlength_to_bytes. Qed.
  Lemma ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS)) = bv_unsigned sp + OFS.
  Proof using B63 GLO LO OFS0 SPB STK0. pose proof SPR. apply unsigned_lit; lia. Qed.
  Lemma SPO : (bv_unsigned sp + OFS) mod 16 = 0.
  Proof using OFS16 SP16. clear - SP16 OFS16. rewrite Z.add_mod, SP16, OFS16 by lia. reflexivity. Qed.
  Lemma EA : errno_addr (Z_to_bv 64 RATP) = 3355012.
  Proof. clear. unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity. Qed.

  Definition oinv (sX : PState) (stX : ap_st bptr) (mX : mem) (OWX : list block) (errvX : word) (boX : Z * Z) (NEW : list block) : Prop :=
    ap_pre sX stX mX OWX (NEW ++ LB) E boX (Z_to_bv 64 (bv_unsigned sp + OFS)) lo B errvX canary STK
    /\ lx_pres LB (bv_unsigned sp) X0 m mX
    /\ (forall b, In b K -> In b OWX) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids stX ++ env_ids E)) /\ kept K m mX
    /\ ps_so sX = ps_so s /\ ps_fa sX = ps_fa s
    /\ bytes_at ctusegs mX D (to_bytes c).

  (* [comment removed for export] *)
  Lemma oinv_entry : forall st OW bo errv,
    ap_pre s st m OW LB E bo sp lo B errv canary (- OFS + STK) ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    bytes_at ctusegs m D (to_bytes c) ->
    oinv s st m OW errv bo [].
  Proof using B63 CEIL GLO LO OFS0 OFS16 PINhi PINlo SP16 SPB STK0.
    intros st OW bo errv PRE KOW KIDS HB. pose proof SPR as SPR. pose proof ESP as ESP.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16').
    destruct (stk_carve ctusegs m lo (bv_unsigned sp) (Z.to_nat (- OFS)) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [ST' _]. rewrite Z2Nat.id in ST' by lia.
    split; [| split; [apply lx_pres_refl| split; [exact KOW| split; [exact KIDS| split; [apply kept_refl| split; [reflexivity| split; [reflexivity| exact HB]]]]]]].
    unfold ap_pre. cbn [app]. rewrite ESP.
    split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact AUX|]. split; [lia|]. split; [lia|].
    split; [replace (bv_unsigned sp + OFS) with (bv_unsigned sp - - OFS) by lia; exact ST'|].
    split; [exact CEIL|]. split; [exact GLO'|]. split; [lia|]. split; [exact ERR|]. split; [exact SSP|]. split; [exact MI|]. exact SPO.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_facts : forall sX stX mX OWX errvX boX NEW,
    oinv sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ List.NoDup (map blk_id (OWX ++ NEW ++ LB))
    /\ (forall q Aq n, In (q, Aq, n) (OWX ++ NEW ++ LB) -> 0 < Aq /\ 0 <= n /\ Aq + n <= alloc_ceiling /\ (Aq + n <= 0x10000 \/ 0x355000 <= Aq) /\ Aq mod 16 = 0)
    /\ (forall q Aq n, In (q, Aq, n) NEW -> ~ In q (map blk_id (OWX ++ LB)))
    /\ (forall q Aq n pb PA psz, In (q, Aq, n) NEW -> In (pb, PA, psz) LB -> Aq + n <= PA \/ PA + psz <= Aq)
    /\ (forall q Aq n pb PA psz, In (q, Aq, n) NEW -> In (pb, PA, psz) OWX -> Aq + n <= PA \/ PA + psz <= Aq).
  Proof.
    intros until NEW. intros (PREX & _). destruct PREX as (HEAP & _).
    pose proof (LH_nodup _ _ _ HEAP) as ND.
    assert (FR : forall q Aq n, In (q, Aq, n) NEW -> ~ In q (map blk_id (OWX ++ LB))).
    { intros q Aq n Hq Hin. rewrite !map_app in ND. rewrite map_app in Hin. apply in_app_iff in Hin.
      pose proof (in_ids _ _ _ _ Hq) as IQ.
      destruct Hin as [Hin|Hin].
      - exact (NoDup_app_disjoint _ _ _ ND Hin ltac:(apply in_app_iff; left; exact IQ)).
      - destruct (NoDup_app_split _ _ ND) as (N23 & _ & _). exact (NoDup_app_disjoint _ _ _ N23 IQ Hin). }
    split; [exact HEAP|]. split; [exact ND|]. split; [intros q Aq n Hq; exact (blk_bounds _ _ _ q Aq n HEAP Hq)|]. split; [exact FR|]. split.
    - intros q Aq n pb PA psz Hq Hb. eapply (blk_disjoint _ _ _ q Aq n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; right; apply in_app_iff; right; exact Hb|].
      intros ->. apply (FR pb Aq n Hq). rewrite map_app. apply in_app_iff. right. exact (in_ids _ _ _ _ Hb).
    - intros q Aq n pb PA psz Hq Hb. eapply (blk_disjoint _ _ _ q Aq n pb PA psz HEAP); [apply in_app_iff; right; apply in_app_iff; left; exact Hq| apply in_app_iff; left; exact Hb|].
      intros ->. apply (FR pb Aq n Hq). rewrite map_app. apply in_app_iff. left. exact (in_ids _ _ _ _ Hb).
  Qed.

  (* [comment removed for export] *)
  Definition own_iv (NEW : list block) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ iv = (PIN, PIN + 8) \/ (exists q Aq n, In (q, Aq, n) NEW /\ Aq <= fst iv /\ snd iv <= Aq + n).

  Lemma oinv_munch : forall sX stX mX OWX errvX boX NEW mY W,
    oinv sX stX mX OWX errvX boX NEW ->
    munch W mX mY -> wmono ctusegs mX mY -> mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + OFS) ->
    rw_cells ctusegs mY 3355012 [C4 errvX] ->
    Forall (own_iv NEW) W ->
    oinv sX stX mY OWX errvX boX NEW.
  Proof using B63 CEIL GLO LO OFS0 OFS16 PBX PINhi PINlo SP16 SPB STK0.
    intros until W. intros OI MU WM MI ST ERR HW. pose proof SPR as SPR. pose proof DLEN as DLEN.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *.
    assert (INCL : forall b, In b OWX -> In b (OWX ++ NEW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW3 : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016)
               \/ (exists q Aq n, In (q, Aq, n) (OWX ++ NEW ++ LB) /\ ~ In q (map blk_id OWX) /\ Aq <= fst iv /\ snd iv <= Aq + n)) W).
    { eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[->|(q & Aq & n & Hq & H1 & H2)]]; [left; exact H1| left; cbn; lia| right; right].
      exists q, Aq, n. split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq|]. split; [| split; [exact H1| exact H2]].
      intros Hin. apply (FRESH q Aq n Hq). rewrite map_app. apply in_app_iff. left. exact Hin. }
    assert (HEAPY : RHEAP sX (OWX ++ NEW ++ LB) mY).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros [x y] [[H1 H2]|[E0|(q & Aq & n & Hq & H1 & H2)]]; cbn [fst snd] in *.
      - left. cbn. lia.
      - injection E0; intros -> ->. left. cbn. lia.
      - right. right. exists (q, Aq, n). split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq| cbn; lia]. }
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [exact SO| split; [exact FA|]]]]]]].
    - unfold ap_pre. rewrite ESP. split; [exact HEAPY|].
      split. { eapply (ap_state_of_munch_blk stX mX mY OWX E boX sX (OWX ++ NEW ++ LB)); [exact AS| exact HEAP| exact INCL| exact MU| exact WM| exact CEIL| unfold GLOBALS_TOP; exact GLO| exact HW3]. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch sX (OWX ++ NEW ++ LB) _ mX mY); [exact DC| intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OWX _ i q k OD Hd))| exact HEAP| exact CEIL| exact MU| exact WM|].
               eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros i q' k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OWX _ i q' k OD Hd)). }
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
               intros iv [[H1 H2]|[->|(q & Aq & n & Hq & H1 & H2)]]; cbn [fst snd] in *; [unfold RAUXV_CELL, GLOBALS_TOP in *; lia| unfold RAUXV_CELL; cbn; lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). unfold RAUXV_CELL. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [exact LO'|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY|].
      split; [exact MI| exact SP16'].
    - eapply lx_pres_trans; [exact LX|].
      eapply (lx_pres_munch_gen sX (OWX ++ NEW) LB W mX mY (bv_unsigned sp) X0 lo); [rewrite <- app_assoc; exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[->|(q & Aq & n & Hq & H1 & H2)]]; [left; split; assumption| right; left| right; right].
      + split; [cbn; lia|]. intros a Ha. cbn [fst snd] in Ha. cbn. left. lia.
      + exists q, Aq, n. split; [apply in_app_iff; right; exact Hq| split; assumption].
    - eapply kept_trans; [exact KP|].
      eapply (kept_of_munch sX (OWX ++ NEW ++ LB) _ mX mY K lo); [exact HEAP| intros b Hb; apply INCL; apply KO; exact Hb| exact CEIL| exact MU|].
      eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
      exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros Hin. apply H2. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). rewrite <- Eb. apply in_map. apply KO. exact Hb.
    - destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)].
      { rewrite E0 in HB |- *. destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. lia. }
      eapply bytes_at_transport; [exact HB| exact MU|]. rewrite DLEN.
      pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (_ & _ & PB3 & _).
      clear - HW DJL HPB PB1 PB2 PB3 CEIL LO D0 PINlo STK0 OFS0. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
      cbn [disjoint_from]. split; [| apply IH; exact H2]. unfold own_iv in H1. cbn [fst snd] in H1.
      destruct H1 as [[H1 H3]|[E0|(q & Aq & n & Hq & H1 & H3)]]; [cbn; lia| injection E0; intros -> ->; cbn; lia|].
      pose proof (DJL q Aq n pb PA psz Hq HPB). cbn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_alloc : forall sX stX mX OWX errvX boX NEW sY mY (errvY : word) pn A n,
    oinv sX stX mX OWX errvX boX NEW ->
    rheap_pres (OWX ++ NEW ++ LB) (bv_unsigned sp + OFS) mX mY ->
    RHEAP sY ((pn, A, n) :: OWX ++ NEW ++ LB) mY ->
    mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + OFS) -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    oinv sY stX mY OWX errvY boX ((pn, A, n) :: NEW).
  Proof using B63 CEIL GLO LO OFS0 PBX SPB STK0.
    intros until n. intros OI HP HEAPY MI ST ERR AUX FA' SO'. pose proof SPR as SPR. pose proof DLEN as DLEN.
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct PREX as (HEAP & AS & IDS & DC & AUX0 & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (HEAPY' : RHEAP sY (OWX ++ ((pn, A, n) :: NEW) ++ LB) mY) by (eapply RHEAP_perm; [exact HEAPY| apply Permutation_middle]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [rewrite SO'; exact SO| split; [rewrite FA'; exact FA|]]]]]]].
    - unfold ap_pre. rewrite ESP. split; [exact HEAPY'|].
      split; [eapply ap_state_heap_pres_app; [exact AS| exact HP]|].
      split; [exact IDS|].
      split. { eapply data_cells_heap_pres; [exact DC| exact HP|]. intros i q k Hd. apply in_app_iff. left. exact (proj1 (optb_ok_nth OWX _ i q k OD Hd)). }
      split; [exact AUX|]. split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [exact GLO'|]. split; [exact LO'|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY'|].
      split; [exact MI| exact SP16'].
    - eapply lx_pres_trans; [exact LX|]. eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HP| lia| | intros a Ha; exact Ha].
      intros b Hb. apply in_app_iff. right. apply in_app_iff. right. exact Hb.
    - eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HP|]. intros b Hb. apply in_app_iff. left. apply KO. exact Hb.
    - destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)].
      { rewrite E0 in HB |- *. destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. lia. }
      eapply bytes_at_agree; [exact AG| exact HB|]. intros a Ha. rewrite DLEN in Ha. right. right. exists (pb, PA, psz).
      split; [apply in_app_iff; right; apply in_app_iff; right; exact HPB| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_call : forall sX stX mX OWX errvX boX NEW,
    oinv sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ rauxv_ok mX B /\ bv_unsigned sp + OFS <= B
    /\ stk ctusegs mX lo (bv_unsigned sp + OFS) /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
    /\ rw_cells ctusegs mX LX_ERRNO [C4 errvX] /\ mem_inv ctusegs mX /\ crypto_statics mX /\ ap_state stX mX OWX E boX.
  Proof using B63 GLO LO OFS0 SPB STK0.
    intros until NEW. intros (PREX & _). pose proof SPR as SPR. pose proof DLEN as DLEN.
    destruct PREX as (HEAP & AS & IDS & DC & AUX0 & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *. pose proof AS as (_ & _ & (CS & _) & _).
    unfold MallocRep.wz in ERR0. rewrite EA in ERR0.
    repeat (split; [first [assumption| lia]|]). exact AS.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_after : forall sX stX mX OWX errvX boX NEW sY stY mY OWY (errvY : word) boY XX NEW2,
    oinv sX stX mX OWX errvX boX NEW ->
    ap_pre sY stY mY OWY (NEW2 ++ NEW ++ LB) E boY (Z_to_bv 64 (bv_unsigned sp + OFS)) lo B errvY canary 0 ->
    lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) (XX ++ LIBW_AP) mX mY ->
    (forall a, rin_ivs XX a -> (bv_unsigned sp + OFS <= a < bv_unsigned sp) \/ (PIN <= a < PIN + 8) \/ (exists q Aq n, In (q, Aq, n) NEW /\ Aq <= a < Aq + n)) ->
    ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX ->
    blocks_kept K stY OWY mX mY ->
    oinv sY stY mY OWY errvY boY (NEW2 ++ NEW).
  Proof using B63 CEIL GLO LO OFS0 OFS16 PBX PINlo SPB STK0.
    intros until NEW2. intros OI PREY LXY HXX SO' FA' (BK1 & BK2 & BK3). pose proof SPR as SPR. pose proof DLEN as DLEN.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXY) as AG.
    assert (CL : forall a, in_block LB a -> ~ rin_ivs LIBW_AP a -> lx_client (NEW ++ LB) (bv_unsigned sp + OFS) (XX ++ LIBW_AP) a).
    { intros a (b & Hb & Hr) HX. destruct b as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in Hr.
      pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)) as (B1 & B2 & B3 & B4 & B5).
      split.
      - intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| exact (HX HIN)].
        destruct (HXX a HIN) as [Hs|[Hs|(q & Aq & n & Hq & Ha)]]; [lia| lia|]. pose proof (DJL q Aq n pb PA psz Hq Hb). lia.
      - right. left. exists (pb, PA, psz). split; [apply in_app_iff; right; exact Hb| cbn; lia]. }
    split; [rewrite <- app_assoc; eapply ap_pre_restack; [exact PREY| rewrite ESP; lia]|].
    split. { eapply lx_pres_trans; [exact LX|]. intros a Ha [HXa Hc]. apply (LXY a Ha). cbn [rin_ivs fst snd app] in HXa.
             destruct Hc as [Hc|[Hblk|Hc]].
             - split; [| left; lia]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| apply HXa; right; exact HIN].
               destruct (HXX a HIN) as [Hs|[Hs|(q & Aq & n & Hq & Hq2)]]; [lia| apply HXa; left; cbn; lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). lia.
             - apply CL; [exact Hblk| intros HIN; apply HXa; right; exact HIN].
             - split; [| right; right; exact Hc]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| apply HXa; right; exact HIN].
               destruct (HXX a HIN) as [Hs|[Hs|(q & Aq & n & Hq & Hq2)]]; [unfold GLOBALS_TOP in *; lia| unfold GLOBALS_TOP in *; lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). unfold ralloc_static in Hc. lia. }
    split; [exact BK1|]. split.
    { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (BK2 b Hb Hin)|]. apply (KI b Hb). apply in_app_iff. right. exact Hin. }
    split; [eapply kept_trans; [exact KP| exact BK3]|].
    split; [rewrite SO'; exact SO|]. split; [rewrite FA'; exact FA|].
    destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)].
    { rewrite E0 in HB |- *. destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. lia. }
    pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (B1 & B2 & B3 & B4 & B5).
    eapply bytes_at_agree; [exact AG| exact HB|]. intros a Ha. rewrite DLEN in Ha. apply CL.
    - exists (pb, PA, psz). split; [exact HPB| cbn; lia].
    - unfold LIBW_AP. cbn [rin_ivs fst snd]. lia.
  Qed.

  Lemma oinv_perm : forall sX stX mX OWX errvX boX NEW NEW',
    Permutation NEW NEW' -> oinv sX stX mX OWX errvX boX NEW -> oinv sX stX mX OWX errvX boX NEW'.
  Proof.
    intros until NEW'. intros HPm (PREX & REST). split; [| exact REST].
    destruct PREX as (HEAP & REST2). split; [| exact REST2].
    eapply RHEAP_perm; [exact HEAP|]. apply Permutation_app_head. apply Permutation_app_tail. exact HPm.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_resp : forall sF (st' : ap_st bptr) mX OW' LB' (errv' : word) boX stk0,
    ap_pre sF st' mX OW' LB' E boX (Z_to_bv 64 (bv_unsigned sp + OFS)) lo B errv' canary stk0 ->
    stk ctusegs mX lo (bv_unsigned sp) ->
    ap_pre sF st' mX OW' LB' E boX sp lo B errv' canary 0.
  Proof using LO OFS0 SP16 SPB STK0 c.
    intros until stk0. intros PREX ST4. pose proof SPR as SPR. pose proof DLEN as DLEN.
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    unfold ap_pre. repeat (split; [first [assumption|lia]|]). exact SP16.
  Qed.

  (* [comment removed for export] *)
  Lemma sct_rep_munch : forall sX L mX mY W adr1 x1,
    sct_rep mX L adr1 x1 -> RHEAP sX L mX -> munch W mX mY -> wmono ctusegs mX mY ->
    Forall (fun iv : Z * Z => alloc_ceiling <= fst iv) W -> sct_rep mY L adr1 x1.
  Proof using OFS sp.
    intros sX L mX mY W adr1 x1 (H1 & H2 & H3 & H4 & H5 & H6 & REST) HEAP MU WM HW.
    assert (DJ : forall q Aq n k, In (q, Aq, n) L -> 0 <= k <= n -> disjoint_from W Aq k).
    { intros q Aq n k Hq Hk. pose proof (blk_bounds _ _ _ q Aq n HEAP Hq) as (B1 & B2 & B3 & B4 & B5). clear - HW Hk B3.
      induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [Hx HW]. cbn [fst] in Hx. cbn. split; [lia| apply IH; exact HW]. }
    assert (AR : forall o, arr_rep mX L adr1 o -> arr_rep mY L adr1 o).
    { intros [[q n]|] Ho; cbn in *; [| exact I]. destruct Ho as (Hn & HL & bs & HC). split; [exact Hn|]. split; [exact HL|]. exists bs.
      eapply rw_cells_transport; [exact HC| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply DJ; [exact HL| lia]. }
    split; [exact H1|]. split.
    { eapply rw_cells_transport; [exact H2| exact MU| exact WM|]. rewrite sct_cells_size. eapply DJ; [exact H1| unfold SCT_SIZE; lia]. }
    split; [apply AR; exact H3|]. split; [apply AR; exact H4|]. split; [apply AR; exact H5|]. split; [apply AR; exact H6|]. exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_heap : forall sX stX mX OWX errvX boX NEW sY mY (errvY : word) L1 LY NEW',
    oinv sX stX mX OWX errvX boX NEW ->
    rheap_pres L1 (bv_unsigned sp + OFS) mX mY -> (forall b, In b OWX \/ In b LB -> In b L1) ->
    RHEAP sY LY mY -> Permutation LY (OWX ++ NEW' ++ LB) ->
    mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + OFS) -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    oinv sY stX mY OWX errvY boX NEW'.
  Proof using B63 CEIL GLO LO OFS0 PBX SPB STK0.
    intros until NEW'. intros OI HP HL1 HEAPY PM MI ST ERR AUX FA' SO'. pose proof SPR as SPR. pose proof DLEN as DLEN.
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & _).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct PREX as (HEAP & AS & IDS & DC & AUX0 & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *.
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    unfold LX_ERRNO, RATP in ERR. change (3355176 - 164) with 3355012 in ERR.
    assert (HEAPY' : RHEAP sY (OWX ++ NEW' ++ LB) mY) by (eapply RHEAP_perm; [exact HEAPY| exact PM]).
    pose proof (agree_of_heap_pres _ _ _ _ HP) as AG.
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [rewrite SO'; exact SO| split; [rewrite FA'; exact FA|]]]]]]].
    - unfold ap_pre. rewrite ESP. split; [exact HEAPY'|].
      split; [eapply ap_state_heap_pres; [exact AS| exact HP| intros b Hb; apply HL1; left; exact Hb]|].
      split; [exact IDS|].
      split. { eapply data_cells_heap_pres; [exact DC| exact HP|]. intros i q k Hd. apply HL1. left. exact (proj1 (optb_ok_nth OWX _ i q k OD Hd)). }
      split; [exact AUX|]. split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [exact GLO'|]. split; [exact LO'|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY'|].
      split; [exact MI| exact SP16'].
    - eapply lx_pres_trans; [exact LX|]. eapply lx_pres_weaken; [eapply lx_pres_of_heap_pres; exact HP| lia| | intros a Ha; exact Ha].
      intros b Hb. apply HL1. right. exact Hb.
    - eapply kept_trans; [exact KP|]. eapply kept_of_heap_pres; [exact HP|]. intros b Hb. apply HL1. left. apply KO. exact Hb.
    - destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)].
      { rewrite E0 in HB |- *. destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. lia. }
      eapply bytes_at_agree; [exact AG| exact HB|]. intros a Ha. rewrite DLEN in Ha. right. right. exists (pb, PA, psz).
      split; [apply HL1; right; exact HPB| cbn; lia].
  Qed.
End Act.
End WithCeiling0.
