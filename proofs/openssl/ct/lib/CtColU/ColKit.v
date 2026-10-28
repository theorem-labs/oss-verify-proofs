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


(* [comment removed for export] *)
Lemma land_ones64_neg : forall x, - 2 ^ 64 <= x < 0 -> Z.land x 18446744073709551615 = x + 2 ^ 64.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land_ones64_small : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a <-> rin_ivs X a \/ rin_ivs Y a.
Proof. intros X Y a. induction X as [|iv X IH]; cbn [rin_ivs app]; [tauto|]. rewrite IH. tauto. Qed.
Lemma rin_ivs_In : forall X a, rin_ivs X a <-> exists iv, In iv X /\ fst iv <= a < snd iv.
Proof.
  intros X a. induction X as [|iv X IH]; cbn [rin_ivs].
  - split; [intros []| intros (iv & [] & _)].
  - rewrite IH. split.
    + intros [H|(iv' & H1 & H2)]; [exists iv; split; [left; reflexivity| exact H]| exists iv'; split; [right; exact H1| exact H2]].
    + intros (iv' & [<-|H1] & H2); [left; exact H2| right; exists iv'; split; [exact H1| exact H2]].
Qed.

(* [comment removed for export] *)
Lemma lx_pres_up : forall (L : list block) (SP SP' : Z) (X X' : list (Z * Z)) (m m' : mem) (lo : Z),
  lx_pres L SP X m m' -> SP <= SP' ->
  (forall q A n, In (q, A, n) L -> A + n <= lo) -> 3493888 <= lo ->
  (forall a, rin_ivs X a -> rin_ivs X' a \/ (lo <= a < SP')) ->
  lx_pres L SP' X' m m'.
Proof.
  intros L SP SP' X X' m m' lo H HS HB GLO HX a Ha [HXa Hc]. apply H; [exact Ha|]. split.
  - intros HIN. destruct (HX a HIN) as [H1|H1]; [exact (HXa H1)|].
    destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | unfold ralloc_static in Hc; lia].
    destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr. pose proof (HB q A n Hb). lia.
  - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Act.
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)) (OFS STK : Z).  (* [comment removed for export] *)
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
  Hypothesis XPok : Forall (fun iv : Z * Z => bv_unsigned sp <= fst iv /\ snd iv <= B) XP.
  Hypothesis PBX : c = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength c <= PA + psz.
  Hypothesis D0 : 0 <= D.

  Local Notation X0 := (XP ++ LIBW_AP) (only parsing).

  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.
  Lemma DLEN : Z.of_nat (length (to_bytes c)) = zlength c.
  Proof. apply zlength_to_bytes. Qed.
  Lemma ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS)) = bv_unsigned sp + OFS.
  Proof. pose proof SPR. apply unsigned_lit; lia. Qed.
  Lemma SPO : (bv_unsigned sp + OFS) mod 16 = 0.
  Proof. clear - SP16 OFS16. rewrite Z.add_mod, SP16, OFS16 by lia. reflexivity. Qed.
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
  Proof.
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
    (lo <= fst iv /\ snd iv <= bv_unsigned sp) \/ In iv XP \/ (exists q Aq n, In (q, Aq, n) NEW /\ Aq <= fst iv /\ snd iv <= Aq + n).

  Lemma oinv_munch : forall sX stX mX OWX errvX boX NEW mY W,
    oinv sX stX mX OWX errvX boX NEW ->
    munch W mX mY -> wmono ctusegs mX mY -> mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + OFS) ->
    rw_cells ctusegs mY 3355012 [C4 errvX] ->
    Forall (own_iv NEW) W ->
    oinv sX stX mY OWX errvX boX NEW.
  Proof.
    intros until W. intros OI MU WM MI ST ERR HW. pose proof SPR as SPR. pose proof DLEN as DLEN.
    assert (XPF : forall iv, In iv XP -> bv_unsigned sp <= fst iv /\ snd iv <= B) by (intros iv Hiv; exact (proj1 (Forall_forall _ _) XPok iv Hiv)).
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    pose proof ESP as ESP. rewrite ESP in *.
    assert (INCL : forall b, In b OWX -> In b (OWX ++ NEW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW3 : Forall (fun iv : Z * Z => lo <= fst iv \/ iv = (3355012, 3355016)
               \/ (exists q Aq n, In (q, Aq, n) (OWX ++ NEW ++ LB) /\ ~ In q (map blk_id OWX) /\ Aq <= fst iv /\ snd iv <= Aq + n)) W).
    { eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[HX|(q & Aq & n & Hq & H1 & H2)]]; [left; exact H1| left; pose proof (XPF iv HX); cbn; lia| right; right].
      exists q, Aq, n. split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq|]. split; [| split; [exact H1| exact H2]].
      intros Hin. apply (FRESH q Aq n Hq). rewrite map_app. apply in_app_iff. left. exact Hin. }
    assert (HEAPY : RHEAP sX (OWX ++ NEW ++ LB) mY).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
      intros [x y] [[H1 H2]|[E0|(q & Aq & n & Hq & H1 & H2)]]; cbn [fst snd] in *.
      - left. cbn. lia.
      - pose proof (XPF _ E0) as [X1 X2]. cbn [fst snd] in X1, X2. left. cbn. lia.
      - right. right. exists (q, Aq, n). split; [apply in_app_iff; right; apply in_app_iff; left; exact Hq| cbn; lia]. }
    split; [| split; [| split; [exact KO| split; [exact KI| split; [| split; [exact SO| split; [exact FA|]]]]]]].
    - unfold ap_pre. rewrite ESP. split; [exact HEAPY|].
      split. { eapply (ap_state_of_munch_blk stX mX mY OWX E boX sX (OWX ++ NEW ++ LB)); [exact AS| exact HEAP| exact INCL| exact MU| exact WM| exact CEIL| unfold GLOBALS_TOP; exact GLO| exact HW3]. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch sX (OWX ++ NEW ++ LB) _ mX mY); [exact DC| intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OWX _ i q k OD Hd))| exact HEAP| exact CEIL| exact MU| exact WM|].
               eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
               exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros i q' k Hd E0. apply H2. rewrite <- E0. eapply in_ids. exact (proj1 (optb_ok_nth OWX _ i q' k OD Hd)). }
      split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact HW].
               intros iv [[H1 H2]|[HX|(q & Aq & n & Hq & H1 & H2)]]; cbn [fst snd] in *; [unfold RAUXV_CELL, GLOBALS_TOP in *; lia| pose proof (XPF iv HX); unfold RAUXV_CELL, GLOBALS_TOP in *; lia|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). unfold RAUXV_CELL. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [exact LO'|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAPY|].
      split; [exact MI| exact SP16'].
    - eapply lx_pres_trans; [exact LX|].
      eapply (lx_pres_munch_gen sX (OWX ++ NEW) LB W mX mY (bv_unsigned sp) X0 lo); [rewrite <- app_assoc; exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros iv [[H1 H2]|[HX|(q & Aq & n & Hq & H1 & H2)]]; [left; split; assumption| right; left| right; right].
      + pose proof (XPF iv HX). split; [lia|]. intros a Ha. apply rin_ivs_app. left. apply rin_ivs_In. exists iv. split; [exact HX| exact Ha].
      + exists q, Aq, n. split; [apply in_app_iff; right; exact Hq| split; assumption].
    - eapply kept_trans; [exact KP|].
      eapply (kept_of_munch sX (OWX ++ NEW ++ LB) _ mX mY K lo); [exact HEAP| intros b Hb; apply INCL; apply KO; exact Hb| exact CEIL| exact MU|].
      eapply Forall_impl; [| exact HW3]. intros iv [Hx|[Hx|(q & Aq & n & H1 & H2 & H3)]]; [left; exact Hx| right; left; exact Hx| right; right].
      exists q, Aq, n. split; [exact H1|]. split; [| exact H3]. intros Hin. apply H2. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb). rewrite <- Eb. apply in_map. apply KO. exact Hb.
    - destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)].
      { rewrite E0 in HB |- *. destruct HB as (HB0 & HB1 & _). split; [exact HB0|]. split; [exact HB1|]. intros i Hi. cbn in Hi. lia. }
      eapply bytes_at_transport; [exact HB| exact MU|]. rewrite DLEN.
      pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (_ & _ & PB3 & _).
      clear - HW DJL HPB PB1 PB2 PB3 CEIL LO D0 XPF STK0 OFS0. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
      cbn [disjoint_from]. split; [| apply IH; exact H2]. unfold own_iv in H1. cbn [fst snd] in H1.
      destruct H1 as [[H1 H3]|[E0|(q & Aq & n & Hq & H1 & H3)]]; [cbn; lia| pose proof (XPF _ E0) as [X1 X2]; cbn [fst snd] in X1, X2; cbn; lia|].
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
  Proof.
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
  Proof.
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
    (forall a, rin_ivs XX a -> (bv_unsigned sp + OFS <= a < bv_unsigned sp) \/ rin_ivs XP a \/ (exists q Aq n, In (q, Aq, n) NEW /\ Aq <= a < Aq + n)) ->
    ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX ->
    blocks_kept K stY OWY mX mY ->
    oinv sY stY mY OWY errvY boY (NEW2 ++ NEW).
  Proof.
    intros until NEW2. intros OI PREY LXY HXX SO' FA' (BK1 & BK2 & BK3). pose proof SPR as SPR. pose proof DLEN as DLEN.
    assert (XPF : forall iv, In iv XP -> bv_unsigned sp <= fst iv /\ snd iv <= B) by (intros iv Hiv; exact (proj1 (Forall_forall _ _) XPok iv Hiv)).
    assert (XPA : forall a, rin_ivs XP a -> bv_unsigned sp <= a) by (intros a Ha; apply rin_ivs_In in Ha; destruct Ha as (iv & Hiv & Ha); pose proof (XPF iv Hiv); lia).
    pose proof (oinv_facts _ _ _ _ _ _ _ OI) as (HEAP3 & ND3 & BND & FRESH & DJL & DJO).
    destruct OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    pose proof (agree_of_lx_pres _ _ _ _ _ LXY) as AG.
    assert (CL : forall a, in_block LB a -> ~ rin_ivs LIBW_AP a -> lx_client (NEW ++ LB) (bv_unsigned sp + OFS) (XX ++ LIBW_AP) a).
    { intros a (b & Hb & Hr) HX. destruct b as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in Hr.
      pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hb)) as (B1 & B2 & B3 & B4 & B5).
      split.
      - intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| exact (HX HIN)].
        destruct (HXX a HIN) as [Hs|[Hs|(q & Aq & n & Hq & Ha)]]; [lia| pose proof (XPA a Hs); lia|]. pose proof (DJL q Aq n pb PA psz Hq Hb). lia.
      - right. left. exists (pb, PA, psz). split; [apply in_app_iff; right; exact Hb| cbn; lia]. }
    split; [rewrite <- app_assoc; eapply ap_pre_restack; [exact PREY| rewrite ESP; lia]|].
    split. { eapply lx_pres_trans; [exact LX|]. intros a Ha [HXa Hc]. apply (LXY a Ha).
             assert (HXl : ~ rin_ivs LIBW_AP a) by (intros X; apply HXa; apply rin_ivs_app; right; exact X).
             destruct Hc as [Hc|[Hblk|Hc]].
             - split; [| left; lia]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| exact (HXl HIN)].
               destruct (HXX a HIN) as [Hs|[Hs|(q & Aq & n & Hq & Hq2)]]; [lia| apply HXa; apply rin_ivs_app; left; exact Hs|].
               pose proof (BND q Aq n ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hq)). lia.
             - apply CL; [exact Hblk| exact HXl].
             - split; [| right; right; exact Hc]. intros HIN. apply rin_ivs_app in HIN. destruct HIN as [HIN|HIN]; [| exact (HXl HIN)].
               destruct (HXX a HIN) as [Hs|[Hs|(q & Aq & n & Hq & Hq2)]]; [unfold GLOBALS_TOP in *; lia| pose proof (XPA a Hs); unfold GLOBALS_TOP in *; lia|].
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
  Proof.
    intros until stk0. intros PREX ST4. pose proof SPR as SPR. pose proof DLEN as DLEN.
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16').
    unfold ap_pre. repeat (split; [first [assumption|lia]|]). exact SP16.
  Qed.

  (* [comment removed for export] *)
  Definition ap_call_post {A} (ra : word) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (RES : A * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) (r : A * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinv s' (snd r) mY OWY errvY boY NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) LIBW_AP mX mY
      /\ RES r OWY mY a0 boY.

  Lemma oinv_ap_call : forall {A} (entry stack : Z) ARGS (cst : ap_st bptr -> aprog bptr (A * ap_st bptr)) RES
      (ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW,
    ap_stmt entry stack ARGS cst RES ->
    oinv sX stX mX OWX errvX boX NEW -> stack <= STK -> frm0 fcX -> ARGS stX OWX mX a0 a1 a2 a3 a4 a5 boX ->
    implM ctusegs (interp (ap_embed (cst stX))) sX (ap_call_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW RES)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FX (wz entry) fcX None mX (seg_rom ctusegs)).
  Proof.
    intros until NEW. intros W OI LE FRMX HA. pose proof ESP as ESP.
    pose proof OI as (PREX & LX & KO & KI & KP & SO & FA & HB).
    eapply implM_mono.
    { unfold ap_stmt in W. eapply W; [eapply ap_pre_stack_le; [exact PREX| exact LE]| reflexivity| exact FRMX| exact HA| exact KO| exact KI]. }
    intros r s' ms' PO. cbv beta in PO.
    destruct PO as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F' & fc' & mY & OWY & errvY & boY
                     & -> & FRM' & FE' & PREY & LXY & SOY & FAY & BKY & RESY).
    rewrite ESP in LXY.
    unfold ap_call_post. exists q0, q1, q2, p0, p1, p2, p3, p4, p5, p6, p7, q3, q4, q5, q6, F', fc', mY, OWY, errvY, boY.
    split; [reflexivity|]. split; [exact FRM'|]. split; [exact FE'|].
    split; [| split; [exact LXY| exact RESY]].
    eapply (oinv_after _ _ _ _ _ _ NEW s' (snd r) mY OWY errvY boY [] []); [exact OI| exact PREY| exact LXY| intros a []| exact SOY| exact FAY| exact BKY].
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_payload : forall sX stX mX OWX errvX boX NEW,
    oinv sX stX mX OWX errvX boX NEW -> 0 < D -> D + zlength c < 2 ^ 63 -> zlength c < 2 ^ 30 ->
    payload_ok mX (NEW ++ LB) D c.
  Proof.
    intros until NEW. intros OI D1 D63 D30. destruct OI as (_ & _ & _ & _ & _ & _ & _ & HB).
    split; [exact HB|]. split; [exact DF|]. split; [exact D1|]. split; [exact D63|]. split; [exact D30|].
    destruct PBX as [E0|(pb & PA & psz & H1 & H2 & H3)]; [left; exact E0| right].
    exists (pb, PA, psz). split; [apply in_app_iff; right; exact H1|]. cbn [blk_addr blk_size fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma oinv_heap : forall sX stX mX OWX errvX boX NEW sY mY (errvY : word) L1 LY NEW',
    oinv sX stX mX OWX errvX boX NEW ->
    rheap_pres L1 (bv_unsigned sp + OFS) mX mY -> (forall b, In b OWX \/ In b LB -> In b L1) ->
    RHEAP sY LY mY -> Permutation LY (OWX ++ NEW' ++ LB) ->
    mem_inv ctusegs mY -> stk ctusegs mY lo (bv_unsigned sp + OFS) -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B ->
    ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    oinv sY stX mY OWX errvY boX NEW'.
  Proof.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma oinv_reframe : forall (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block)
    (c : list Z) (D : Z) (XP : list (Z * Z)) (OFS STK OFS' STK' : Z) sX stX mX OWX errvX boX NEW,
  oinv sp m s LB E lo B canary K c D XP OFS STK sX stX mX OWX errvX boX NEW ->
  bv_unsigned sp <= B -> bv_unsigned sp mod 16 = 0 ->
  stk ctusegs mX lo (bv_unsigned sp + OFS') -> lo <= bv_unsigned sp + OFS' - STK' -> OFS' <= 0 -> 0 <= STK' -> OFS' mod 16 = 0 ->
  oinv sp m s LB E lo B canary K c D XP OFS' STK' sX stX mX OWX errvX boX NEW.
Proof.
  intros until NEW. intros (PREX & REST) SPB SP16 ST' LO' OFS0' STK0' OFS16'. split; [| exact REST].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO0 & ERR0 & SSP & MI0 & SP16').
  assert (E1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS')) = bv_unsigned sp + OFS').
  { apply unsigned_lit. unfold GLOBALS_TOP in GLO'. lia. }
  unfold ap_pre. rewrite E1. repeat (split; [first [assumption| lia]|]).
  rewrite Z.add_mod, SP16, OFS16' by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma oinv_xp : forall (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block)
    (c : list Z) (D : Z) (XP XP' : list (Z * Z)) (OFS STK : Z) sX stX mX OWX errvX boX NEW,
  oinv sp m s LB E lo B canary K c D XP OFS STK sX stX mX OWX errvX boX NEW ->
  (forall iv, In iv XP -> In iv XP') ->
  oinv sp m s LB E lo B canary K c D XP' OFS STK sX stX mX OWX errvX boX NEW.
Proof.
  intros until NEW. intros (PREX & LX & REST) INCL. split; [exact PREX|]. split; [| exact REST].
  intros a Ha [HX Hc]. apply (LX a Ha). split; [| exact Hc]. intros HIN. apply HX.
  apply rin_ivs_app in HIN. apply rin_ivs_app. destruct HIN as [HIN|HIN]; [left| right; exact HIN].
  apply rin_ivs_In in HIN. apply rin_ivs_In. destruct HIN as (iv & H1 & H2). exists iv. split; [apply INCL; exact H1| exact H2].
Qed.

End WithCeiling0.
