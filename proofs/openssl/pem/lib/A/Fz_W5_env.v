(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_agree D_clx PLayout Fz_kit Fz_ckit Fz_M_malloc Fz_env Th_mutex Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_rep Fz_W5_agr Fz_W2_exdc Fz_W2_bnew.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition libenv (m : mem) (LBL : list (Z * Z)) (E : Z) : Prop :=
  exists (od e : word) (k MK SA NODES LV : Z) (pad tw ne : word) (kd LK : Z),
       LBL = [(MK, 72); (SA, 32); (NODES, 128); (LK, 40)]
    /\ err_env m od e k MK SA NODES E LV pad tw ne /\ MK mod 8 = 0 /\ SA mod 8 = 0 /\ NODES mod 8 = 0 /\ E mod 8 = 0
    /\ exd_stat m kd LK /\ rw_cells asegs m LK (mutex_cells z64 z64)
    /\ 0xbc57d0 <= LK /\ (LK + 40 <= MK \/ MK + 72 <= LK) /\ (LK + 40 <= SA \/ SA + 32 <= LK) /\ (LK + 40 <= NODES \/ NODES + 128 <= LK).

(* [comment removed for export] *)
Definition libenv_stat (a : Z) : Prop :=
  (0xb9f200 <= a < 0xb9f2e8) \/ (0xb9f500 <= a < 0xb9f528) \/ (0xb9f560 <= a < 0xb9f7a8) \/ (ERRNO_A <= a < ERRNO_A + 4) \/ (0xbc52a0 <= a < 0xbc5698).
Definition libenv_fp (LBL : list (Z * Z)) (a : Z) : Prop := libenv_stat a \/ in_live LBL a.

Lemma libenv_stat_where : forall a, libenv_stat a -> in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a.
Proof.
  intros a Ha. unfold libenv_stat, ERRNO_A in Ha. split; [| split].
  - unfold LIB_W. destruct Ha as [H|[H|[H|[H|H]]]].
    + exists 0xb9f200, 0xb9f848. split; [cbn; tauto | lia].
    + exists 0xb9f200, 0xb9f848. split; [cbn; tauto | lia].
    + exists 0xb9f200, 0xb9f848. split; [cbn; tauto | lia].
    + exists 0xba3e4c, 0xba3e50. split; [cbn; tauto | lia].
    + exists 0xbc52a0, 0xbc5698. split; [cbn; tauto | lia].
  - apply client_static_intro. lia.
  - intros (lo & hi & Hin & Hx). unfold CL_CELLS, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC, G_ALLOW_CUST, ssp_guard in Hin.
    cbn [In] in Hin. repeat (destruct Hin as [EQ|Hin]; [injection EQ as <- <-; lia|]). destruct Hin.
Qed.

Lemma libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Proof. intros LBL a [H|H]; [left; exact (libenv_stat_where a H) | right; exact H]. Qed.

Lemma libenv_LBL : forall m LBL E, libenv m LBL E -> exists MK SA NODES LK, LBL = [(MK, 72); (SA, 32); (NODES, 128); (LK, 40)].
Proof. intros m LBL E (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & _). exists MK, SA, NODES, LK. exact EL. Qed.

(* [comment removed for export] *)
Lemma libenv_agree : forall (m m' : mem) LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Proof.
  intros m m' LBL E (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & (IC & ER & CH) & AL1 & AL2 & AL3 & AL4 & XS & LKC & APT) AG.
  exists od, e, k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. split; [exact EL|].
  assert (LIVE : forall p n a n', In (p, n) LBL -> p <= a -> a + n' <= p + n -> agree_on (fun x => a <= x < a + n') m m').
  { intros p n a n' Hin H1 H2 x Hx. cbv beta in Hx. apply AG. right. exists p, n. split; [exact Hin | lia]. }
  rewrite EL in LIVE. pose proof CH as (_ & _ & HK & _). pose proof XS as (_ & _ & KD & _).
  split; [split; [| split]|].
  - apply (icstat_agree_nw m m' od IC). intros a n H1 H2 x Hx. cbv beta in Hx. apply AG. left. unfold libenv_stat. lia.
  - apply (rw_cells_agree_nw asegs m m' _ _ ER). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AG. left. unfold libenv_stat. lia.
  - apply (errchain_agree_nw m m' _ _ _ _ _ _ _ _ _ CH). intros a n H. unfold TSD_MAIN_A in H.
    destruct H as [H|[H|[H|[H|H]]]].
    + intros x Hx. cbv beta in Hx. apply AG. left. unfold libenv_stat. lia.
    + intros x Hx. cbv beta in Hx. apply AG. left. unfold libenv_stat. lia.
    + apply (LIVE MK 72); [cbn; tauto | lia | lia].
    + apply (LIVE SA 32); [cbn; tauto | lia | lia].
    + apply (LIVE NODES 128); [cbn; tauto | lia | lia].
  - split; [exact AL1|]. split; [exact AL2|]. split; [exact AL3|]. split; [exact AL4|].
    split; [apply (exd_stat_agree m m' kd LK XS); intros x Hx; apply AG; left; unfold exd_fp in Hx; unfold libenv_stat; lia|].
    split; [| exact APT].
    apply (rw_cells_agree_nw asegs m m' _ _ LKC). apply (LIVE LK 40); [cbn; tauto | lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma libenv_exd : exd_iface libenv libenv_fp.
Proof.
  intros m LBL E LE. pose proof LE as (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & ENV & AL1 & AL2 & AL3 & AL4 & XS & LKC & APT).
  exists kd, LK. split; [exact XS|]. split; [rewrite EL; cbn; tauto|]. split; [exact LKC|].
  intros m' AG LKC'. exists od, e, k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. split; [exact EL|].
  pose proof ENV as (IC & ER & CH). pose proof CH as (_ & _ & HK & _). pose proof XS as (_ & _ & KD & _). destruct APT as (LKHI & AP1 & AP2 & AP3).
  assert (AGS : forall x : word, libenv_stat (bv_unsigned x) -> m' x = m x).
  { intros x Hx. apply AG; [left; exact Hx|]. unfold libenv_stat, ERRNO_A in Hx. lia. }
  assert (LIVE : forall p n a n', In (p, n) LBL -> (p + n <= LK \/ LK + 40 <= p) -> p <= a -> a + n' <= p + n -> agree_on (fun x => a <= x < a + n') m m').
  { intros p n a n' Hin Hap H1 H2 x Hx. cbv beta in Hx. apply AG; [right; exists p, n; split; [exact Hin | lia] | lia]. }
  rewrite EL in LIVE.
  split; [split; [| split]|].
  - apply (icstat_agree_nw m m' od IC). intros a n H1 H2 x Hx. cbv beta in Hx. apply AGS. unfold libenv_stat. lia.
  - apply (rw_cells_agree_nw asegs m m' _ _ ER). intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGS. unfold libenv_stat. lia.
  - apply (errchain_agree_nw m m' _ _ _ _ _ _ _ _ _ CH). intros a n H. unfold TSD_MAIN_A in H.
    destruct H as [H|[H|[H|[H|H]]]].
    + intros x Hx. cbv beta in Hx. apply AGS. unfold libenv_stat. lia.
    + intros x Hx. cbv beta in Hx. apply AGS. unfold libenv_stat. lia.
    + apply (LIVE MK 72); [cbn; tauto | lia | lia | lia].
    + apply (LIVE SA 32); [cbn; tauto | lia | lia | lia].
    + apply (LIVE NODES 128); [cbn; tauto | lia | lia | lia].
  - split; [exact AL1|]. split; [exact AL2|]. split; [exact AL3|]. split; [exact AL4|].
    split; [apply (exd_stat_agree m m' kd LK XS); intros x Hx; apply AGS; unfold exd_fp in Hx; unfold libenv_stat; lia|].
    split; [exact LKC'|]. exact (conj LKHI (conj AP1 (conj AP2 AP3))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition errst_live (E top bot : Z) (strs : list (Z * Z)) (m : mem) : Prop :=
  exists (bot' : Z) (fl mk buf fs ls fn : list word) (ks : list (Z * bool)), es_rep m E top bot' fl mk buf fs ls fn /\ slots_ok fs fn ks strs /\ 0 <= bot < 16.
Definition errst_at_rest (E : Z) (strs : list (Z * Z)) (m : mem) : Prop := strs = [] /\ es_at_rest m E.
Definition errst_fp (E : Z) (strs : list (Z * Z)) (a : Z) : Prop := (E <= a < E + 904) \/ in_live strs a.

Lemma errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Proof. intros E strs a H. exact H. Qed.
Lemma errst_rest_agree : forall (m m' : mem) E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Proof.
  intros m m' E strs [-> (fl & mk & buf & ls & ES)] AG. split; [reflexivity|]. exists fl, mk, buf, ls.
  apply (es_rep_agree_nw m m' _ _ _ _ _ _ _ _ _ ES). intros x Hx. apply AG. left. exact Hx.
Qed.
Lemma errst_live_agree : forall (m m' : mem) E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Proof.
  intros m m' E top bot strs (bot' & fl & mk & buf & fs & ls & fn & ks & ES & SL & HB) AG. exists bot', fl, mk, buf, fs, ls, fn, ks.
  split; [| exact (conj SL HB)]. apply (es_rep_agree_nw m m' _ _ _ _ _ _ _ _ _ ES). intros x Hx. apply AG. left. exact Hx.
Qed.
Lemma slots_ok_rest : slots_ok (repeat (Z_to_bv 64 0) 16) (repeat (Z_to_bv 64 0) 16) [] [].
Proof.
  split; [constructor|]. split; [reflexivity|]. split; [intros ik []|]. split; [intros j ik pn H; destruct j; discriminate|].
  intros ik w Hi Hw _. unfold slot_word in Hw. destruct (snd ik); apply List.nth_error_In in Hw; apply repeat_spec in Hw; exact Hw.
Qed.
Lemma errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.
Proof.
  intros m E [_ (fl & mk & buf & ls & ES)]. exists 0, fl, mk, buf, (repeat (Z_to_bv 64 0) 16), ls, (repeat (Z_to_bv 64 0) 16), [].
  split; [exact ES|]. split; [exact slots_ok_rest| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition libenv_core (m : mem) (LBL : list (Z * Z)) (E : Z) : Prop :=
  exists (od : word) (k MK SA NODES LV : Z) (pad tw ne : word) (kd LK : Z),
       LBL = [(MK, 72); (SA, 32); (NODES, 128); (LK, 40)]
    /\ icstat m od /\ errchain m k MK SA NODES E LV pad tw ne /\ MK mod 8 = 0 /\ SA mod 8 = 0 /\ NODES mod 8 = 0 /\ E mod 8 = 0
    /\ exd_stat m kd LK /\ rw_cells asegs m LK (mutex_cells z64 z64)
    /\ 0xbc57d0 <= LK /\ (LK + 40 <= MK \/ MK + 72 <= LK) /\ (LK + 40 <= SA \/ SA + 32 <= LK) /\ (LK + 40 <= NODES \/ NODES + 128 <= LK).
Definition libenv_cstat (a : Z) : Prop :=
  (0xb9f200 <= a < 0xb9f2e8) \/ (0xb9f500 <= a < 0xb9f528) \/ (0xb9f560 <= a < 0xb9f7a8) \/ (0xbc52a0 <= a < 0xbc5698).
Definition libenv_core_fp (LBL : list (Z * Z)) (a : Z) : Prop := libenv_cstat a \/ in_live LBL a.

Lemma libenv_core_of : forall m LBL E, libenv m LBL E -> libenv_core m LBL E.
Proof.
  intros m LBL E (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & (IC & ER & CH) & REST).
  exists od, k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. exact (conj EL (conj IC (conj CH REST))).
Qed.
Lemma libenv_of_core : forall m LBL E (e : word), libenv_core m LBL E -> rw_cells asegs m ERRNO_A [C4 e] -> libenv m LBL E.
Proof.
  intros m LBL E e (od & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & IC & CH & REST) ER.
  exists od, e, k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. exact (conj EL (conj (conj IC (conj ER CH)) REST)).
Qed.
Lemma libenv_core_errno : forall m LBL E, libenv m LBL E -> exists e : word, rw_cells asegs m ERRNO_A [C4 e].
Proof. intros m LBL E (od & e & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & (IC & ER & CH) & REST). exists e. exact ER. Qed.
Lemma libenv_cstat_LIB_D : forall a, libenv_cstat a -> (0xb9f200 <= a < 0xb9f848) \/ (0xbc52a0 <= a < 0xbc5698).
Proof. intros a H. unfold libenv_cstat in H. lia. Qed.
Lemma libenv_core_agree : forall (m m' : mem) LBL E, libenv_core m LBL E -> agree_on (libenv_core_fp LBL) m m' -> libenv_core m' LBL E.
Proof.
  intros m m' LBL E (od & k & MK & SA & NODES & LV & pad & tw & ne & kd & LK & EL & IC & CH & AL1 & AL2 & AL3 & AL4 & XS & LKC & APT) AG.
  exists od, k, MK, SA, NODES, LV, pad, tw, ne, kd, LK. split; [exact EL|].
  assert (LIVE : forall p n a n', In (p, n) LBL -> p <= a -> a + n' <= p + n -> agree_on (fun x => a <= x < a + n') m m').
  { intros p n a n' Hin H1 H2 x Hx. cbv beta in Hx. apply AG. right. exists p, n. split; [exact Hin | lia]. }
  rewrite EL in LIVE. pose proof CH as (_ & _ & HK & _). pose proof XS as (_ & _ & KD & _).
  split; [apply (icstat_agree_nw m m' od IC); intros a n H1 H2 x Hx; cbv beta in Hx; apply AG; left; unfold libenv_cstat; lia|].
  split.
  { apply (errchain_agree_nw m m' _ _ _ _ _ _ _ _ _ CH). intros a n H. unfold TSD_MAIN_A in H.
    destruct H as [H|[H|[H|[H|H]]]].
    + intros x Hx. cbv beta in Hx. apply AG. left. unfold libenv_cstat. lia.
    + intros x Hx. cbv beta in Hx. apply AG. left. unfold libenv_cstat. lia.
    + apply (LIVE MK 72); [cbn; tauto | lia | lia].
    + apply (LIVE SA 32); [cbn; tauto | lia | lia].
    + apply (LIVE NODES 128); [cbn; tauto | lia | lia]. }
  split; [exact AL1|]. split; [exact AL2|]. split; [exact AL3|]. split; [exact AL4|].
  split; [apply (exd_stat_agree m m' kd LK XS); intros x Hx; apply AG; left; unfold exd_fp in Hx; unfold libenv_cstat; lia|].
  split; [| exact APT].
  apply (rw_cells_agree_nw asegs m m' _ _ LKC). apply (LIVE LK 40); [cbn; tauto | lia | cbn; lia].
Qed.
