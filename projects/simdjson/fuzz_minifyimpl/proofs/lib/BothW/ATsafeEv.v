(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotal AsanFree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Ev.
Variables (SB PA : Z).    (* [comment removed for export] *)

Definition inAP (a n : Z) : Prop :=
  (SB <= a /\ a + n <= SB + K_SPACE_SIZE) \/ (PA <= a /\ a + n <= PA + K_PTRARR_RESERVE).

(* [comment removed for export] *)
Definition covG (G : list (Z * Z)) (a n : Z) : Prop :=
  exists g, In g G /\ 0 <= fst g /\ shad (fst g) <= a /\ a + n <= shad (fst g + snd g).

Lemma covG_mono : forall G G' a n, covG G a n -> incl G G' -> covG G' a n.
Proof. intros G G' a n (g & Hin & H) HI. exists g. split; [apply HI; exact Hin| exact H]. Qed.

Fixpoint evq {R} (RP : list (Z * Z) -> Z -> R -> Prop) (ga : list Z) (G : list (Z * Z)) (b : Z) (t : AM R) {struct t} : Prop :=
  match t with
  | SRet r => RP G b r        (* [comment removed for export] *)
  | SVis e k =>
    match e with
    | AUndef _ => True
    | AMmap a len prot flags =>
        prot = PROT_RW /\ 0 < len /\ len mod 4096 = 0 /\
        ((flags = F_ANON /\ a = 0 /\
            match ga with
            | l0 :: ga' => len = l0 /\ len <= b /\ forall z, evq RP ga' ((z, len) :: G) (if is_err z then b else b - len) (k z)
            | [] => False
            end)
         \/ (flags = F_FIXED /\ inAP a len /\ K_PTRARR_COMMIT <= len /\ len <= b /\ forall z, evq RP ga G (if is_err z then b else b - len) (k z))   (* [comment removed for export] *)
         \/ (flags = F_FIXNORES /\ covG G a len /\ forall z, evq RP ga G b (k z)))
    | AMunmap a len => forall z, evq RP ga G b (k z)
    | AMadvise a len => forall z, evq RP ga G b (k z)        (* [comment removed for export] *)
    | _ => False
    end
  end.

(* [comment removed for export] *)
Lemma evq_mono : forall {R} (RP RP' : list (Z * Z) -> Z -> R -> Prop) (t : AM R) ga G G' b b',
  evq RP ga G b t -> incl G G' -> b <= b' ->
  (forall G1 G1' b1 b1' r, incl G1 G1' -> b1 <= b1' -> RP G1 b1 r -> RP' G1' b1' r) ->
  evq RP' ga G' b' t.
Proof.
  intros R RP RP' t. induction t as [r|e k IH]; intros ga G G' b b' H HI Hb HRP; cbn in H |- *.
  - eapply HRP; [exact HI| exact Hb| exact H].
  - destruct e as [t0|b0|a len prot flags|a len|a l p|a len|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & H)|[(Hf & Hin & Hmin & Hlb & H)|(Hf & Hc & H)]].
      * left. split; [exact Hf|]. split; [exact Ha|]. destruct ga as [|l0 ga']; [exact H|].
        destruct H as (El & Hlb & H). split; [exact El|]. split; [lia|]. intros z. eapply IH; [exact (H z)| | destruct (is_err z); lia| exact HRP].
        intros g [<-|Hg]; [left; reflexivity| right; apply HI; exact Hg].
      * right; left. split; [exact Hf|]. split; [exact Hin|]. split; [exact Hmin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| exact HI| destruct (is_err z); lia| exact HRP].
      * right; right. split; [exact Hf|]. split; [eapply covG_mono; eauto|]. intros z. eapply IH; [exact (H z)| exact HI| lia| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact HI| exact Hb| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact HI| exact Hb| exact HRP].
Qed.

Definition bmono {R} (RP : list (Z * Z) -> Z -> R -> Prop) : Prop := forall G b b' r, b <= b' -> RP G b r -> RP G b' r.
Lemma evq_mono_b : forall {R} (RP : list (Z * Z) -> Z -> R -> Prop) (t : AM R) ga G b b',
  bmono RP -> evq RP ga G b t -> b <= b' -> evq RP ga G b' t.
Proof.
  intros R RP t. induction t as [r|e k IH]; intros ga G b b' HM H Hb; cbn in H |- *.
  - eapply HM; [exact Hb| exact H].
  - destruct e as [t0|b0|a len prot flags|a len|a l p|a len|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & H)|[(Hf & Hin & Hmin & Hlb & H)|(Hf & Hc & H)]].
      * left. split; [exact Hf|]. split; [exact Ha|]. destruct ga as [|l0 ga']; [exact H|].
        destruct H as (El & Hlb & H). split; [exact El|]. split; [lia|]. intros z. eapply IH; [exact HM| exact (H z)| destruct (is_err z); lia].
      * right; left. split; [exact Hf|]. split; [exact Hin|]. split; [exact Hmin|]. split; [lia|]. intros z. eapply IH; [exact HM| exact (H z)| destruct (is_err z); lia].
      * right; right. split; [exact Hf|]. split; [exact Hc|]. intros z. eapply IH; [exact HM| exact (H z)| lia].
    + intros z. eapply IH; [exact HM| exact (H z)| exact Hb].
    + intros z. eapply IH; [exact HM| exact (H z)| exact Hb].
Qed.

Lemma evq_aundef : forall {R} RP ga G b w (k : AM R), evq RP ga G b (aundef_ w k).
Proof. intros. cbn. exact I. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chunk_ok (G : list (Z * Z)) (ch : achunk) : Prop :=
  match ch with
  | CPrim c _ => 1 <= c <= 31
  | CSec mb ms n => In (mb, ms) G /\ 0 < mb /\ 0 <= n /\ PG + rz_size n + n <= ms
  end.

Lemma chunk_ok_mono : forall G G' ch, chunk_ok G ch -> incl G G' -> chunk_ok G' ch.
Proof. intros G G' [c n|mb ms n] H HI; cbn in *; [exact H|]. destruct H as (H1 & H2). split; [apply HI; exact H1| exact H2]. Qed.

Lemma Forall_chunk_ok_mono : forall G G' l, Forall (chunk_ok G) l -> incl G G' -> Forall (chunk_ok G') l.
Proof. intros G G' l H HI. eapply Forall_impl; [|exact H]. intros ch Hc. eapply chunk_ok_mono; eauto. Qed.

(* [comment removed for export] *)
Definition stk (r : aclass) : Z := c_count r + c_num_freed r.
Definition HH (c : Z) (r : aclass) : Z := c_allocated_user r - size_of_class c * stk r.
Definition SLK (c : Z) : Z := 8 + 589823 / size_of_class c.

Definition gsum (f : Z -> Z) : Z := fold_right (fun c acc => f c + acc) 0 CLASSES.

Variable m : Z -> Z.
Hypothesis Hm : forall c, 1 <= c <= 31 -> 0 <= m c.

Definition MS : Z := gsum (fun c => m c + SLK c).
Definition UCAP (c : Z) : Z := size_of_class c * (m c + SLK c) + 2 * K_USER_MAP.
Definition FCNT (c : Z) : Z := m c + SLK c + MS + 2.
Definition FCAP (c : Z) : Z := 4 * FCNT c + 2 * K_FREEARR_MAP.
Definition CBM : Z := gsum (fun c => UCAP c + FCAP c) + K_PTRARR_RESERVE.

(* [comment removed for export] *)
Definition is_primb (ch : achunk) : bool := match ch with CPrim _ _ => true | CSec _ _ _ => false end.
Definition nprim (l : list achunk) : Z := zlen (List.filter is_primb l).
Fixpoint nprimq (bs : list abatch) : Z := match bs with [] => 0 | b :: bs' => nprim (b_chunks b) + 1 + nprimq bs' end.
Definition QT (st : astate) : Z := nprimq (a_qloc st ++ a_qglob st).

Lemma size_of_class_pos : forall c, 1 <= c <= 31 -> 32 <= size_of_class c <= 65536.
Proof.
  intros c Hc. assert (H : forall k, In k (map Z.of_nat (seq 1 31)) -> 32 <= size_of_class k <= 65536).
  { intros k Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [vm_compute; split; discriminate|]). destruct Hk. }
  apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma SLK_nonneg : forall c, 1 <= c <= 31 -> 8 <= SLK c.
Proof. intros c Hc. unfold SLK. pose proof (size_of_class_pos c Hc). pose proof (Z.div_pos 589823 (size_of_class c) ltac:(lia) ltac:(lia)). lia. Qed.
Lemma SLK_mul : forall c, 1 <= c <= 31 -> 8 * size_of_class c + 589824 <= size_of_class c * (1 + SLK c).
Proof.
  intros c Hc. unfold SLK. pose proof (size_of_class_pos c Hc) as [S1 S2].
  pose proof (Z.div_mod 589823 (size_of_class c) ltac:(lia)). pose proof (Z.mod_pos_bound 589823 (size_of_class c) ltac:(lia)). nia.
Qed.
(* [comment removed for export] *)
Lemma max_half_bytes : forall c, 1 <= c <= 31 -> 1 <= max_cached c / 2 <= 8 /\ (max_cached c / 2) * size_of_class c <= 65536.
Proof.
  intros c Hc. assert (H : forall k, In k (map Z.of_nat (seq 1 31)) -> 1 <= max_cached k / 2 <= 8 /\ (max_cached k / 2) * size_of_class k <= 65536).
  { intros k Hk. cbn in Hk. repeat (destruct Hk as [<-|Hk]; [vm_compute; repeat split; discriminate|]). destruct Hk. }
  apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma gsum_ge : forall (f : Z -> Z) c, 1 <= c <= 31 -> (forall c', 1 <= c' <= 31 -> 0 <= f c') -> f c <= gsum f.
Proof.
  intros f c Hc Hf. unfold gsum.
  assert (G : forall l, (forall x, In x l -> 1 <= x <= 31) -> (In c l -> f c <= fold_right (fun c0 acc => f c0 + acc) 0 l) /\ 0 <= fold_right (fun c0 acc => f c0 + acc) 0 l).
  { induction l as [|x l IH]; intros Hl; cbn; [split; [intros []| lia]|].
    destruct (IH ltac:(intros y Hy; apply Hl; right; exact Hy)) as [IH1 IH2]. pose proof (Hf x (Hl x (or_introl eq_refl))).
    split; [| lia]. intros [->|Hin]; [lia|]. specialize (IH1 Hin). lia. }
  apply (proj1 (G CLASSES ltac:(intros x Hx; apply In_CLASSES; exact Hx))). apply In_CLASSES. exact Hc.
Qed.
Lemma gsum_nonneg : forall (f : Z -> Z), (forall c', 1 <= c' <= 31 -> 0 <= f c') -> 0 <= gsum f.
Proof. intros f Hf. pose proof (gsum_ge f 1 ltac:(lia) Hf). pose proof (Hf 1 ltac:(lia)). lia. Qed.
Lemma MS_ge : forall c, 1 <= c <= 31 -> m c + SLK c <= MS.
Proof. intros c Hc. unfold MS. apply (gsum_ge (fun c => m c + SLK c) c Hc). intros c' Hc'. pose proof (Hm c' Hc'). pose proof (SLK_nonneg c' Hc'). lia. Qed.
Lemma MS_nonneg : 0 <= MS.
Proof. pose proof (MS_ge 1 ltac:(lia)). pose proof (Hm 1 ltac:(lia)). pose proof (SLK_nonneg 1 ltac:(lia)). lia. Qed.
Lemma UCAP_nonneg : forall c, 1 <= c <= 31 -> 0 <= UCAP c.
Proof. intros c Hc. unfold UCAP, K_USER_MAP. pose proof (Hm c Hc). pose proof (SLK_nonneg c Hc). pose proof (size_of_class_pos c Hc). nia. Qed.
Lemma FCAP_nonneg : forall c, 1 <= c <= 31 -> 0 <= FCAP c.
Proof. intros c Hc. unfold FCAP, FCNT, K_FREEARR_MAP. pose proof (Hm c Hc). pose proof (SLK_nonneg c Hc). pose proof MS_nonneg. lia. Qed.

(* [comment removed for export] *)
Lemma csum_le_gsum : forall (f : aclass -> Z) (g : Z -> Z) st,
  (forall c, 1 <= c <= 31 -> f (get_cls st c) <= g c) -> csum f st <= gsum g.
Proof.
  intros f g st Hfg. unfold csum, gsum.
  assert (G : forall l, (forall x, In x l -> 1 <= x <= 31) -> fold_right (fun c acc => f (get_cls st c) + acc) 0 l <= fold_right (fun c acc => g c + acc) 0 l).
  { induction l as [|x l IH]; intros Hl; cbn; [lia|]. pose proof (Hfg x (Hl x (or_introl eq_refl))). specialize (IH ltac:(intros y Hy; apply Hl; right; exact Hy)). lia. }
  apply G. intros x Hx. apply In_CLASSES. exact Hx.
Qed.

Definition cls_lw (c : Z) (r : aclass) : Prop :=
  0 <= c_mapped_user r <= K_FREEARR_OFF /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ c_mapped_user r <= UCAP c /\ c_mapped_free_array r <= FCAP c       (* [comment removed for export] *)
  /\ 0 <= c_allocated_user r /\ c_mapped_user r <= c_allocated_user r + 2 * K_USER_MAP    (* [comment removed for export] *)
  /\ 0 <= c_count r /\ 0 <= c_num_freed r.                                                       (* [comment removed for export] *)
Definition LW (st : astate) : Prop :=
  a_space_beg st = SB /\ a_ptr_array st = PA /\ 0 <= a_nres st /\ 8 * a_nres st <= K_PTRARR_RESERVE
  /\ forall c, 1 <= c <= 31 -> cls_lw c (get_cls st c).

(* [comment removed for export] *)
Definition PHI (st : astate) : Z := CBM - commit_bytes st.

Lemma commit_bytes_LW : forall st, LW st -> 0 <= commit_bytes st <= CBM.
Proof.
  intros st (_ & _ & N0 & N1 & HC). unfold commit_bytes, CBM.
  pose proof (csum_le_gsum cls_mapped_bytes' (fun c => UCAP c + FCAP c) st ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?&?&?&?&?&?&?); unfold cls_mapped_bytes'; lia)).
  pose proof (csum_nonneg cls_mapped_bytes' st ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?&?&?&?&?&?&?); unfold cls_mapped_bytes'; lia)).
  lia.
Qed.
Lemma PHI_nonneg : forall st, LW st -> 0 <= PHI st.
Proof. intros st H. pose proof (commit_bytes_LW st H). unfold PHI. lia. Qed.

(* [comment removed for export] *)
Lemma LW_put : forall st c r, LW st -> 1 <= c <= 31 -> cls_lw c r -> LW (put_cls c r st).
Proof.
  intros st c r (S1 & S2 & N0 & N1 & HC) Hc Hr. unfold LW. cbn [a_space_beg a_ptr_array a_nres put_cls set_cls].
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
  intros c' Hc'. destruct (Z.eq_dec c c') as [<-|NE].
  - rewrite get_put_eq. exact Hr.
  - rewrite get_put_ne by exact NE. apply HC. exact Hc'.
Qed.
Lemma LW_cls : forall st c, LW st -> 1 <= c <= 31 -> cls_lw c (get_cls st c).
Proof. intros st c (_ & _ & _ & _ & HC) Hc. apply HC. exact Hc. Qed.
Lemma LW_init_cache : forall st, LW st -> LW (init_cache st).
Proof. intros st H. unfold init_cache. destruct (a_cinit st); [exact H|]. exact H. Qed.
Lemma LW_set_nsec : forall v st, LW st -> LW (set_nsec v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_live : forall v st, LW st -> LW (set_live v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_next : forall v st, LW st -> LW (set_next v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_qloc : forall l b st, LW st -> LW (set_qloc l b st). Proof. intros l b st H. exact H. Qed.
Lemma LW_set_qglob : forall l b st, LW st -> LW (set_qglob l b st). Proof. intros l b st H. exact H. Qed.

Lemma PHI_put : forall st c r, 1 <= c <= 31 ->
  PHI (put_cls c r st) = PHI st + cls_mapped_bytes' (get_cls st c) - cls_mapped_bytes' r.
Proof. intros. unfold PHI. rewrite commit_bytes_put by assumption. lia. Qed.
Lemma PHI_init_cache : forall st, PHI (init_cache st) = PHI st.
Proof. intros. unfold PHI. rewrite commit_bytes_init_cache. reflexivity. Qed.
Lemma PHI_set_nsec : forall v st, PHI (set_nsec v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_live : forall v st, PHI (set_live v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_next : forall v st, PHI (set_next v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_qloc : forall l b st, PHI (set_qloc l b st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_qglob : forall l b st, PHI (set_qglob l b st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_nres : forall v st, PHI (set_nres v st) = PHI st - 8 * (v - a_nres st).
Proof. intros. unfold PHI, commit_bytes. cbn [a_nres set_nres]. unfold csum. rewrite (fold_csum_ext cls_mapped_bytes' st (set_nres v st)) by (intros; reflexivity). lia. Qed.


(* [comment removed for export] *)
Lemma all_chunks_same_but : forall c st st', same_but c st st' -> all_chunks [] [] st' = all_chunks [] [] st.
Proof.
  intros c st st' (_&_&_&_&_&HL&_&HQ1&_&HQ2&_&_). unfold all_chunks, live_chunks, qbatches. rewrite HL, HQ1, HQ2. reflexivity.
Qed.
Lemma QT_same_but : forall c st st', same_but c st st' -> QT st' = QT st.
Proof. intros c st st' (_&_&_&_&_&HL&_&HQ1&_&HQ2&_&_). unfold QT. rewrite HQ1, HQ2. reflexivity. Qed.
Lemma LW_same_but : forall c st st', same_but c st st' -> LW st -> cls_lw c (get_cls st' c) -> LW st'.
Proof.
  intros c st st' (E1&E2&E3&_&_&_&_&_&_&_&_&HG) (S1 & S2 & N0 & N1 & HC) Hc'. unfold LW. rewrite E1, E2, E3.
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
  intros c' Hr. destruct (Z.eq_dec c' c) as [->|NE]; [exact Hc'|]. rewrite HG by exact NE. apply HC. exact Hr.
Qed.

(* [comment removed for export] *)
Definition crel_n (st st' : astate) : Prop := forall c, get_cls st' c = get_cls st c.
Definition crel_d (c : Z) (st st' : astate) : Prop :=
  (forall c', c' <> c -> get_cls st' c' = get_cls st c')
  /\ c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c)
  /\ c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c)
  /\ stk (get_cls st' c) = stk (get_cls st c) + 1.
(* [comment removed for export] *)
Definition cgrow (d : Z) (st st' : astate) : Prop :=
  forall c, 1 <= c <= 31 ->
    c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c)
    /\ stk (get_cls st c) <= stk (get_cls st' c) <= stk (get_cls st c) + d.
Lemma cgrow_refl : forall st, cgrow 0 st st. Proof. intros st c Hc. lia. Qed.
Lemma cgrow_n : forall d st st', crel_n st st' -> 0 <= d -> cgrow d st st'.
Proof. intros d st st' H Hd c Hc. rewrite (H c). lia. Qed.
Lemma cgrow_d : forall c st st', 1 <= c <= 31 -> crel_d c st st' -> cgrow 1 st st'.
Proof.
  intros c st st' Hc (E & A & _ & S) c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [lia|]. rewrite (E c' NE). lia.
Qed.
Lemma cgrow_trans : forall d1 d2 st1 st2 st3, cgrow d1 st1 st2 -> cgrow d2 st2 st3 -> 0 <= d1 -> 0 <= d2 -> cgrow (d1 + d2) st1 st3.
Proof. intros d1 d2 st1 st2 st3 H1 H2 Hd1 Hd2 c Hc. destruct (H1 c Hc) as [A1 B1]. destruct (H2 c Hc) as [A2 B2]. split; lia. Qed.
Lemma cgrow_mono : forall d d' st st', cgrow d st st' -> d <= d' -> cgrow d' st st'.
Proof. intros d d' st st' H Hd c Hc. destruct (H c Hc) as [A B]. split; lia. Qed.
Lemma cgrow_HH : forall d st st' c, cgrow d st st' -> 1 <= c <= 31 -> HH c (get_cls st' c) <= HH c (get_cls st c).
Proof. intros d st st' c H Hc. destruct (H c Hc) as [A B]. unfold HH. pose proof (size_of_class_pos c Hc). nia. Qed.
Lemma crel_n_init_cache : forall st, crel_n st (init_cache st).
Proof. intros st c. apply get_cls_init_cache. Qed.
Lemma crel_n_refl : forall st, crel_n st st. Proof. intros st c. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_sub_mult : forall x y m0, 0 < m0 -> x mod m0 = 0 -> y mod m0 = 0 -> (x - y) mod m0 = 0.
Proof.
  intros x y m0 Hm0 Hx Hy. rewrite Zminus_mod, Hx, Hy. reflexivity.
Qed.

Lemma evq_poison0 : forall {R} RP ga G b (k : AM R) addr size g,
  In g G -> 0 <= fst g -> fst g <= addr -> 0 <= size -> addr + size <= fst g + snd g ->
  evq RP ga G b k -> evq RP ga G b (poison0 addr size k).
Proof. (* [comment removed for export] *) intros R RP ga G b k addr size g _ _ _ _ _ Hk. exact Hk. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma region_in_arena : forall st c x y, LW st -> 1 <= c <= 31 -> 0 <= x -> 0 <= y -> x + y <= K_REGION ->
  inAP (region_beg st c + x) y.
Proof.
  intros st c x y (S1 & _) Hc Hx Hy Hxy. left. unfold region_beg. rewrite S1. unfold K_REGION, K_SPACE_SIZE in *. nia.
Qed.

(* [comment removed for export] *)
Lemma evq_ensure_free_array : forall {R} RP ga G st c nf (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  rup (nf * 4) K_FREEARR_MAP <= FCAP c ->
  (forall st' ok, LW st' -> same_but c st st' -> PHI st' <= PHI st ->
     c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) -> c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
     c_count (get_cls st' c) = c_count (get_cls st c) -> c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
     (ok = true -> nf * 4 <= c_mapped_free_array (get_cls st' c)) ->
     evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (ensure_free_array st c nf k).
Proof.
  intros R RP ga G st c nf k extra HL Hc Hex Hcap Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2 & U3 & F3 & U4 & U5 & C8 & C9).
  unfold ensure_free_array.
  destruct (nf * 4 <=? _) eqn:E1. { apply Z.leb_le in E1. apply (Hk st true HL (same_but_refl c st)); auto; lia. }
  destruct (K_FREEARR_MAX <? _) eqn:E2. { apply evq_aundef. }
  apply Z.leb_gt in E1. apply Z.ltb_ge in E2. assert (Hnf : 0 <= nf) by lia.
  pose proof (rup_freearr_bounds (nf * 4) ltac:(lia)) as RB.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RM.
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RG.
  set (nm := rup (nf * 4) K_FREEARR_MAP) in *.
  assert (D : (4096 | K_FREEARR_MAP)) by (exists 64; reflexivity).
  cbn -[evq Z.sub Z.add Z.mul rup region_beg K_FREEARR_OFF nm get_cls put_cls cls_set_mapped_free_array fixed_answer_ok is_err PHI].
  split; [reflexivity|]. split; [lia|]. split.
  { assert (M1 : nm mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod nm K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact RM]).
    assert (M2 : c_mapped_free_array (get_cls st c) mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod _ K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact F2]).
    apply mod_sub_mult; [lia| exact M1| exact M2]. }
  right; left. split; [reflexivity|]. split.
  { replace (region_beg st c + K_FREEARR_OFF + c_mapped_free_array (get_cls st c)) with (region_beg st c + (K_FREEARR_OFF + c_mapped_free_array (get_cls st c))) by lia.
    apply (region_in_arena st c); auto; unfold K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; lia. }
  split. { (* [comment removed for export] *) unfold K_PTRARR_COMMIT, K_FREEARR_MAP in *. clear -E1 RG RM F2 F1. Z.div_mod_to_equations. nia. }
  set (r' := cls_set_mapped_free_array nm (get_cls st c)).
  assert (Hr' : cls_lw c r') by (unfold r', cls_lw; cbn; repeat split; try lia; assumption).
  assert (HL' : LW (put_cls c r' st)) by (apply LW_put; auto).
  assert (EP : PHI (put_cls c r' st) = PHI st - (nm - c_mapped_free_array (get_cls st c)))
    by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
  pose proof (PHI_nonneg _ HL') as P0.
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL (same_but_refl c st)); auto; [lia| intros X; discriminate X].
  - replace (PHI st + extra - (nm - c_mapped_free_array (get_cls st c))) with (PHI (put_cls c r' st) + extra) by lia.
    apply Hk; [exact HL'| apply same_but_put| lia| | | | |]; rewrite ?get_put_eq; unfold r'; cbn; try reflexivity. intros _. lia.
Qed.

(* [comment removed for export] *)
Lemma evq_populate : forall {R} RP ga G st c req (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra -> 0 < req -> req * size_of_class c <= 65536 ->
  0 <= c_num_freed (get_cls st c) <= 8 ->
  c_allocated_user (get_cls st c) + req * size_of_class c <= size_of_class c * (m c + 7) ->
  (forall st' ok, LW st' -> same_but c st st' -> PHI st' <= PHI st ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     (   (* [comment removed for export] *)
         (c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) /\ c_num_freed (get_cls st' c) = c_num_freed (get_cls st c))
      \/ (* [comment removed for export] *)
         (exists q, 0 < q /\ req <= q /\ q * size_of_class c <= req * size_of_class c + 2 * K_USER_MAP /\ ok = true
                    /\ c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) + q * size_of_class c
                    /\ c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) + q)) ->
     evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (populate_free_array st c req k).
Proof.
  intros R RP ga G st c req k extra HL Hc Hex Hreq Hrs Hnf8 HAU7 Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2 & U3 & F3 & HAU0 & U5 & C8 & C9).
  pose proof (size_of_class_pos c Hc) as [SZ1 SZ2]. pose proof (Hm c Hc) as Hm0. pose proof (SLK_nonneg c Hc) as SL0. pose proof MS_nonneg as MS0.
  remember (size_of_class c) as size eqn:Hsize.
  unfold populate_free_array. rewrite <- Hsize. cbv zeta.
  (* [comment removed for export] *)
  assert (AFTER : forall st1, LW st1 -> same_but c st st1 -> PHI st1 <= PHI st ->
    c_count (get_cls st1 c) = c_count (get_cls st c) -> c_num_freed (get_cls st1 c) = c_num_freed (get_cls st c) ->
    c_allocated_user (get_cls st1 c) = c_allocated_user (get_cls st c) ->
    c_allocated_user (get_cls st c) + req * size <= c_mapped_user (get_cls st1 c) ->
    c_mapped_user (get_cls st1 c) <= c_allocated_user (get_cls st c) + req * size + 2 * K_USER_MAP ->
    evq RP ga G (PHI st1 + extra)
      (ensure_free_array st1 c (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size)
         (fun st2 ok => if negb ok then k st2 false else
            k (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size * size)
                            (cls_set_num_freed (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size) (get_cls st2 c))) st2) true))).
  { intros st1 HL1 HS1 HP1 Hcnt1 Hnf1 Hau1 Hen1 Hub1.
    pose proof (carve_facts (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) size ltac:(lia) ltac:(lia)) as (Q0 & Qcv & Qrest).
    pose proof (carve_enough_nomap (c_mapped_user (get_cls st1 c)) (c_allocated_user (get_cls st1 c)) size req ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
    set (q := (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size) in *.
    assert (Hq : req <= q /\ q * size <= req * size + 2 * K_USER_MAP) by (split; [lia| unfold K_USER_MAP in *; lia]).
    assert (HqB : 4 * (c_num_freed (get_cls st1 c) + q) <= 4 * (m c + 7) + 4 * 16384 + 32).
    { assert (size * q <= size * (m c + 7) + 524288) by (unfold K_USER_MAP in *; lia).
      assert (32 * q <= size * q) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (q <= m c + 7 + 16384); [| lia].
      destruct (Z_le_dec q (m c + 7 + 16384)) as [|NE]; [assumption| exfalso].
      assert (size * (m c + 7 + 16384 + 1) <= size * q) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
    apply evq_ensure_free_array; auto.
    { pose proof (rup_le ((c_num_freed (get_cls st1 c) + q) * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)).
      unfold FCAP, FCNT, K_FREEARR_MAP in *. lia. }
    intros st2 ok HL2 HS2 HP2 E1 E2 E3 E4 E5. destruct ok; cbn [negb].
    - set (r3 := cls_set_allocated_user _ (cls_set_num_freed _ (get_cls st2 c))).
      assert (Hr3 : cls_lw c r3).
      { pose proof (LW_cls st2 c HL2 Hc) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10). unfold r3, cls_lw in *; cbn. rewrite E1, E2 in *.
        repeat split; try assumption; unfold K_USER_MAP in *; try lia. }
      replace (PHI st2 + extra) with (PHI (put_cls c r3 st2) + extra) by (rewrite PHI_put by exact Hc; unfold r3, cls_mapped_bytes'; cbn; lia).
      apply Hk; [apply LW_put; auto| eapply same_but_trans; [eapply same_but_trans; [exact HS1| exact HS2]| apply same_but_put]| | |].
      + rewrite PHI_put by exact Hc. unfold r3, cls_mapped_bytes'; cbn. lia.
      + rewrite get_put_eq. unfold r3. cbn. congruence.
      + right. exists q. rewrite get_put_eq. unfold r3. cbn. rewrite ?E2, ?Hau1, ?E4, ?Hnf1. split; [lia|]. repeat split; try lia; reflexivity.
    - apply Hk; [exact HL2| eapply same_but_trans; [exact HS1| exact HS2]| lia| congruence| left; split; congruence]. }
  destruct (_ <=? c_mapped_user (get_cls st c)) eqn:E1.
  { apply Z.leb_le in E1. apply AFTER; [exact HL| apply same_but_refl| lia| reflexivity| reflexivity| reflexivity| exact E1| lia]. }
  apply Z.leb_gt in E1.
  set (ums := rup _ K_USER_MAP).
  destruct (K_FREEARR_OFF <? _) eqn:E2. { apply evq_aundef. }
  apply Z.ltb_ge in E2.
  pose proof (rup_ge (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RG. fold ums in RG.
  pose proof (rup_le (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RL. fold ums in RL.
  pose proof (rup_mod (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RM. fold ums in RM.
  assert (D : (4096 | K_USER_MAP)) by (exists 64; reflexivity).
  set (r' := cls_set_mapped_user (c_mapped_user (get_cls st c) + ums) (get_cls st c)).
  assert (Hr' : cls_lw c r').
  { unfold r', cls_lw; cbn. split; [lia|]. split; [| split; [exact F1| split; [exact F2| split; [| split; [exact F3| unfold K_USER_MAP in *; lia]]]]].
    - rewrite Z.add_mod, U2, RM by (unfold K_USER_MAP; lia). reflexivity.
    - (* [comment removed for export] *) unfold UCAP, SLK, K_USER_MAP in *. rewrite <- Hsize in *.
      assert (0 <= size * (589823 / size)) by (apply Z.mul_nonneg_nonneg; [lia| apply Z.div_pos; lia]). lia. }
  assert (HL' : LW (put_cls c r' st)) by (apply LW_put; auto).
  assert (EP : PHI (put_cls c r' st) = PHI st - ums) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
  pose proof (PHI_nonneg _ HL') as P0.
  cbn -[evq Z.sub Z.add Z.mul Z.div rup region_beg K_FREEARR_OFF ums get_cls put_cls cls_set_mapped_user cls_set_allocated_user cls_set_num_freed
        fixed_answer_ok is_err PHI ensure_free_array size_of_class].
  split; [reflexivity|]. split; [lia|]. split.
  { apply Znumtheory.Zdivide_mod. apply (div4096_of_mod ums K_USER_MAP); [exact D| unfold K_USER_MAP; lia| exact RM]. }
  right; left. split; [reflexivity|]. split.
  { apply (region_in_arena st c); auto; try lia. unfold K_FREEARR_OFF, K_REGION in *. lia. }
  split. { (* [comment removed for export] *) unfold K_PTRARR_COMMIT, K_USER_MAP in *. clear -E1 RG RM. Z.div_mod_to_equations. nia. }
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL (same_but_refl c st)); [lia| reflexivity| left; split; reflexivity].
  - replace (PHI st + extra - ums) with (PHI (put_cls c r' st) + extra) by lia.
    apply AFTER; [exact HL'| apply same_but_put| lia| | | | |]; rewrite ?get_put_eq; unfold r'; cbn; try reflexivity; unfold K_USER_MAP in *; lia.
Qed.

(* [comment removed for export] *)
Definition frq (st st' : astate) : Prop :=
  a_live st' = a_live st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st /\ a_next st' = a_next st.
Lemma frq_refl : forall st, frq st st. Proof. intros. unfold frq. auto. Qed.
Lemma frq_trans : forall a b c, frq a b -> frq b c -> frq a c.
Proof. intros a b c (A1&A2&A3&A4) (B1&B2&B3&B4). unfold frq. rewrite B1, B2, B3, B4. auto. Qed.
Lemma frq_same_but : forall c st st', same_but c st st' -> frq st st'.
Proof. intros c st st' (_&_&_&_&_&HL&HN&HQ1&_&HQ2&_&_). unfold frq. auto. Qed.
Lemma frq_init_cache : forall st, frq st (init_cache st).
Proof. intros. unfold init_cache. destruct (a_cinit st); [apply frq_refl|]. unfold frq. auto. Qed.
Lemma frq_put : forall st c r, frq st (put_cls c r st). Proof. intros. unfold frq. auto. Qed.
Lemma all_chunks_frq : forall st st', frq st st' -> all_chunks [] [] st' = all_chunks [] [] st.
Proof. intros st st' (A&B&C&_). unfold all_chunks, live_chunks, qbatches. rewrite A, B, C. reflexivity. Qed.
Lemma QT_frq : forall st st', frq st st' -> QT st' = QT st.
Proof. intros st st' (_&B&C&_). unfold QT. rewrite B, C. reflexivity. Qed.
Lemma same_but_other : forall c st st' c', same_but c st st' -> c' <> c -> get_cls st' c' = get_cls st c'.
Proof. intros c st st' c' (_&_&_&_&_&_&_&_&_&_&_&HG) NE. apply HG. exact NE. Qed.

(* [comment removed for export] *)
Definition crel_a (c : Z) (st st' : astate) : Prop :=
  (forall c', c' <> c -> get_cls st' c' = get_cls st c')
  /\ HH c (get_cls st' c) <= HH c (get_cls st c) + size_of_class c
  /\ c_allocated_user (get_cls st c) <= c_allocated_user (get_cls st' c)
  /\ (c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c)
      \/ c_allocated_user (get_cls st' c) <= HH c (get_cls st c) + size_of_class c * (1 + SLK c))
  /\ stk (get_cls st' c) <= Z.max (stk (get_cls st c)) (SLK c).

Lemma evq_cache_alloc : forall {R} RP ga G st c (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  HH c (get_cls st c) + size_of_class c <= size_of_class c * m c ->      (* [comment removed for export] *)
  (forall st' ok, LW st' -> frq st st' -> PHI st' <= PHI st -> crel_a c st st' -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (cache_alloc st c k).
Proof.
  intros R RP ga G st c k extra HL Hc Hex HHm Hk. unfold cache_alloc. cbv zeta.
  pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2 & U3 & F3 & A0 & U5 & C8 & C9).
  pose proof (size_of_class_pos c Hc) as [SZ1 SZ2]. pose proof (SLK_nonneg c Hc) as SL0. pose proof (SLK_mul c Hc) as SLM.
  pose proof (max_half_bytes c Hc) as [MH1 MH2].
  assert (HST : size_of_class c * stk (get_cls st c) <= c_allocated_user (get_cls st c) -> True) by (intros; exact I). clear HST.
  destruct (0 <? _) eqn:E0.
  { apply Z.ltb_lt in E0. set (r' := cls_set_count _ _). assert (Hr' : cls_lw c r') by (unfold r', cls_lw; cbn; repeat split; try assumption; lia).
    replace (PHI st + extra) with (PHI (put_cls c r' st) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| apply frq_put| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia|].
    unfold crel_a. rewrite get_put_eq. unfold r', HH, stk; cbn. split; [intros c' NE; apply get_put_ne; congruence|]. split; [lia|]. split; [lia|]. split; [left; reflexivity| lia]. }
  apply Z.ltb_ge in E0. assert (Hcnt0 : c_count (get_cls st c) = 0) by lia.
  pose proof (LW_init_cache st HL) as HL1. rewrite max_count_init_cache.
  set (n0 := max_cached c / 2) in *.
  assert (TAKE : forall st2, LW st2 -> frq st st2 -> PHI st2 <= PHI st ->
    (forall c', c' <> c -> get_cls st2 c' = get_cls st c') -> c_count (get_cls st2 c) = 0 ->
    (   (c_allocated_user (get_cls st2 c) = c_allocated_user (get_cls st c) /\ c_num_freed (get_cls st2 c) = c_num_freed (get_cls st c))
     \/ (exists q, 0 < q /\ c_num_freed (get_cls st c) < n0 /\ n0 - c_num_freed (get_cls st c) <= q /\ q * size_of_class c <= (n0 - c_num_freed (get_cls st c)) * size_of_class c + 2 * K_USER_MAP
                   /\ c_allocated_user (get_cls st2 c) = c_allocated_user (get_cls st c) + q * size_of_class c
                   /\ c_num_freed (get_cls st2 c) = c_num_freed (get_cls st c) + q)) ->
    evq RP ga G (PHI st2 + extra)
      (if c_num_freed (get_cls st2 c) <? n0 then aundef_ (UCheck 229) (k st2 false)
       else k (put_cls c (cls_set_count (n0 - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n0) (get_cls st2 c))) st2) true)).
  { intros st2 HL2 HF2 HP2 HO2 Hc2 HE2. destruct (_ <? _) eqn:EL; [apply evq_aundef|]. apply Z.ltb_ge in EL.
    pose proof (LW_cls st2 c HL2 Hc) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw c r') by (unfold r', cls_lw; cbn; repeat split; try assumption; lia).
    replace (PHI st2 + extra) with (PHI (put_cls c r' st2) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [exact HF2| apply frq_put]| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia|].
    unfold crel_a. rewrite get_put_eq. unfold r', HH, stk; cbn. rewrite Hcnt0.
    split; [intros c' NE; rewrite get_put_ne by congruence; apply HO2; exact NE|].
    destruct HE2 as [[EA EN]|(q & Hq0 & Hnf0 & Hq1 & Hq2 & EA & EN)]; rewrite EA, EN.
    - split; [lia|]. split; [lia|]. split; [left; reflexivity| lia].
    - assert (QS0 : 0 <= q * size_of_class c) by (apply Z.mul_nonneg_nonneg; lia).
      assert (N8 : (n0 - c_num_freed (get_cls st c)) * size_of_class c <= 8 * size_of_class c) by (apply Z.mul_le_mono_nonneg_r; lia).
      unfold K_USER_MAP in Hq2.
      split; [lia|]. split; [lia|]. split.
      + right. lia.
      + (* [comment removed for export] *)
        assert (Hq3 : (q - (n0 - c_num_freed (get_cls st c))) * size_of_class c <= 524288) by lia.
        assert (Hq4 : q - (n0 - c_num_freed (get_cls st c)) <= 524288 / size_of_class c) by (apply Z.div_le_lower_bound; lia).
        assert (SLKc : 524288 / size_of_class c <= 589823 / size_of_class c) by (apply Z.div_le_mono; lia).
        unfold SLK. lia. }
  destruct (_ <=? _) eqn:E1.
  - apply Z.leb_le in E1. rewrite get_cls_init_cache in E1. rewrite <- (PHI_init_cache st). apply TAKE; [exact HL1| apply frq_init_cache| rewrite PHI_init_cache; lia| intros c' NE; apply get_cls_init_cache| rewrite get_cls_init_cache; exact Hcnt0| left; rewrite get_cls_init_cache; split; reflexivity].
  - apply Z.leb_gt in E1. rewrite get_cls_init_cache in E1. rewrite <- (PHI_init_cache st).
    assert (R64 : (n0 - c_num_freed (get_cls st c)) * size_of_class c <= 65536).
    { apply (Z.le_trans _ (n0 * size_of_class c)); [apply Z.mul_le_mono_nonneg_r; lia| exact MH2]. }
    assert (R7 : c_allocated_user (get_cls st c) + (n0 - c_num_freed (get_cls st c)) * size_of_class c <= size_of_class c * (m c + 7)).
    { (* [comment removed for export] *)
      unfold HH, stk in HHm. rewrite Hcnt0 in HHm.
      assert (n0 * size_of_class c <= 8 * size_of_class c) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    apply evq_populate; auto; try (rewrite get_cls_init_cache); try lia.
    intros st2 ok HL2 HS2 HP2 Hc2 HE2. rewrite PHI_init_cache in HP2. rewrite ?get_cls_init_cache in Hc2. rewrite ?get_cls_init_cache in HE2. destruct ok.
      * apply TAKE; [exact HL2| eapply frq_trans; [apply frq_init_cache| eapply frq_same_but; exact HS2]| exact HP2| | lia|].
        { intros c' NE. rewrite (same_but_other c _ _ c' HS2 NE). apply get_cls_init_cache. }
        destruct HE2 as [HE2|(q & Hq0 & Hq1 & Hq2 & _ & EA & EN)]; [left; exact HE2| right; exists q; repeat split; auto; lia].
      * apply Hk; [exact HL2| eapply frq_trans; [apply frq_init_cache| eapply frq_same_but; exact HS2]| exact HP2|].
        destruct HE2 as [[EA EN]|(q & _ & _ & _ & Habs & _)]; [| discriminate Habs].
        unfold crel_a, HH, stk. rewrite EA, EN, Hc2.
        split; [intros c' NE; rewrite (same_but_other c _ _ c' HS2 NE); apply get_cls_init_cache|]. split; [lia|]. split; [lia|]. split; [left; reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma evq_cache_dealloc : forall {R} RP ga G st c (k : astate -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  stk (get_cls st c) + 1 <= FCNT c ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> crel_d c st st' -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (cache_dealloc st c k).
Proof.
  intros R RP ga G st c k extra HL Hc Hex Hroom Hk. unfold cache_dealloc. cbv zeta.
  pose proof (LW_init_cache st HL) as HL1. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2 & U3 & F3 & A0 & U5 & C8 & C9).
  pose proof (max_half_bytes c Hc) as [MH1 MH2].
  destruct (_ =? _) eqn:EQ.
  - apply Z.eqb_eq in EQ. rewrite get_cls_init_cache, max_count_init_cache in EQ.
    rewrite <- (PHI_init_cache st). apply evq_ensure_free_array; auto.
    { rewrite get_cls_init_cache, max_count_init_cache. unfold stk in Hroom.
      pose proof (rup_le ((c_num_freed (get_cls st c) + max_cached c / 2) * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)).
      assert (2 * (max_cached c / 2) <= max_cached c) by (apply Z.mul_div_le; lia).
      unfold FCAP, K_FREEARR_MAP in *. lia. }
    intros st2 ok HL2 HS2 HP2 E1 E2 E3 E4 E5. rewrite PHI_init_cache in HP2. rewrite !get_cls_init_cache, ?max_count_init_cache in *. destruct ok; cbn [negb]; [|apply evq_aundef].
    pose proof (LW_cls st2 c HL2 Hc) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw c r') by (unfold r', cls_lw; cbn; repeat split; try assumption; lia).
    replace (PHI st2 + extra) with (PHI (put_cls c r' st2) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [apply frq_init_cache| eapply frq_trans; [eapply frq_same_but; exact HS2| apply frq_put]]| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia|].
    unfold crel_d, stk. rewrite get_put_eq. unfold r'; cbn. split; [| rewrite E2, E3, E4; repeat split; lia].
    intros c' NE. rewrite get_put_ne by congruence. rewrite (same_but_other c _ _ c' HS2 NE). apply get_cls_init_cache.
  - set (r' := cls_set_count _ _). assert (Hr' : cls_lw c r') by (pose proof (LW_cls (init_cache st) c HL1 Hc) as X; unfold r', cls_lw in *; cbn; rewrite get_cls_init_cache in *; repeat split; try lia; assumption).
    replace (PHI st + extra) with (PHI (put_cls c r' (init_cache st)) + extra) by (rewrite PHI_put by exact Hc; rewrite PHI_init_cache; unfold r', cls_mapped_bytes'; cbn; rewrite get_cls_init_cache; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [apply frq_init_cache| apply frq_put]| |].
    + rewrite PHI_put by exact Hc. rewrite PHI_init_cache. unfold r', cls_mapped_bytes'; cbn. rewrite get_cls_init_cache. lia.
    + unfold crel_d, stk. rewrite get_put_eq. unfold r'; cbn. rewrite get_cls_init_cache. split; [| repeat split; lia].
      intros c' NE. rewrite get_put_ne by congruence. apply get_cls_init_cache.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_lnot7 : forall n, 0 <= n -> 0 <= Z.land n (Z.lnot 7) <= n.
Proof.
  intros n Hn. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia.
Qed.
Lemma rz_size_large : forall n, 64512 < n -> rz_size n = 2048.
Proof. intros. unfold rz_size, rz_log. repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity. Qed.
Lemma sec_map_size_mod : forall n, sec_map_size n mod 4096 = 0.
Proof. intros. unfold sec_map_size. rewrite Z.add_mod, rup_mod by (unfold PG; lia). reflexivity. Qed.

Lemma evq_large_alloc : forall {R} RESV RP G st n (k : astate -> option achunk -> AM R),
  bmono RP -> LW st -> 64512 < n <= 2^40 ->
  (forall G' st' och, incl G G' -> LW st' -> frq st st' -> PHI st' <= PHI st -> crel_n st st' ->
     (forall ch, och = Some ch -> chunk_ok G' ch /\ ch = CSec (match ch with CSec mb _ _ => mb | _ => 0 end) (sec_map_size n) n) ->
     evq RP [] G' (PHI st' + 0) (k st' och)) ->
  evq RP [sec_map_size n] G (PHI st + sec_map_size n) (large_alloc ATOP RESV st n k).
Proof.
  intros R RESV RP G st n k HBM HL Hn Hk. pose proof HL as (S1 & S2 & N0 & N1 & HC).
  pose proof (sec_map_size_ge n ltac:(lia)) as SG. pose proof (rz_size_large n ltac:(lia)) as RZ.
  pose proof (PHI_nonneg st HL) as P0.
  unfold large_alloc. cbv zeta. cbn [evq ev].
  split; [reflexivity|]. split; [lia|]. split; [apply sec_map_size_mod|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP _ z)) eqn:E0; [apply evq_aundef|].
  destruct (is_err z) eqn:E1.
  { eapply evq_mono_b; [exact HBM| apply (Hk ((z, sec_map_size n) :: G) st None); auto| lia].
    - intros g Hg; right; exact Hg. - apply frq_refl. - lia. - apply crel_n_refl. - intros ch H; discriminate. }
  assert (Hz : 0 < z). { unfold mmap_answer_ok in E0. rewrite E1 in E0. cbn [orb] in E0. apply Bool.negb_false_iff in E0.
                         repeat (apply andb_prop in E0 as [E0 ?]). apply Z.ltb_lt in E0. exact E0. }
  destruct (negb (avoids_all z (sec_map_size n) (RESV ++ asec_ranges st))) eqn:E2; [apply evq_aundef|].
  set (ch := CSec z (sec_map_size n) n).
  assert (CH : forall G', In (z, sec_map_size n) G' -> chunk_ok G' ch /\ ch = CSec z (sec_map_size n) n).
  { intros G' HinG. split; [|reflexivity]. unfold ch, chunk_ok. split; [exact HinG|]. split; [lia|]. split; [lia|]. rewrite RZ. unfold PG. lia. }
  destruct (a_nsec st =? a_nres st).
  - destruct (K_PTRARR_RESERVE <? _) eqn:E3; [apply evq_aundef|]. apply Z.ltb_ge in E3.
    cbn [evq ev].
    split; [reflexivity|]. split; [unfold K_PTRARR_COMMIT; lia|]. split; [reflexivity|].
    right; left. split; [reflexivity|]. split.
    { right. rewrite S2. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *. lia. }
    split; [lia|].   (* [comment removed for export] *)
    assert (EPn : PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) = PHI st - K_PTRARR_COMMIT).
    { rewrite PHI_set_nres. cbn [a_nres set_nsec]. rewrite PHI_set_nsec. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK. lia. }
    assert (HLn : LW (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))).
    { unfold LW. cbn [a_space_beg a_ptr_array a_nres set_nres set_nsec]. split; [exact S1|]. split; [exact S2|].
      split; [unfold K_CHUNKS_BLOCK; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|]. intros c Hc. apply HC. exact Hc. }
    pose proof (PHI_nonneg _ HLn). split; [lia|].
    intros r. destruct (negb (fixed_answer_ok _ r)); [apply evq_aundef|]. destruct (is_err r); [apply evq_aundef|].
    replace (PHI st + sec_map_size n - sec_map_size n - K_PTRARR_COMMIT) with (PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + 0) by lia.
    apply Hk; [intros g Hg; right; exact Hg| exact HLn| unfold frq; auto| rewrite EPn; unfold K_PTRARR_COMMIT; lia| intros c; reflexivity|].
    intros ch0 [= <-]. apply CH. left; reflexivity.
  - replace (PHI st + sec_map_size n - sec_map_size n) with (PHI (set_nsec (a_nsec st + 1) st) + 0) by (rewrite PHI_set_nsec; lia).
    apply Hk; [intros g Hg; right; exact Hg| apply LW_set_nsec; exact HL| unfold frq; auto| rewrite PHI_set_nsec; lia| intros c; reflexivity|].
    intros ch0 [= <-]. apply CH. left; reflexivity.
Qed.

Lemma evq_large_dealloc : forall {R} RP ga G st mb ms n (k : astate -> AM R) extra,
  LW st -> chunk_ok G (CSec mb ms n) ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> crel_n st st' -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (large_dealloc st mb ms k).
Proof.
  intros R RP ga G st mb ms n k extra HL (Hin & Hmb & Hn & Hms) Hk. unfold large_dealloc. cbv zeta.
  pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply (evq_poison0 RP ga G _ _ mb ms (mb, ms)); auto; cbn [fst snd]; try lia. { unfold PG in Hms. lia. }
  (* [comment removed for export] *)
  assert (UN : forall z : Z, evq RP ga G (PHI st + extra)
                 (if z =? 0 then k (set_nsec (a_nsec st - 1) st)
                  else if is_err z then aundef_ USpin (k (set_nsec (a_nsec st - 1) st)) else aundef_ UBadAnswer (k (set_nsec (a_nsec st - 1) st)))).
  { intros z. destruct (z =? 0).
    - replace (PHI st + extra) with (PHI (set_nsec (a_nsec st - 1) st) + extra) by (rewrite PHI_set_nsec; lia).
      apply Hk; [apply LW_set_nsec; exact HL| unfold frq; auto| rewrite PHI_set_nsec; lia| intros c; reflexivity].
    - destruct (is_err z); apply evq_aundef. }
  destruct (_ <? _); cbn; [intros _|]; exact UN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RPst (st0 : astate) (E : astate -> astate -> Prop) (G : list (Z * Z)) (b : Z) (st' : astate) : Prop :=
  LW st' /\ Forall (chunk_ok G) (all_chunks [] [] st') /\ E st0 st' /\ PHI st' <= b.   (* [comment removed for export] *)
Definition RPm (st0 : astate) (E : astate -> astate -> Prop) (G : list (Z * Z)) (b : Z) (r : astate * option AsanCtrl.aptr) : Prop :=
  let (st', _) := r in RPst st0 E G b st'.
Lemma RPst_bmono : forall st0 E, bmono (RPst st0 E).
Proof. intros st0 E G b b' r Hb (A & B & C & D). split; [exact A|]. split; [exact B|]. split; [exact C| lia]. Qed.
Lemma RPm_bmono : forall st0 E, bmono (RPm st0 E).
Proof. intros st0 E G b b' [st' o] Hb H. exact (RPst_bmono st0 E G b b' st' Hb H). Qed.

Lemma all_chunks_live_insert : forall G st id ch,
  (a_live st) !! id = None -> chunk_ok G ch -> Forall (chunk_ok G) (all_chunks [] [] st) ->
  Forall (chunk_ok G) (all_chunks [] [] (set_live (<[id := ch]> (a_live st)) st)).
Proof.
  intros G st id ch Hn Hch HF. unfold all_chunks in *. cbn [app] in *.
  apply Forall_app in HF as [HF1 HF2]. apply Forall_app. split.
  - eapply Permutation_Forall; [apply Permutation_sym; apply live_chunks_insert; exact Hn|]. constructor; assumption.
  - unfold qbatches in *. cbn [app a_qloc a_qglob set_live] in *. exact HF2.
Qed.

(* [comment removed for export] *)
Definition next_fresh (st : astate) : Prop := forall id ch, (a_live st) !! id = Some ch -> (id < a_next st)%N.

(* [comment removed for export] *)
Definition mrel (n : Z) (st st' : astate) : Prop :=
  if is_primary n then crel_a (class_id (needed_size n)) st st' else crel_n st st'.

Lemma crel_a_cls : forall c st st' st'', crel_a c st st' -> (forall c0, get_cls st'' c0 = get_cls st' c0) -> crel_a c st st''.
Proof. intros c st st' st'' (A & B & C & D & E) HE. unfold crel_a. rewrite !HE. repeat split; auto. intros c' NE. rewrite HE. apply A. exact NE. Qed.

Lemma evq_amalloc : forall RESV G st n,
  LW st -> Forall (chunk_ok G) (all_chunks [] [] st) -> next_fresh st -> 0 <= n ->
  (is_primary n = true -> let c := class_id (needed_size n) in HH c (get_cls st c) + size_of_class c <= size_of_class c * m c) ->
  evq (RPm st (mrel n)) (if is_primary n then [] else [sec_map_size n]) G (PHI st + (if is_primary n then 0 else sec_map_size n)) (amalloc ATOP RESV st n).
Proof.
  intros RESV G st n HL HF HNF Hn HPAY. unfold amalloc. cbv zeta.
  destruct (_ || _) eqn:E0.
  { unfold RPm, RPst. split; [exact HL|]. split; [exact HF|]. unfold mrel. destruct (is_primary n) eqn:EP.
    - pose proof (primary_class_facts n Hn EP) as (C1 & _). unfold crel_a. pose proof (size_of_class_pos (class_id (needed_size n)) ltac:(lia)). pose proof (SLK_nonneg (class_id (needed_size n)) ltac:(lia)).
      split; [| lia]. split; [intros; reflexivity|]. split; [lia|]. split; [lia|]. split; [left; reflexivity| lia].
    - split; [apply crel_n_refl|]. apply Bool.orb_true_iff in E0. destruct E0 as [E0|E0]; apply Z.ltb_lt in E0; [pose proof (sec_map_size_ge n ltac:(lia)); lia|].
      (* [comment removed for export] *)
      destruct (Z_lt_le_dec 64512 n) as [Hl|Hs]; [pose proof (sec_map_size_ge n Hl); lia|].
      exfalso. rewrite (proj2 (is_primary_iff n ltac:(lia))) in EP || idtac. pose proof (primary_class_facts n Hn) as PF.
      rewrite is_primary_iff in EP by lia. apply Z.leb_gt in EP. lia. }
  apply Bool.orb_false_iff in E0 as [E0a E0b]. apply Z.ltb_ge in E0a. apply Z.ltb_ge in E0b.
  (* [comment removed for export] *)
  assert (FIN : forall G' st1 ch b, incl G G' -> LW st1 -> frq st st1 -> chunk_ok G' ch -> mrel n st st1 -> PHI st1 <= b ->
            (forall mb ms n0, ch = CSec mb ms n0 -> n0 = n) ->
            evq (RPm st (mrel n)) [] G' b
              (match ch with
               | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))
               | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7)) (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1)))
               end)).
  { intros G' st1 ch b HI HL1 HF1 Hch HM HPB Hchn.
    assert (HNF1 : (a_live st1) !! (a_next st1) = None).
    { destruct HF1 as (EL & _ & _ & EN). destruct ((a_live st1) !! (a_next st1)) as [c0|] eqn:E; [|reflexivity].
      exfalso. rewrite EL, EN in E. pose proof (HNF _ _ E). lia. }
    assert (POST : RPm st (mrel n) G' b (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))).
    { unfold RPm, RPst. split; [apply LW_set_next, LW_set_live; exact HL1|]. split; [| split].
      - unfold all_chunks. cbn [app]. apply all_chunks_live_insert; [exact HNF1| exact Hch|].
        rewrite (all_chunks_frq st st1 HF1). eapply Forall_chunk_ok_mono; eauto.
      - unfold mrel in *. destruct (is_primary n); [eapply crel_a_cls; [exact HM| intros; reflexivity]| intros c0; cbn; apply HM].
      - rewrite PHI_set_next, PHI_set_live. exact HPB. }
    destruct ch as [c0 n0|mb ms n0]; [exact POST|].
    cbn in Hch. destruct Hch as (Hin & Hmb & Hn0 & Hms). specialize (Hchn mb ms n0 eq_refl). subst n0.
    pose proof (land_lnot7 n Hn) as LN. pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
    apply (evq_poison0 _ [] G' b _ _ _ (mb, ms)); auto; cbn [fst snd chunk_user_beg]; unfold PG in *; lia. }
  destruct (is_primary n) eqn:EP.
  - rewrite Z.add_0_r. replace (PHI st) with (PHI st + 0) by lia.
    pose proof (primary_class_facts n Hn EP) as (C1 & _).
    apply evq_cache_alloc; [exact HL| lia| lia| exact (HPAY eq_refl)|]. intros st1 ok HL1 HF1 HP1 HR1. destruct ok.
    + apply (FIN G st1 (CPrim (class_id (needed_size n)) n)); auto. { apply incl_refl. } { cbn. lia. } { unfold mrel. rewrite EP. exact HR1. } { lia. } { intros; discriminate. }
    + unfold RPm, RPst. split; [exact HL1|]. rewrite (all_chunks_frq st st1 HF1). split; [exact HF|]. unfold mrel. rewrite EP. split; [exact HR1| lia].
  - pose proof (not_primary_large n Hn EP) as NL.
    apply evq_large_alloc; [apply RPm_bmono| exact HL| lia|]. intros G' st1 och HI HL1 HF1 HP1 HN1 HCH. destruct och as [ch|].
    + destruct (HCH ch eq_refl) as [Hch Ech]. apply (FIN G' st1 ch); auto. { unfold mrel. rewrite EP. exact HN1. } { lia. } intros mb ms n0 E. rewrite E in Ech. congruence.
    + unfold RPm, RPst. split; [exact HL1|]. rewrite (all_chunks_frq st st1 HF1). split; [eapply Forall_chunk_ok_mono; eauto|]. unfold mrel. rewrite EP. split; [exact HN1| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition QOK (G : list (Z * Z)) (st : astate) : Prop := Forall (chunk_ok G) (all_chunks [] [] st).

Lemma QOK_frq : forall G st st', frq st st' -> QOK G st -> QOK G st'.
Proof. intros G st st' HF H. unfold QOK. rewrite (all_chunks_frq st st' HF). exact H. Qed.
Lemma QOK_mono : forall G G' st, QOK G st -> incl G G' -> QOK G' st.
Proof. intros. eapply Forall_chunk_ok_mono; eauto. Qed.
Lemma QOK_parts : forall G st, QOK G st <-> Forall (chunk_ok G) (live_chunks st) /\ Forall (chunk_ok G) (qchunks (a_qloc st)) /\ Forall (chunk_ok G) (qchunks (a_qglob st)).
Proof.
  intros G st. unfold QOK, all_chunks, qbatches. cbn [app]. rewrite qchunks_app, !Forall_app. tauto.
Qed.

(* [comment removed for export] *)
Lemma nprim_nonneg : forall l, 0 <= nprim l. Proof. intros. unfold nprim. apply zlen_nonneg. Qed.
Lemma nprim_cons : forall ch l, nprim (ch :: l) = (if is_primb ch then 1 else 0) + nprim l.
Proof. intros. unfold nprim. cbn [List.filter]. destruct (is_primb ch); [rewrite zlen_cons|]; lia. Qed.
Lemma nprim_app : forall a b, nprim (a ++ b) = nprim a + nprim b.
Proof. intros. unfold nprim. rewrite filter_app, zlen_app. reflexivity. Qed.
Lemma nprim_rev : forall l, nprim (rev l) = nprim l.
Proof. induction l as [|x l IH]; cbn [rev]; [reflexivity|]. rewrite nprim_app, IH, !nprim_cons. unfold nprim. cbn. rewrite (@zlen_nil achunk). lia. Qed.
Lemma nprimq_nonneg : forall bs, 0 <= nprimq bs.
Proof. induction bs; cbn; [lia|]. pose proof (nprim_nonneg (b_chunks a)). lia. Qed.
Lemma nprimq_app : forall a b, nprimq (a ++ b) = nprimq a + nprimq b.
Proof. induction a; intros; cbn; [lia|]. rewrite IHa. lia. Qed.
Lemma nprim_incl_perm : forall l l', Permutation l l' -> nprim l = nprim l'.
Proof. intros l l' HP. unfold nprim. unfold zlen. rewrite (Permutation_length (filter_perm is_primb _ _ HP)). reflexivity. Qed.

(* [comment removed for export] *)
Definition ROOM (d : Z) (st : astate) : Prop := forall c, 1 <= c <= 31 -> stk (get_cls st c) + d <= FCNT c.
Lemma ROOM_mono : forall d d' st, ROOM d st -> d' <= d -> ROOM d' st.
Proof. intros d d' st H Hd c Hc. pose proof (H c Hc). lia. Qed.
Lemma ROOM_d : forall d c st st', ROOM d st -> 1 <= c <= 31 -> crel_d c st st' -> ROOM (d - 1) st'.
Proof.
  intros d c st st' H Hc (E & _ & _ & S) c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [pose proof (H c Hc); lia|].
  rewrite (E c' NE). pose proof (H c' Hc'). lia.
Qed.
Lemma ROOM_n : forall d st st', ROOM d st -> crel_n st st' -> ROOM d st'.
Proof. intros d st st' H E c Hc. rewrite (E c). apply H. exact Hc. Qed.

Lemma evq_recycle_chunk : forall {R} RP ga G st ch (k : astate -> AM R) extra,
  LW st -> chunk_ok G ch -> 0 <= extra -> ROOM (nprim [ch]) st ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> cgrow (nprim [ch]) st st' -> ROOM 0 st' -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle_chunk st ch k).
Proof.
  intros R RP ga G st ch k extra HL Hch Hex HR Hk. destruct ch as [c n|mb ms n]; cbn [recycle_chunk].
  - cbn in Hch. assert (E1 : nprim [CPrim c n] = 1) by reflexivity. rewrite E1 in HR, Hk. apply evq_cache_dealloc; [exact HL| exact Hch| exact Hex| exact (HR c Hch)|].
    intros st' HL' HF' HP' HD. apply Hk; auto. { eapply cgrow_d; eauto. } { replace 0 with (1 - 1) by lia. eapply ROOM_d; eauto. }
  - assert (E1 : nprim [CSec mb ms n] = 0) by reflexivity. rewrite E1 in HR, Hk. eapply evq_large_dealloc; eauto.
    intros st' HL' HF' HP' HN. apply Hk; auto. { apply cgrow_n; [exact HN| lia]. } { eapply ROOM_n; eauto. }
Qed.

Lemma evq_recycle_chunks : forall {R} RP ga G l st (k : astate -> AM R) extra,
  LW st -> Forall (chunk_ok G) l -> 0 <= extra -> ROOM (nprim l) st ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> cgrow (nprim l) st st' -> ROOM 0 st' -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle_chunks st l k).
Proof.
  intros R RP ga G l. induction l as [|ch l IH]; intros st k extra HL HF Hex HR Hk; cbn [recycle_chunks].
  - apply Hk; [exact HL| apply frq_refl| lia| apply cgrow_refl| exact HR].
  - apply Forall_cons_iff in HF as [Hch HF]. rewrite nprim_cons in HR, Hk.
    pose proof (nprim_nonneg l) as N0.
    assert (E1 : nprim [ch] = if is_primb ch then 1 else 0) by (unfold nprim; cbn; destruct (is_primb ch); reflexivity).
    eapply evq_recycle_chunk; eauto.
    { rewrite E1. eapply ROOM_mono; [exact HR| destruct (is_primb ch); lia]. }
    intros st1 HL1 HF1 HP1 HG1 HR1. apply IH; auto.
    { intros c Hc. destruct (HG1 c Hc) as [_ B]. pose proof (HR c Hc). rewrite E1 in B. lia. }
    intros st2 HL2 HF2 HP2 HG2 HR2. apply Hk; [exact HL2| eapply frq_trans; eauto| lia| | exact HR2].
    rewrite E1 in HG1. eapply cgrow_trans; eauto; destruct (is_primb ch); lia.
Qed.

Lemma batch_K : 1 <= K_BATCH_CLASS <= 31. Proof. unfold K_BATCH_CLASS. lia. Qed.

Lemma evq_do_recycle : forall {R} RP ga G bs st (k : astate -> AM R) extra,
  LW st -> Forall (chunk_ok G) (qchunks bs) -> 0 <= extra -> ROOM (nprimq bs) st ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> cgrow (nprimq bs) st st' -> ROOM 0 st' -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (do_recycle st bs k).
Proof.
  intros R RP ga G bs. induction bs as [|b bs IH]; intros st k extra HL HF Hex HR Hk; cbn [do_recycle].
  - apply Hk; [exact HL| apply frq_refl| lia| apply cgrow_refl| exact HR].
  - rewrite qchunks_cons in HF. apply Forall_app in HF as [Hb HF]. cbn [nprimq] in HR, Hk.
    pose proof (nprim_nonneg (b_chunks b)) as N0. pose proof (nprimq_nonneg bs) as N1.
    apply evq_recycle_chunks; auto. { apply Forall_rev. exact Hb. } { rewrite nprim_rev. eapply ROOM_mono; [exact HR| lia]. }
    intros st1 HL1 HF1 HP1 HG1 HR1. rewrite nprim_rev in HG1.
    apply evq_cache_dealloc; auto; [apply batch_K| |].
    { destruct (HG1 K_BATCH_CLASS batch_K) as [_ B]. pose proof (HR K_BATCH_CLASS batch_K). lia. }
    intros st2 HL2 HF2 HP2 HD2. apply IH; auto.
    { intros c Hc. destruct (HG1 c Hc) as [_ B]. pose proof (HR c Hc). pose proof (cgrow_d _ _ _ batch_K HD2 c Hc) as [_ B2]. lia. }
    intros st3 HL3 HF3 HP3 HG3 HR3.
    apply Hk; [exact HL3| eapply frq_trans; [exact HF1| eapply frq_trans; eauto]| lia| | exact HR3].
    replace (nprim (b_chunks b) + 1 + nprimq bs) with ((nprim (b_chunks b) + 1) + nprimq bs) by lia.
    eapply cgrow_trans; [eapply cgrow_trans; [exact HG1| eapply cgrow_d; [apply batch_K| exact HD2]| lia| lia]| exact HG3| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma in_qchunks_app : forall ch a b, In ch (qchunks (a ++ b)) <-> In ch (qchunks a) \/ In ch (qchunks b).
Proof. intros. rewrite qchunks_app. apply in_app_iff. Qed.
Lemma in_qchunks_cons : forall ch b bs, In ch (qchunks (b :: bs)) <-> In ch (b_chunks b) \/ In ch (qchunks bs).
Proof. intros. rewrite qchunks_cons. apply in_app_iff. Qed.

Lemma merge_batches_incl : forall rest cur,
  let '(l, ex, exb) := merge_batches cur rest in incl (qchunks (l ++ ex)) (qchunks (cur :: rest)).
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn [merge_batches].
  - rewrite app_nil_r. apply incl_refl.
  - destruct (_ <=? _).
    + set (cur' := mkABatch _ _ _). specialize (IH cur'). destruct (merge_batches cur' rest) as [[l ex] exb].
      intros ch Hin. apply in_qchunks_app in Hin as [Hin|Hin].
      * assert (H2 : In ch (qchunks (l ++ ex))) by (apply in_qchunks_app; left; exact Hin). apply IH in H2.
        apply in_qchunks_cons in H2 as [H2|H2].
        -- unfold cur' in H2. cbn [b_chunks] in H2. apply in_app_iff in H2 as [H2|H2].
           ++ apply in_qchunks_cons. right. apply in_qchunks_cons. left. exact H2.
           ++ apply in_qchunks_cons. left. exact H2.
        -- apply in_qchunks_cons. right. apply in_qchunks_cons. right. exact H2.
      * apply in_qchunks_cons in Hin as [Hin|Hin]; [cbn in Hin; destruct Hin|].
        assert (H2 : In ch (qchunks (l ++ ex))) by (apply in_qchunks_app; right; exact Hin). apply IH in H2.
        apply in_qchunks_cons in H2 as [H2|H2].
        -- unfold cur' in H2. cbn [b_chunks] in H2. apply in_app_iff in H2 as [H2|H2].
           ++ apply in_qchunks_cons. right. apply in_qchunks_cons. left. exact H2.
           ++ apply in_qchunks_cons. left. exact H2.
        -- apply in_qchunks_cons. right. apply in_qchunks_cons. right. exact H2.
    + specialize (IH nx). destruct (merge_batches nx rest) as [[l ex] exb].
      intros ch Hin. change ((cur :: l) ++ ex) with (cur :: (l ++ ex)) in Hin. apply in_qchunks_cons in Hin as [H1|H2].
      * apply in_qchunks_cons. left. exact H1.
      * apply in_qchunks_cons. right. apply IH. exact H2.
Qed.

(* [comment removed for export] *)
Lemma merge_batches_count : forall rest cur,
  let '(l, ex, exb) := merge_batches cur rest in nprimq (l ++ ex) = nprimq (cur :: rest).
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn [merge_batches].
  - rewrite app_nil_r. reflexivity.
  - destruct (_ <=? _).
    + set (cur' := mkABatch _ _ _). specialize (IH cur'). destruct (merge_batches cur' rest) as [[l ex] exb].
      rewrite !nprimq_app in *. unfold cur' in IH. cbn [nprimq b_chunks] in *. rewrite nprim_app in IH.
      replace (nprim (@nil achunk)) with 0 by reflexivity. lia.
    + specialize (IH nx). destruct (merge_batches nx rest) as [[l ex] exb].
      change ((cur :: l) ++ ex) with (cur :: (l ++ ex)). cbn [nprimq]. rewrite IH. cbn [nprimq]. lia.
Qed.

Lemma Forall_incl' : forall {A} (P : A -> Prop) l l', Forall P l' -> incl l l' -> Forall P l.
Proof. intros A P l l' H HI. rewrite Forall_forall in *. intros x Hx. apply H, HI, Hx. Qed.

Lemma evq_recycle : forall {R} RP ga G st mn (k : astate -> AM R) extra,
  LW st -> QOK G st -> 0 <= extra -> ROOM (nprimq (a_qglob st)) st ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> cgrow (nprimq (a_qglob st)) st st' -> ROOM 0 st' ->
     a_live st' = a_live st -> a_next st' = a_next st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle st mn k).
Proof.
  intros R RP ga G st mn k extra HL HQ Hex HR Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  pose proof (nprimq_nonneg (a_qglob st)) as N0.
  unfold recycle. cbv zeta.
  destruct (_ <? _); [apply evq_aundef|].
  assert (TAIL : forall gl extracted exb, incl (qchunks (gl ++ extracted)) (qchunks (a_qglob st)) -> nprimq (gl ++ extracted) = nprimq (a_qglob st) ->
    evq RP ga G (PHI st + extra)
      (let '(taken, rest, bytes2) := dequeue_while gl (a_qglob_bytes st - exb) mn in
       if mn <? bytes2 then aundef_ (UCheck 0) (k st) else do_recycle (set_qglob rest bytes2 st) (extracted ++ taken) k)).
  2:{ destruct (_ && _).
      - destruct (a_qglob st) as [|b0 rest0] eqn:EQ.
        + cbv beta iota. apply TAIL; rewrite ?EQ; cbn; [intros x Hx; exact Hx| reflexivity].
        + pose proof (merge_batches_incl rest0 b0) as HM. pose proof (merge_batches_count rest0 b0) as HC. destruct (merge_batches b0 rest0) as [[gl extracted] exb].
          cbv beta iota. apply TAIL; rewrite ?EQ; [exact HM| exact HC].
      - cbv beta iota. apply TAIL; rewrite app_nil_r; [apply incl_refl| reflexivity]. }
  intros gl extracted exb HM HC.
  pose proof (dequeue_while_spec gl (a_qglob_bytes st - exb) mn) as HD.
  destruct (dequeue_while gl (a_qglob_bytes st - exb) mn) as [[taken rest] bytes2]. destruct HD as (HD1 & _ & _).
  destruct (mn <? bytes2); [apply evq_aundef|].
  assert (INC : incl (qchunks (extracted ++ taken) ++ qchunks rest) (qchunks (a_qglob st))).
  { intros ch Hin. apply HM. rewrite <- HD1. rewrite !qchunks_app in *. repeat (apply in_app_iff in Hin as [Hin|Hin]); apply in_app_iff; auto.
    - left. apply in_app_iff. auto. - left. apply in_app_iff. auto. }
  assert (CNT : nprimq (extracted ++ taken) + nprimq rest = nprimq (a_qglob st)).
  { rewrite <- HC, <- HD1. rewrite !nprimq_app. lia. }
  pose proof (nprimq_nonneg rest) as N1. pose proof (nprimq_nonneg (extracted ++ taken)) as N2.
  rewrite <- (PHI_set_qglob rest bytes2 st). apply evq_do_recycle; auto.
  { eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. left. exact Hin. }
  { intros c Hc. pose proof (HR c Hc). replace (get_cls (set_qglob rest bytes2 st) c) with (get_cls st c) by reflexivity. lia. }
  intros st1 HL1 HF1 HP1 HG1 HR1. destruct HF1 as (FL & FQ1 & FQ2 & FN). cbn [a_live a_qloc a_qglob a_next set_qglob] in FL, FQ1, FQ2, FN.
  apply Hk; [exact HL1| | rewrite PHI_set_qglob in HP1; exact HP1| eapply cgrow_mono; [exact HG1| lia]| exact HR1| exact FL| exact FN].
  apply QOK_parts. unfold live_chunks. rewrite FL, FQ1, FQ2.
  split; [exact Q1|]. split; [exact Q2|]. eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. right. exact Hin.
Qed.

Lemma evq_drain : forall {R} RP ga G st (k : astate -> AM R) extra,
  LW st -> QOK G st -> 0 <= extra -> ROOM (QT st) st ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> cgrow (QT st) st st' -> ROOM 0 st' ->
     a_live st' = a_live st -> a_next st' = a_next st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (drain st k).
Proof.
  intros R RP ga G st k extra HL HQ Hex HR Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold drain. cbv zeta. set (st1 := set_qglob _ _ (set_qloc [] 0 st)).
  assert (HQ1 : QOK G st1). { apply QOK_parts. cbn. split; [exact Q1|]. split; [constructor|]. rewrite qchunks_app. apply Forall_app. auto. }
  assert (HL1 : LW st1) by exact HL. assert (EP : PHI st1 = PHI st) by reflexivity.
  assert (EQT : nprimq (a_qglob st1) = QT st) by (unfold QT, st1; cbn; rewrite !nprimq_app; lia).
  pose proof (nprimq_nonneg (a_qloc st ++ a_qglob st)) as N0. unfold QT in *.
  destruct (Q_MAX <? _).
  - rewrite <- EP. apply evq_recycle; [exact HL1| exact HQ1| lia| rewrite EQT; intros c Hc; apply HR; exact Hc|].
    intros st2 HL2 HQ2 HP2 HG2 HR2 FL FN. rewrite EQT in HG2. apply Hk; [exact HL2| exact HQ2| lia| exact HG2| exact HR2| exact FL| exact FN].
  - rewrite <- EP. apply Hk; [exact HL1| exact HQ1| lia| apply cgrow_n; [intros c; reflexivity| exact N0]| | reflexivity| reflexivity].
    intros c Hc. pose proof (HR c Hc). replace (get_cls st1 c) with (get_cls st c) by reflexivity. lia.
Qed.

Lemma qchunks_rev_snoc : forall P rl b,
  Forall P (qchunks (rev (b :: rl))) <-> Forall P (qchunks (rev rl)) /\ Forall P (b_chunks b).
Proof. intros P rl b. cbn [rev]. rewrite qchunks_app, Forall_app, qchunks_cons. cbn. rewrite app_nil_r. tauto. Qed.

Lemma nprimq_rev_perm : forall l, nprimq (rev l) = nprimq l.
Proof. induction l as [|b l IH]; cbn [rev]; [reflexivity|]. rewrite nprimq_app, IH. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma evq_enqueue : forall {R} RP ga G st ch (k : astate -> AM R) extra,
  LW st -> QOK G st -> chunk_ok G ch -> 0 <= extra ->
  HH K_BATCH_CLASS (get_cls st K_BATCH_CLASS) + size_of_class K_BATCH_CLASS <= size_of_class K_BATCH_CLASS * m K_BATCH_CLASS ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> QT st' <= QT st + 2 ->
     a_live st' = a_live st -> a_next st' = a_next st ->
     (crel_a K_BATCH_CLASS st st' \/ crel_n st st') -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (enqueue st ch k).
Proof.
  intros R RP ga G st ch k extra HL HQ Hch Hex HPAY Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  assert (NCH : nprim [ch] <= 1) by (unfold nprim; cbn; destruct (is_primb ch); cbn; rewrite ?zlen_cons, ?(@zlen_nil achunk); lia).
  pose proof (nprim_nonneg [ch]) as NCH0.
  unfold enqueue. cbv zeta.
  assert (NEW : forall st0, LW st0 -> frq st st0 -> PHI st0 <= PHI st -> crel_n st st0 ->
    evq RP ga G (PHI st0 + extra)
      (cache_alloc st0 K_BATCH_CLASS (fun st1 ok => if negb ok then aundef_ USpin (k st1)
         else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1)))).
  { intros st0 HL0 HF0 HP0 HN0. apply evq_cache_alloc; auto; [apply batch_K| rewrite (HN0 K_BATCH_CLASS); exact HPAY|].
    intros st1 ok HL1 HF1 HP1 HA1. destruct ok; cbn [negb]; [|apply evq_aundef].
    rewrite <- (PHI_set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1).
    pose proof (frq_trans _ _ _ HF0 HF1) as (FL & FQ1 & FQ2 & FN).
    apply Hk; [apply LW_set_qloc; exact HL1| | rewrite PHI_set_qloc; lia| | exact FL| exact FN|].
    - pose proof (QOK_frq G st st1 (frq_trans _ _ _ HF0 HF1) HQ) as HQ1. apply QOK_parts in HQ1 as (R1 & R2 & R3).
      apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live]. split; [exact R1|]. split; [| exact R3].
      rewrite qchunks_app, Forall_app. split; [exact R2|]. rewrite qchunks_cons. cbn. constructor; [exact Hch| constructor].
    - unfold QT. cbn [a_qloc a_qglob set_qloc]. rewrite FQ1, FQ2. rewrite <- app_assoc, !nprimq_app. cbn [nprimq b_chunks]. lia.
    - left. apply (crel_a_cls _ _ st1); [| intros c0; reflexivity]. destruct HA1 as (A & B & C & D & E). unfold crel_a. rewrite <- !(HN0 K_BATCH_CLASS).
      split; [intros c' NE; rewrite (A c' NE); apply HN0| auto]. }
  destruct (rev (a_qloc st)) as [|b rl] eqn:ER.
  - apply NEW; [exact HL| apply frq_refl| lia| apply crel_n_refl].
  - destruct (b_count b =? Q_BATCH). { apply NEW; [exact HL| apply frq_refl| lia| apply crel_n_refl]. }
    rewrite <- (PHI_set_qloc (rev (mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b) :: rl)) (a_qloc_bytes st + chunk_size ch) st).

    assert (E : a_qloc st = rev (b :: rl)) by (rewrite <- ER, rev_involutive; reflexivity).
    apply Hk; [apply LW_set_qloc; exact HL| | rewrite PHI_set_qloc; lia| | reflexivity| reflexivity| right; intros c; reflexivity].
    + apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live]. split; [exact Q1|]. split; [| exact Q3].
      rewrite E in Q2. apply qchunks_rev_snoc in Q2 as [Q2a Q2b]. apply qchunks_rev_snoc. split; [exact Q2a|]. cbn. constructor; assumption.
    + unfold QT. cbn [a_qloc a_qglob set_qloc]. rewrite E. rewrite !nprimq_app, !nprimq_rev_perm. cbn [nprimq b_chunks]. rewrite nprim_cons. destruct (is_primb ch); lia.
Qed.

(* [comment removed for export] *)
Definition frel (st st' : astate) : Prop :=
  forall c, 1 <= c <= 31 ->
    HH c (get_cls st' c) <= HH c (get_cls st c) + (if c =? K_BATCH_CLASS then size_of_class c else 0)
    /\ c_allocated_user (get_cls st c) <= c_allocated_user (get_cls st' c)
    /\ (c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c)
        \/ (c = K_BATCH_CLASS /\ c_allocated_user (get_cls st' c) <= HH c (get_cls st c) + size_of_class c * (1 + SLK c))).

Lemma frel_of_parts : forall st st1 st2 d,
  (crel_a K_BATCH_CLASS st st1 \/ crel_n st st1) -> cgrow d st1 st2 -> 0 <= d -> frel st st2.
Proof.
  intros st st1 st2 d H1 H2 Hd c Hc. pose proof (H2 c Hc) as [A2 B2]. pose proof (size_of_class_pos c Hc) as [S1 S2]. pose proof (SLK_nonneg c Hc).
  assert (HH2 : HH c (get_cls st2 c) <= HH c (get_cls st1 c)) by (unfold HH; nia).
  destruct H1 as [(A & B & C & D & E)|N].
  - destruct (Z.eqb_spec c K_BATCH_CLASS) as [->|NE]; cbv iota beta.
    + split; [lia|]. split; [lia|]. destruct D as [D|D]; [left; lia| right; split; [reflexivity| lia]].
    + rewrite A2. rewrite (A c NE) in *. split; [lia|]. split; [lia|]. left; reflexivity.
  - rewrite A2. rewrite (N c) in *. split; [destruct (c =? K_BATCH_CLASS); lia|]. split; [lia|]. left; reflexivity.
Qed.

Lemma frel_cgrow : forall st st2 st3 d, frel st st2 -> cgrow d st2 st3 -> 0 <= d -> frel st st3.
Proof.
  intros st st2 st3 d H1 H2 Hd c Hc. pose proof (H1 c Hc) as (A1 & B1 & C1). pose proof (H2 c Hc) as [A2 B2].
  pose proof (size_of_class_pos c Hc) as [S1 S2].
  assert (HH3 : HH c (get_cls st3 c) <= HH c (get_cls st2 c)) by (unfold HH; nia).
  split; [lia|]. split; [lia|]. destruct C1 as [C1|[C1 C1']]; [left; lia| right; split; [exact C1| lia]].
Qed.
Lemma frel_of_cgrow : forall st st2 d, cgrow d st st2 -> 0 <= d -> frel st st2.
Proof.
  intros st st2 d H Hd c Hc. pose proof (H c Hc) as [A B]. pose proof (size_of_class_pos c Hc) as [S1 S2].
  assert (HH2 : HH c (get_cls st2 c) <= HH c (get_cls st c)) by (unfold HH; nia).
  split; [destruct (c =? K_BATCH_CLASS); lia|]. split; [lia|]. left; lia.
Qed.

Lemma evq_afree : forall G st id,
  LW st -> QOK G st ->
  HH K_BATCH_CLASS (get_cls st K_BATCH_CLASS) + size_of_class K_BATCH_CLASS <= size_of_class K_BATCH_CLASS * m K_BATCH_CLASS ->
  (forall c, 1 <= c <= 31 -> stk (get_cls st c) + QT st + 1 <= MS) ->
  evq (RPst st frel) [] G (PHI st + 0) (afree st (Some id)).
Proof.
  intros G st id HL HQ HPAY HQT. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3). unfold afree.
  destruct ((a_live st) !! id) as [ch|] eqn:Hl; [|apply evq_aundef]. cbv zeta.
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  pose proof (Permutation_Forall HPl Q1) as Q1'. apply Forall_cons_iff in Q1' as [Hch Q1d].
  set (st1 := set_live (delete id (a_live st)) st).
  assert (HQ1 : QOK G st1). { apply QOK_parts. cbn [a_qloc a_qglob st1 set_live]. split; [exact Q1d|]. auto. }
  assert (HL1 : LW st1) by exact HL. assert (EP : PHI st1 = PHI st) by reflexivity. assert (EQ1 : QT st1 = QT st) by reflexivity.
  assert (ECL : forall c, get_cls st1 c = get_cls st c) by (intros; reflexivity).
  pose proof (nprimq_nonneg (a_qloc st ++ a_qglob st)) as N0. change (nprimq (a_qloc st ++ a_qglob st)) with (QT st) in N0.
  (* [comment removed for export] *)
  assert (AFTER : forall st2, LW st2 -> QOK G st2 -> PHI st2 <= PHI st -> QT st2 <= QT st + 2 ->
    frel st st2 -> (forall c, 1 <= c <= 31 -> stk (get_cls st2 c) <= Z.max (stk (get_cls st c)) (SLK c) + 1) ->
    evq (RPst st frel) [] G (PHI st2 + 0) (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)).
  { intros st2 HL2 HQ2 HP2 HQT2 HR2 HS2.
    assert (HROOM : ROOM (QT st2) st2).
    { intros c Hc. pose proof (HQT c Hc) as X. pose proof (HS2 c Hc). pose proof (MS_ge c Hc). pose proof (Hm c Hc). pose proof (SLK_nonneg c Hc).
      pose proof (LW_cls st c HL Hc) as (_&_&_&_&_&_&_&_&C8&C9). unfold FCNT, stk in *. lia. }
    destruct (Q_CACHE <? _).
    - apply evq_drain; [exact HL2| exact HQ2| lia| exact HROOM|]. intros st3 HL3 HQ3 HP3 HG3 HR3 FL FN. cbn. split; [exact HL3|]. split; [exact HQ3|]. split; [| lia].
      eapply frel_cgrow; [exact HR2| exact HG3| pose proof (nprimq_nonneg (a_qloc st2 ++ a_qglob st2)); unfold QT; lia].
    - cbn. split; [exact HL2|]. split; [exact HQ2|]. split; [exact HR2| lia]. }
  rewrite <- EP. destruct (chunk_size ch <=? Q_MAX).
  - apply evq_enqueue; [exact HL1| exact HQ1| exact Hch| lia| exact HPAY|]. intros st2 HL2 HQ2 HP2 HQT2 FL FN HR2. apply AFTER; [exact HL2| exact HQ2| rewrite <- EP; exact HP2| rewrite EQ1 in HQT2; lia| |].
    + eapply frel_of_parts; [exact HR2| apply cgrow_refl| lia].
    + intros c Hc. destruct HR2 as [(A & B & C & D & E)|N].
      * destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE].
        -- change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in E. lia.
        -- rewrite (A c NE). change (get_cls st1 c) with (get_cls st c). lia.
      * rewrite (N c). change (get_cls st1 c) with (get_cls st c). lia.
  - apply (evq_recycle_chunk _ [] G st1 ch); [exact HL1| exact Hch| lia| |].
    { intros c Hc. pose proof (HQT c Hc). pose proof (MS_ge c Hc). pose proof (Hm c Hc). pose proof (SLK_nonneg c Hc). unfold FCNT. change (get_cls st1 c) with (get_cls st c).
      pose proof (LW_cls st c HL Hc) as (_&_&_&_&_&_&_&_&C8&C9).
      assert (nprim [ch] <= 1) by (unfold nprim; cbn; destruct (is_primb ch); cbn; rewrite ?zlen_cons, ?(@zlen_nil achunk); lia). unfold stk in *. lia. }
    intros st2 HL2 HF2 HP2 HG2 HR2.
    assert (N1 : nprim [ch] <= 1) by (unfold nprim; cbn; destruct (is_primb ch); cbn; rewrite ?zlen_cons, ?(@zlen_nil achunk); lia).
    pose proof (nprim_nonneg [ch]) as N2.
    apply AFTER; [exact HL2| eapply QOK_frq; eauto| lia| rewrite (QT_frq st1 st2 HF2); lia| eapply frel_of_cgrow; [exact HG2| exact N2]|].
    intros c Hc. destruct (HG2 c Hc) as [_ B]. change (get_cls st1 c) with (get_cls st c) in B. lia.
Qed.

Lemma evq_afree_none : forall G st, LW st -> QOK G st -> evq (RPst st frel) [] G (PHI st + 0) (afree st None).
Proof.
  intros G st HL HQ. cbn. split; [exact HL|]. split; [exact HQ|]. split; [| lia]. intros c Hc. pose proof (size_of_class_pos c Hc). split; [destruct (c =? K_BATCH_CLASS); lia|]. split; [lia|]. left; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma evq_aannotate : forall G st p cap old new ch,
  LW st -> QOK G st -> (a_live st) !! p = Some ch -> cap <= chunk_size ch ->
  evq (RPst st crel_n) [] G (PHI st + 0) (aannotate st p cap old new).
Proof.
  intros G st p cap old new ch HL HQ Hl Hcap. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3). unfold aannotate. rewrite Hl.
  assert (RET : evq (RPst st crel_n) [] G (PHI st + 0) (aret st)) by (cbn; split; [exact HL| split; [exact HQ| split; [apply crel_n_refl| lia]]]).
  destruct (negb _) eqn:E1; [apply evq_aundef|].
  apply Bool.negb_false_iff in E1. repeat (apply andb_prop in E1 as [E1 ?]).
  apply Z.leb_le in E1. apply Z.leb_le in H1. apply Z.leb_le in H0. apply Z.leb_le in H.
  destruct (2 ^ 40 <? cap); [apply evq_aundef|].
  destruct (old =? new); [exact RET|].
  destruct (negb (Z.land cap 7 =? 0) && _); [apply evq_aundef|].
  destruct (old <? new) eqn:E2; [|exact RET]. apply Z.ltb_lt in E2.
  assert (Hch : chunk_ok G ch).
  { pose proof (live_chunks_delete st p ch Hl) as HPl. pose proof (Permutation_Forall HPl Q1) as X. apply Forall_cons_iff in X as [X _]. exact X. }
  destruct ch as [c n|mb ms n]; [exact RET|]. cbv zeta. cbn in Hcap.
  destruct (rdn old 8 <? rdn new 8) eqn:E3; [|exact RET]. apply Z.ltb_lt in E3.
  cbn in Hch. destruct Hch as (Hin & Hmb & Hn & Hms).
  pose proof (rdn_le new 8 ltac:(lia)). pose proof (rdn_le old 8 ltac:(lia)).
  assert (0 <= rdn old 8) by (unfold rdn; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
  pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply (evq_poison0 _ [] G _ _ _ _ (mb, ms)); auto; cbn [fst snd chunk_user_beg]; unfold PG in *; lia.
Qed.
End Ev.
End CANSEC1.
