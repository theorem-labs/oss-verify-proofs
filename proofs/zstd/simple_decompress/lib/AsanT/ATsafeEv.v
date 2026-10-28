(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotal AsanFree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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

Fixpoint evq {R} (RP : list (Z * Z) -> R -> Prop) (ga : list Z) (G : list (Z * Z)) (b : Z) (t : AM R) {struct t} : Prop :=
  match t with
  | SRet r => RP G r
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
         \/ (flags = F_FIXED /\ inAP a len /\ len <= b /\ forall z, evq RP ga G (if is_err z then b else b - len) (k z))
         \/ (flags = F_FIXNORES /\ covG G a len /\ forall z, evq RP ga G b (k z)))
    | AMunmap a len => forall z, evq RP ga G b (k z)
    | AMadvise a len => forall z, evq RP ga G b (k z)        (* [comment removed for export] *)
    | _ => False
    end
  end.

(* [comment removed for export] *)
Lemma evq_mono : forall {R} (RP RP' : list (Z * Z) -> R -> Prop) (t : AM R) ga G G' b b',
  evq RP ga G b t -> incl G G' -> b <= b' ->
  (forall G1 G1' r, incl G1 G1' -> RP G1 r -> RP' G1' r) ->
  evq RP' ga G' b' t.
Proof.
  intros R RP RP' t. induction t as [r|e k IH]; intros ga G G' b b' H HI Hb HRP; cbn in H |- *.
  - eapply HRP; [exact HI| exact H].
  - destruct e as [t0|b0|a len prot flags|a len|a l p|a len|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & H)|[(Hf & Hin & Hlb & H)|(Hf & Hc & H)]].
      * left. split; [exact Hf|]. split; [exact Ha|]. destruct ga as [|l0 ga']; [exact H|].
        destruct H as (El & Hlb & H). split; [exact El|]. split; [lia|]. intros z. eapply IH; [exact (H z)| | destruct (is_err z); lia| exact HRP].
        intros g [<-|Hg]; [left; reflexivity| right; apply HI; exact Hg].
      * right; left. split; [exact Hf|]. split; [exact Hin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| exact HI| destruct (is_err z); lia| exact HRP].
      * right; right. split; [exact Hf|]. split; [eapply covG_mono; eauto|]. intros z. eapply IH; [exact (H z)| exact HI| lia| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact HI| exact Hb| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact HI| exact Hb| exact HRP].
Qed.

Lemma evq_mono_b : forall {R} (RP : list (Z * Z) -> R -> Prop) (t : AM R) ga G b b',
  evq RP ga G b t -> b <= b' -> evq RP ga G b' t.
Proof.
  intros R RP t. induction t as [r|e k IH]; intros ga G b b' H Hb; cbn in H |- *.
  - exact H.
  - destruct e as [t0|b0|a len prot flags|a len|a l p|a len|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & H)|[(Hf & Hin & Hlb & H)|(Hf & Hc & H)]].
      * left. split; [exact Hf|]. split; [exact Ha|]. destruct ga as [|l0 ga']; [exact H|].
        destruct H as (El & Hlb & H). split; [exact El|]. split; [lia|]. intros z. eapply IH; [exact (H z)| destruct (is_err z); lia].
      * right; left. split; [exact Hf|]. split; [exact Hin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| destruct (is_err z); lia].
      * right; right. split; [exact Hf|]. split; [exact Hc|]. intros z. eapply IH; [exact (H z)| lia].
    + intros z. eapply IH; [exact (H z)| exact Hb].
    + intros z. eapply IH; [exact (H z)| exact Hb].
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

Definition CBM : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + K_PTRARR_RESERVE.

Definition cls_lw (r : aclass) : Prop :=
  0 <= c_mapped_user r <= K_FREEARR_OFF /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0.
Definition LW (st : astate) : Prop :=
  a_space_beg st = SB /\ a_ptr_array st = PA /\ 0 <= a_nres st /\ 8 * a_nres st <= K_PTRARR_RESERVE
  /\ forall c, 1 <= c <= 31 -> cls_lw (get_cls st c).

(* [comment removed for export] *)
Definition PHI (st : astate) : Z := CBM - commit_bytes st.

Lemma commit_bytes_LW : forall st, LW st -> 0 <= commit_bytes st <= CBM.
Proof.
  intros st (_ & _ & N0 & N1 & HC). unfold commit_bytes, CBM.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX) ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  pose proof (csum_nonneg cls_mapped_bytes' st ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  lia.
Qed.
Lemma PHI_nonneg : forall st, LW st -> 0 <= PHI st.
Proof. intros st H. pose proof (commit_bytes_LW st H). unfold PHI. lia. Qed.

(* [comment removed for export] *)
Lemma LW_put : forall st c r, LW st -> 1 <= c <= 31 -> cls_lw r -> LW (put_cls c r st).
Proof.
  intros st c r (S1 & S2 & N0 & N1 & HC) Hc Hr. unfold LW. cbn [a_space_beg a_ptr_array a_nres put_cls set_cls].
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
  intros c' Hc'. destruct (Z.eq_dec c c') as [<-|NE].
  - rewrite get_put_eq. exact Hr.
  - rewrite get_put_ne by exact NE. apply HC. exact Hc'.
Qed.
Lemma LW_cls : forall st c, LW st -> 1 <= c <= 31 -> cls_lw (get_cls st c).
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
Lemma LW_same_but : forall c st st', same_but c st st' -> LW st -> cls_lw (get_cls st' c) -> LW st'.
Proof.
  intros c st st' (E1&E2&E3&_&_&_&_&_&_&_&_&HG) (S1 & S2 & N0 & N1 & HC) Hc'. unfold LW. rewrite E1, E2, E3.
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
  intros c' Hr. destruct (Z.eq_dec c' c) as [->|NE]; [exact Hc'|]. rewrite HG by exact NE. apply HC. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod_sub_mult : forall x y m, 0 < m -> x mod m = 0 -> y mod m = 0 -> (x - y) mod m = 0.
Proof.
  intros x y m Hm Hx Hy. rewrite Zminus_mod, Hx, Hy. reflexivity.
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
  (forall st' ok, LW st' -> same_but c st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (ensure_free_array st c nf k).
Proof.
  intros R RP ga G st c nf k extra HL Hc Hex Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  unfold ensure_free_array.
  destruct (nf * 4 <=? _) eqn:E1. { apply (Hk st true HL (same_but_refl c st)). lia. }
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
  set (r' := cls_set_mapped_free_array nm (get_cls st c)).
  assert (Hr' : cls_lw r') by (unfold r', cls_lw; cbn; lia).
  assert (HL' : LW (put_cls c r' st)) by (apply LW_put; auto).
  assert (EP : PHI (put_cls c r' st) = PHI st - (nm - c_mapped_free_array (get_cls st c)))
    by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
  pose proof (PHI_nonneg _ HL') as P0.
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL (same_but_refl c st)). lia.
  - replace (PHI st + extra - (nm - c_mapped_free_array (get_cls st c))) with (PHI (put_cls c r' st) + extra) by lia.
    apply Hk; [exact HL'| apply same_but_put| lia].
Qed.

Lemma evq_populate : forall {R} RP ga G st c req (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> same_but c st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (populate_free_array st c req k).
Proof.
  intros R RP ga G st c req k extra HL Hc Hex Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  unfold populate_free_array. cbv zeta.
  (* [comment removed for export] *)
  assert (AFTER : forall st1, LW st1 -> same_but c st st1 -> PHI st1 <= PHI st ->
    evq RP ga G (PHI st1 + extra)
      (ensure_free_array st1 c (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c)
         (fun st2 ok => if negb ok then k st2 false else
            k (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c * size_of_class c)
                            (cls_set_num_freed (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c) (get_cls st2 c))) st2) true))).
  { intros st1 HL1 HS1 HP1. apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HS2 HP2. destruct ok; cbn [negb].
    - set (r3 := cls_set_allocated_user _ (cls_set_num_freed _ (get_cls st2 c))).
      assert (Hr3 : cls_lw r3) by (pose proof (LW_cls st2 c HL2 Hc) as X; unfold r3, cls_lw in *; cbn; exact X).
      replace (PHI st2 + extra) with (PHI (put_cls c r3 st2) + extra) by (rewrite PHI_put by exact Hc; unfold r3, cls_mapped_bytes'; cbn; lia).
      apply Hk; [apply LW_put; auto| eapply same_but_trans; [eapply same_but_trans; [exact HS1| exact HS2]| apply same_but_put]|].
      rewrite PHI_put by exact Hc. unfold r3, cls_mapped_bytes'; cbn. lia.
    - apply Hk; [exact HL2| eapply same_but_trans; [exact HS1| exact HS2]| lia]. }
  destruct (_ <=? c_mapped_user (get_cls st c)) eqn:E1. { apply AFTER; [exact HL| apply same_but_refl| lia]. }
  apply Z.leb_gt in E1.
  set (ums := rup _ K_USER_MAP).
  destruct (K_FREEARR_OFF <? _) eqn:E2. { apply evq_aundef. }
  apply Z.ltb_ge in E2.
  pose proof (rup_ge (c_allocated_user (get_cls st c) + req * size_of_class c - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RG. fold ums in RG.
  pose proof (rup_mod (c_allocated_user (get_cls st c) + req * size_of_class c - c_mapped_user (get_cls st c)) K_USER_MAP ltac:(unfold K_USER_MAP; lia)) as RM. fold ums in RM.
  assert (D : (4096 | K_USER_MAP)) by (exists 64; reflexivity).
  set (r' := cls_set_mapped_user (c_mapped_user (get_cls st c) + ums) (get_cls st c)).
  assert (Hr' : cls_lw r').
  { unfold r', cls_lw; cbn. split; [lia|]. split; [| split; [exact F1| exact F2]].
    rewrite Z.add_mod, U2, RM by (unfold K_USER_MAP; lia). reflexivity. }
  assert (HL' : LW (put_cls c r' st)) by (apply LW_put; auto).
  assert (EP : PHI (put_cls c r' st) = PHI st - ums) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
  pose proof (PHI_nonneg _ HL') as P0.
  cbn -[evq Z.sub Z.add Z.mul Z.div rup region_beg K_FREEARR_OFF ums get_cls put_cls cls_set_mapped_user cls_set_allocated_user cls_set_num_freed
        fixed_answer_ok is_err PHI ensure_free_array size_of_class].
  split; [reflexivity|]. split; [lia|]. split.
  { apply Znumtheory.Zdivide_mod. apply (div4096_of_mod ums K_USER_MAP); [exact D| unfold K_USER_MAP; lia| exact RM]. }
  right; left. split; [reflexivity|]. split.
  { apply (region_in_arena st c); auto; try lia. unfold K_FREEARR_OFF, K_REGION in *. lia. }
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL (same_but_refl c st)). lia.
  - replace (PHI st + extra - ums) with (PHI (put_cls c r' st) + extra) by lia.
    apply AFTER; [exact HL'| apply same_but_put| lia].
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

Lemma evq_cache_alloc : forall {R} RP ga G st c (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st' ok)) ->
  evq RP ga G (PHI st + extra) (cache_alloc st c k).
Proof.
  intros R RP ga G st c k extra HL Hc Hex Hk. unfold cache_alloc. cbv zeta.
  destruct (0 <? _).
  { set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st c HL Hc) as X; exact X).
    replace (PHI st + extra) with (PHI (put_cls c r' st) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| apply frq_put| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia]. }
  pose proof (LW_init_cache st HL) as HL1.
  assert (TAKE : forall st2, LW st2 -> frq st st2 -> PHI st2 <= PHI st ->
    evq RP ga G (PHI st2 + extra)
      (if c_num_freed (get_cls st2 c) <? max_count (init_cache st) c / 2 then aundef_ (UCheck 229) (k st2 false)
       else k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)).
  { intros st2 HL2 HF2 HP2. destruct (_ <? _); [apply evq_aundef|].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    replace (PHI st2 + extra) with (PHI (put_cls c r' st2) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [exact HF2| apply frq_put]| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia]. }
  destruct (_ <=? _).
  - rewrite <- (PHI_init_cache st). apply TAKE; [exact HL1| apply frq_init_cache| rewrite PHI_init_cache; lia].
  - rewrite <- (PHI_init_cache st). apply evq_populate; auto.
    intros st2 ok HL2 HS2 HP2. rewrite PHI_init_cache in HP2. destruct ok.
    + apply TAKE; [exact HL2| eapply frq_trans; [apply frq_init_cache| eapply frq_same_but; exact HS2]| exact HP2].
    + apply Hk; [exact HL2| eapply frq_trans; [apply frq_init_cache| eapply frq_same_but; exact HS2]| exact HP2].
Qed.

Lemma evq_cache_dealloc : forall {R} RP ga G st c (k : astate -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (cache_dealloc st c k).
Proof.
  intros R RP ga G st c k extra HL Hc Hex Hk. unfold cache_dealloc. cbv zeta.
  pose proof (LW_init_cache st HL) as HL1.
  destruct (_ =? _).
  - rewrite <- (PHI_init_cache st). apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HS2 HP2. rewrite PHI_init_cache in HP2. destruct ok; cbn [negb]; [|apply evq_aundef].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    replace (PHI st2 + extra) with (PHI (put_cls c r' st2) + extra) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [apply frq_init_cache| eapply frq_trans; [eapply frq_same_but; exact HS2| apply frq_put]]| rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia].
  - set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls (init_cache st) c HL1 Hc) as X; exact X).
    replace (PHI st + extra) with (PHI (put_cls c r' (init_cache st)) + extra) by (rewrite PHI_put by exact Hc; rewrite PHI_init_cache; unfold r', cls_mapped_bytes'; cbn; rewrite get_cls_init_cache; lia).
    apply Hk; [apply LW_put; auto| eapply frq_trans; [apply frq_init_cache| apply frq_put]|].
    rewrite PHI_put by exact Hc. rewrite PHI_init_cache. unfold r', cls_mapped_bytes'; cbn. rewrite get_cls_init_cache. lia.
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
  LW st -> 64512 < n <= 2^40 ->
  (forall G' st' och, incl G G' -> LW st' -> frq st st' -> PHI st' <= PHI st ->
     (forall ch, och = Some ch -> chunk_ok G' ch /\ ch = CSec (match ch with CSec mb _ _ => mb | _ => 0 end) (sec_map_size n) n) ->
     evq RP [] G' (PHI st' + 0) (k st' och)) ->
  evq RP [sec_map_size n] G (PHI st + sec_map_size n) (large_alloc ATOP RESV st n k).
Proof.
  intros R RESV RP G st n k HL Hn Hk. pose proof HL as (S1 & S2 & N0 & N1 & HC).
  pose proof (sec_map_size_ge n ltac:(lia)) as SG. pose proof (rz_size_large n ltac:(lia)) as RZ.
  pose proof (PHI_nonneg st HL) as P0.
  unfold large_alloc. cbv zeta. cbn [evq ev].
  split; [reflexivity|]. split; [lia|]. split; [apply sec_map_size_mod|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP _ z)) eqn:E0; [apply evq_aundef|].
  destruct (is_err z) eqn:E1.
  { eapply evq_mono_b; [apply (Hk ((z, sec_map_size n) :: G) st None); auto| lia].
    - intros g Hg; right; exact Hg. - apply frq_refl. - lia. - intros ch H; discriminate. }
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
    assert (EPn : PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) = PHI st - K_PTRARR_COMMIT).
    { rewrite PHI_set_nres. cbn [a_nres set_nsec]. rewrite PHI_set_nsec. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK. lia. }
    assert (HLn : LW (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))).
    { unfold LW. cbn [a_space_beg a_ptr_array a_nres set_nres set_nsec]. split; [exact S1|]. split; [exact S2|].
      split; [unfold K_CHUNKS_BLOCK; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|]. intros c Hc. apply HC. exact Hc. }
    pose proof (PHI_nonneg _ HLn). split; [lia|].
    intros r. destruct (negb (fixed_answer_ok _ r)); [apply evq_aundef|]. destruct (is_err r); [apply evq_aundef|].
    replace (PHI st + sec_map_size n - sec_map_size n - K_PTRARR_COMMIT) with (PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + 0) by lia.
    apply Hk; [intros g Hg; right; exact Hg| exact HLn| unfold frq; auto| rewrite EPn; unfold K_PTRARR_COMMIT; lia|].
    intros ch0 [= <-]. apply CH. left; reflexivity.
  - replace (PHI st + sec_map_size n - sec_map_size n) with (PHI (set_nsec (a_nsec st + 1) st) + 0) by (rewrite PHI_set_nsec; lia).
    apply Hk; [intros g Hg; right; exact Hg| apply LW_set_nsec; exact HL| unfold frq; auto| rewrite PHI_set_nsec; lia|].
    intros ch0 [= <-]. apply CH. left; reflexivity.
Qed.

Lemma evq_large_dealloc : forall {R} RP ga G st mb ms n (k : astate -> AM R) extra,
  LW st -> chunk_ok G (CSec mb ms n) ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
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
      apply Hk; [apply LW_set_nsec; exact HL| unfold frq; auto| rewrite PHI_set_nsec; lia].
    - destruct (is_err z); apply evq_aundef. }
  destruct (_ <? _); cbn; [intros _|]; exact UN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RPst (G : list (Z * Z)) (st' : astate) : Prop := LW st' /\ Forall (chunk_ok G) (all_chunks [] [] st').
Definition RPm (G : list (Z * Z)) (r : astate * option AsanCtrl.aptr) : Prop := let (st', _) := r in RPst G st'.

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

Lemma evq_amalloc : forall RESV G st n,
  LW st -> Forall (chunk_ok G) (all_chunks [] [] st) -> next_fresh st -> 0 <= n ->
  evq RPm (if is_primary n then [] else [sec_map_size n]) G (PHI st + (if is_primary n then 0 else sec_map_size n)) (amalloc ATOP RESV st n).
Proof.
  intros RESV G st n HL HF HNF Hn. unfold amalloc. cbv zeta.
  destruct (_ || _) eqn:E0.
  { unfold RPm, RPst. split; [exact HL| exact HF]. }
  apply Bool.orb_false_iff in E0 as [E0a E0b]. apply Z.ltb_ge in E0a. apply Z.ltb_ge in E0b.
  (* [comment removed for export] *)
  assert (FIN : forall G' st1 ch b, incl G G' -> LW st1 -> frq st st1 -> chunk_ok G' ch ->
            (forall mb ms n0, ch = CSec mb ms n0 -> n0 = n) ->
            evq RPm [] G' b
              (match ch with
               | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))
               | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7)) (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1)))
               end)).
  { intros G' st1 ch b HI HL1 HF1 Hch Hchn.
    assert (HNF1 : (a_live st1) !! (a_next st1) = None).
    { destruct HF1 as (EL & _ & _ & EN). destruct ((a_live st1) !! (a_next st1)) as [c0|] eqn:E; [|reflexivity].
      exfalso. rewrite EL, EN in E. pose proof (HNF _ _ E). lia. }
    assert (POST : RPm G' (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))).
    { unfold RPm, RPst. split; [apply LW_set_next, LW_set_live; exact HL1|].
      unfold all_chunks. cbn [app]. apply all_chunks_live_insert; [exact HNF1| exact Hch|].
      rewrite (all_chunks_frq st st1 HF1). eapply Forall_chunk_ok_mono; eauto. }
    destruct ch as [c0 n0|mb ms n0]; [exact POST|].
    cbn in Hch. destruct Hch as (Hin & Hmb & Hn0 & Hms). specialize (Hchn mb ms n0 eq_refl). subst n0.
    pose proof (land_lnot7 n Hn) as LN. pose proof (rz_log_range n). assert (0 <= rz_size n) by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by lia; lia).
    apply (evq_poison0 RPm [] G' b _ _ _ (mb, ms)); auto; cbn [fst snd chunk_user_beg]; unfold PG in *; lia. }
  destruct (is_primary n) eqn:EP.
  - rewrite Z.add_0_r. replace (PHI st) with (PHI st + 0) by lia.
    pose proof (primary_class_facts n Hn EP) as (C1 & _).
    apply evq_cache_alloc; [exact HL| lia| lia|]. intros st1 ok HL1 HF1 HP1. destruct ok.
    + apply (FIN G st1 (CPrim (class_id (needed_size n)) n)); auto. { apply incl_refl. } { cbn. lia. } { intros; discriminate. }
    + unfold RPm, RPst. split; [exact HL1|]. rewrite (all_chunks_frq st st1 HF1). exact HF.
  - pose proof (not_primary_large n Hn EP) as NL.
    apply evq_large_alloc; [exact HL| lia|]. intros G' st1 och HI HL1 HF1 HP1 HCH. destruct och as [ch|].
    + destruct (HCH ch eq_refl) as [Hch Ech]. apply (FIN G' st1 ch); auto. intros mb ms n0 E. rewrite E in Ech. congruence.
    + unfold RPm, RPst. split; [exact HL1|]. rewrite (all_chunks_frq st st1 HF1). eapply Forall_chunk_ok_mono; eauto.
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

Lemma evq_recycle_chunk : forall {R} RP ga G st ch (k : astate -> AM R) extra,
  LW st -> chunk_ok G ch -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle_chunk st ch k).
Proof.
  intros R RP ga G st ch k extra HL Hch Hex Hk. destruct ch as [c n|mb ms n]; cbn [recycle_chunk].
  - cbn in Hch. apply evq_cache_dealloc; auto.
  - eapply evq_large_dealloc; eauto.
Qed.

Lemma evq_recycle_chunks : forall {R} RP ga G l st (k : astate -> AM R) extra,
  LW st -> Forall (chunk_ok G) l -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle_chunks st l k).
Proof.
  intros R RP ga G l. induction l as [|ch l IH]; intros st k extra HL HF Hex Hk; cbn [recycle_chunks].
  - apply Hk; [exact HL| apply frq_refl| lia].
  - apply Forall_cons_iff in HF as [Hch HF]. eapply evq_recycle_chunk; eauto.
    intros st1 HL1 HF1 HP1. apply IH; auto. intros st2 HL2 HF2 HP2. apply Hk; [exact HL2| eapply frq_trans; eauto| lia].
Qed.

Lemma batch_K : 1 <= K_BATCH_CLASS <= 31. Proof. unfold K_BATCH_CLASS. lia. Qed.

Lemma evq_do_recycle : forall {R} RP ga G bs st (k : astate -> AM R) extra,
  LW st -> Forall (chunk_ok G) (qchunks bs) -> 0 <= extra ->
  (forall st', LW st' -> frq st st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (do_recycle st bs k).
Proof.
  intros R RP ga G bs. induction bs as [|b bs IH]; intros st k extra HL HF Hex Hk; cbn [do_recycle].
  - apply Hk; [exact HL| apply frq_refl| lia].
  - rewrite qchunks_cons in HF. apply Forall_app in HF as [Hb HF].
    apply evq_recycle_chunks; auto. { apply Forall_rev. exact Hb. }
    intros st1 HL1 HF1 HP1. apply evq_cache_dealloc; auto; [apply batch_K|].
    intros st2 HL2 HF2 HP2. apply IH; auto. intros st3 HL3 HF3 HP3.
    apply Hk; [exact HL3| eapply frq_trans; [exact HF1| eapply frq_trans; eauto]| lia].
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

Lemma Forall_incl' : forall {A} (P : A -> Prop) l l', Forall P l' -> incl l l' -> Forall P l.
Proof. intros A P l l' H HI. rewrite Forall_forall in *. intros x Hx. apply H, HI, Hx. Qed.

Lemma evq_recycle : forall {R} RP ga G st mn (k : astate -> AM R) extra,
  LW st -> QOK G st -> 0 <= extra ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (recycle st mn k).
Proof.
  intros R RP ga G st mn k extra HL HQ Hex Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold recycle. cbv zeta.
  destruct (_ <? _); [apply evq_aundef|].
  assert (TAIL : forall gl extracted exb, incl (qchunks (gl ++ extracted)) (qchunks (a_qglob st)) ->
    evq RP ga G (PHI st + extra)
      (let '(taken, rest, bytes2) := dequeue_while gl (a_qglob_bytes st - exb) mn in
       if mn <? bytes2 then aundef_ (UCheck 0) (k st) else do_recycle (set_qglob rest bytes2 st) (extracted ++ taken) k)).
  2:{ destruct (_ && _).
      - destruct (a_qglob st) as [|b0 rest0] eqn:EQ.
        + cbv beta iota. apply TAIL. rewrite ?EQ. cbn. intros x Hx; exact Hx.
        + pose proof (merge_batches_incl rest0 b0) as HM. destruct (merge_batches b0 rest0) as [[gl extracted] exb].
          cbv beta iota. apply TAIL. rewrite ?EQ. exact HM.
      - cbv beta iota. apply TAIL. rewrite app_nil_r. apply incl_refl. }
  intros gl extracted exb HM.
  pose proof (dequeue_while_spec gl (a_qglob_bytes st - exb) mn) as HD.
  destruct (dequeue_while gl (a_qglob_bytes st - exb) mn) as [[taken rest] bytes2]. destruct HD as (HD1 & _ & _).
  destruct (mn <? bytes2); [apply evq_aundef|].
  assert (INC : incl (qchunks (extracted ++ taken) ++ qchunks rest) (qchunks (a_qglob st))).
  { intros ch Hin. apply HM. rewrite <- HD1. rewrite !qchunks_app in *. repeat (apply in_app_iff in Hin as [Hin|Hin]); apply in_app_iff; auto.
    - left. apply in_app_iff. auto. - left. apply in_app_iff. auto. }
  rewrite <- (PHI_set_qglob rest bytes2 st). apply evq_do_recycle; auto.
  { eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. left. exact Hin. }
  intros st1 HL1 HF1 HP1. apply Hk; [exact HL1| | rewrite PHI_set_qglob in HP1; exact HP1].
  apply (QOK_frq G (set_qglob rest bytes2 st) st1 HF1). apply QOK_parts. cbn [a_qloc a_qglob set_qglob].
  split; [exact Q1|]. split; [exact Q2|]. eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. right. exact Hin.
Qed.

Lemma evq_drain : forall {R} RP ga G st (k : astate -> AM R) extra,
  LW st -> QOK G st -> 0 <= extra ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (drain st k).
Proof.
  intros R RP ga G st k extra HL HQ Hex Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold drain. cbv zeta. set (st1 := set_qglob _ _ (set_qloc [] 0 st)).
  assert (HQ1 : QOK G st1). { apply QOK_parts. cbn. split; [exact Q1|]. split; [constructor|]. rewrite qchunks_app. apply Forall_app. auto. }
  assert (HL1 : LW st1) by exact HL. assert (EP : PHI st1 = PHI st) by reflexivity.
  destruct (Q_MAX <? _).
  - rewrite <- EP. apply evq_recycle; [exact HL1| exact HQ1| lia|]. intros st2 HL2 HQ2 HP2. apply Hk; [exact HL2| exact HQ2| lia].
  - rewrite <- EP. apply Hk; [exact HL1| exact HQ1| lia].
Qed.

Lemma qchunks_rev_snoc : forall P rl b,
  Forall P (qchunks (rev (b :: rl))) <-> Forall P (qchunks (rev rl)) /\ Forall P (b_chunks b).
Proof. intros P rl b. cbn [rev]. rewrite qchunks_app, Forall_app, qchunks_cons. cbn. rewrite app_nil_r. tauto. Qed.

Lemma evq_enqueue : forall {R} RP ga G st ch (k : astate -> AM R) extra,
  LW st -> QOK G st -> chunk_ok G ch -> 0 <= extra ->
  (forall st', LW st' -> QOK G st' -> PHI st' <= PHI st -> evq RP ga G (PHI st' + extra) (k st')) ->
  evq RP ga G (PHI st + extra) (enqueue st ch k).
Proof.
  intros R RP ga G st ch k extra HL HQ Hch Hex Hk. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3).
  unfold enqueue. cbv zeta.
  assert (NEW : forall st0, LW st0 -> frq st st0 -> PHI st0 <= PHI st ->
    evq RP ga G (PHI st0 + extra)
      (cache_alloc st0 K_BATCH_CLASS (fun st1 ok => if negb ok then aundef_ USpin (k st1)
         else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1)))).
  { intros st0 HL0 HF0 HP0. apply evq_cache_alloc; auto; [apply batch_K|]. intros st1 ok HL1 HF1 HP1. destruct ok; cbn [negb]; [|apply evq_aundef].
    rewrite <- (PHI_set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1).
    apply Hk; [apply LW_set_qloc; exact HL1| | rewrite PHI_set_qloc; lia].
    pose proof (QOK_frq G st st1 (frq_trans _ _ _ HF0 HF1) HQ) as HQ1. apply QOK_parts in HQ1 as (R1 & R2 & R3).
    apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live]. split; [exact R1|]. split; [| exact R3].
    rewrite qchunks_app, Forall_app. split; [exact R2|]. rewrite qchunks_cons. cbn. constructor; [exact Hch| constructor]. }
  destruct (rev (a_qloc st)) as [|b rl] eqn:ER.
  - apply NEW; [exact HL| apply frq_refl| lia].
  - destruct (b_count b =? Q_BATCH). { apply NEW; [exact HL| apply frq_refl| lia]. }
    rewrite <- (PHI_set_qloc (rev (mkABatch (b_count b + 1) (b_size b + chunk_size ch) (ch :: b_chunks b) :: rl)) (a_qloc_bytes st + chunk_size ch) st).
    apply Hk; [apply LW_set_qloc; exact HL| | rewrite PHI_set_qloc; lia].
    apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live]. split; [exact Q1|]. split; [| exact Q3].
    assert (E : a_qloc st = rev (b :: rl)) by (rewrite <- ER, rev_involutive; reflexivity).
    rewrite E in Q2. apply qchunks_rev_snoc in Q2 as [Q2a Q2b]. apply qchunks_rev_snoc. split; [exact Q2a|]. cbn. constructor; assumption.
Qed.

Lemma evq_afree : forall G st id,
  LW st -> QOK G st ->
  evq RPst [] G (PHI st + 0) (afree st (Some id)).
Proof.
  intros G st id HL HQ. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3). unfold afree.
  destruct ((a_live st) !! id) as [ch|] eqn:Hl; [|apply evq_aundef]. cbv zeta.
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  pose proof (Permutation_Forall HPl Q1) as Q1'. apply Forall_cons_iff in Q1' as [Hch Q1d].
  set (st1 := set_live (delete id (a_live st)) st).
  assert (HQ1 : QOK G st1). { apply QOK_parts. cbn [a_qloc a_qglob st1 set_live]. split; [exact Q1d|]. auto. }
  assert (HL1 : LW st1) by exact HL. assert (EP : PHI st1 = PHI st) by reflexivity.
  assert (AFTER : forall st2, LW st2 -> QOK G st2 -> PHI st2 <= PHI st ->
    evq RPst [] G (PHI st2 + 0) (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)).
  { intros st2 HL2 HQ2 HP2. destruct (Q_CACHE <? _).
    - apply evq_drain; [exact HL2| exact HQ2| lia|]. intros st3 HL3 HQ3 HP3. cbn. split; assumption.
    - cbn. split; assumption. }
  rewrite <- EP. destruct (chunk_size ch <=? Q_MAX).
  - apply evq_enqueue; [exact HL1| exact HQ1| exact Hch| lia|]. intros st2 HL2 HQ2 HP2. apply AFTER; [exact HL2| exact HQ2| lia].
  - apply (evq_recycle_chunk RPst [] G st1 ch); [exact HL1| exact Hch| lia|]. intros st2 HL2 HF2 HP2. apply AFTER; [exact HL2| eapply QOK_frq; eauto| lia].
Qed.

Lemma evq_afree_none : forall G st, LW st -> QOK G st -> evq RPst [] G (PHI st + 0) (afree st None).
Proof. intros G st HL HQ. cbn. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma evq_aannotate : forall G st p cap old new ch,
  LW st -> QOK G st -> (a_live st) !! p = Some ch -> cap <= chunk_size ch ->
  evq RPst [] G (PHI st + 0) (aannotate st p cap old new).
Proof.
  intros G st p cap old new ch HL HQ Hl Hcap. pose proof (proj1 (QOK_parts G st) HQ) as (Q1 & Q2 & Q3). unfold aannotate. rewrite Hl.
  assert (RET : evq RPst [] G (PHI st + 0) (aret st)) by (cbn; split; assumption).
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
  apply (evq_poison0 RPst [] G _ _ _ _ (mb, ms)); auto; cbn [fst snd chunk_user_beg]; unfold PG in *; lia.
Qed.
End Ev.
End CANSEC1.
