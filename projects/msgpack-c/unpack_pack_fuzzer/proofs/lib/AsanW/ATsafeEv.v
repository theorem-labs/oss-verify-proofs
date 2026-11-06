(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotal AsanFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition pcost (len : Z) : Z := len / 4096 + len / 32768 + 4.
Lemma pcost_nonneg : forall l, 0 <= l -> 0 <= pcost l.
Proof. intros. unfold pcost. pose proof (Z.div_pos l 4096). pose proof (Z.div_pos l 32768). lia. Qed.
Lemma pcost_mono : forall a b, a <= b -> pcost a <= pcost b.
Proof. intros a b H. unfold pcost. pose proof (Z.div_le_mono a b 4096 ltac:(lia) H). pose proof (Z.div_le_mono a b 32768 ltac:(lia) H). lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Ev.
Variables (SB PA : Z).

Definition inAP (a n : Z) : Prop :=
  (SB <= a /\ a + n <= SB + K_SPACE_SIZE) \/ (PA <= a /\ a + n <= PA + K_PTRARR_RESERVE).

Fixpoint evq {R} (RP : Z -> R -> Prop) (gp b : Z) (t : AM R) {struct t} : Prop :=
  match t with
  | SRet r => RP gp r
  | SVis e k =>
    match e with
    | AUndef _ => True
    | AMmap a len prot flags =>
        prot = PROT_RW /\ 0 < len /\ len mod 4096 = 0 /\
        ((flags = F_ANON /\ a = 0 /\ pcost len <= gp /\ len <= b /\ forall z, evq RP (gp - pcost len) (b - len) (k z))
         \/ (flags = F_FIXED /\ inAP a len /\ len <= b /\ forall z, evq RP gp (if is_err z then b else b - len) (k z)))
    | AMmapT len =>
        0 < len /\ len mod 4096 = 0 /\ pcost len <= gp /\ len <= b /\
        forall z, evq RP (if is_err z then gp else gp - pcost len) (if is_err z then b else b - len) (k z)
    | AMunmap a len => forall z, evq RP gp b (k z)
    | AMadvise a len => forall z, evq RP gp b (k z)
    | _ => False
    end
  end.

Lemma evq_mono : forall {R} (RP RP' : Z -> R -> Prop) (t : AM R) gp gp' b b',
  evq RP gp b t -> gp <= gp' -> b <= b' ->
  (forall g g' r, g <= g' -> RP g r -> RP' g' r) ->
  evq RP' gp' b' t.
Proof.
  intros R RP RP' t. induction t as [r|e k IH]; intros gp gp' b b' H Hg Hb HRP; cbn in H |- *.
  - eapply HRP; [exact Hg| exact H].
  - destruct e as [t0|b0|a len prot flags|a len|a l p|a len|len|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & Hpc & Hlb & H)|(Hf & Hin & Hlb & H)].
      * left. split; [exact Hf|]. split; [exact Ha|]. split; [lia|]. split; [lia|].
        intros z. eapply IH; [exact (H z)| lia| lia| exact HRP].
      * right. split; [exact Hf|]. split; [exact Hin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| exact Hg| destruct (is_err z); lia| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact Hg| exact Hb| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact Hg| exact Hb| exact HRP].
    + destruct H as (Hl & Hm & Hpc & Hlb & H). split; [exact Hl|]. split; [exact Hm|]. split; [lia|]. split; [lia|].
      intros z. eapply IH; [exact (H z)| destruct (is_err z); lia| destruct (is_err z); lia| exact HRP].
Qed.

Definition RPmono {R} (RP : Z -> R -> Prop) : Prop := forall g g' r, g <= g' -> RP g r -> RP g' r.

Lemma evq_mono_b : forall {R} (RP : Z -> R -> Prop) (t : AM R) gp gp' b b',
  RPmono RP -> evq RP gp b t -> gp <= gp' -> b <= b' -> evq RP gp' b' t.
Proof. intros R RP t gp gp' b b' HM H Hg Hb. eapply evq_mono; eauto. Qed.

Lemma evq_aundef : forall {R} RP gp b w (k : AM R), evq RP gp b (aundef_ w k).
Proof. intros. cbn. exact I. Qed.

Definition CBM : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + K_PTRARR_RESERVE.

Definition emb_cap (st : astate) : Z := snd (fst (a_emb st)).
Definition cls_lw (r : aclass) : Prop :=
  0 <= c_mapped_user r <= K_FREEARR_OFF /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0.
Definition emb_lw (st : astate) : Prop := 0 <= emb_cap st <= EMB_MAX /\ emb_cap st mod 4096 = 0 /\ 0 <= emb_sz st.

Definition chunk_cls_ok (ch : achunk) : Prop := match ch with CPrim c _ => 1 <= c <= 31 | CSec _ _ _ => True end.
Definition QOK (st : astate) : Prop := Forall chunk_cls_ok (all_chunks [] [] st).
Definition LW (st : astate) : Prop :=
  a_space_beg st = SB /\ a_ptr_array st = PA /\ 0 <= a_nres st /\ 8 * a_nres st <= K_PTRARR_RESERVE
  /\ (forall c, 1 <= c <= 31 -> cls_lw (get_cls st c)) /\ emb_lw st /\ QOK st.

Definition PHI (st : astate) : Z := CBM - commit_bytes st.

Definition PEMB : Z := pcost EMB_MAX.
Definition GP (st : astate) : Z := PEMB * ((EMB_MAX - emb_cap st) / 4096).

Definition EXB : Z := 4 * EMB_MAX.

Lemma PEMB_pos : 0 < PEMB. Proof. reflexivity. Qed.
Lemma GP_nonneg : forall st, emb_lw st -> 0 <= GP st.
Proof. intros st (H1 & _). unfold GP. pose proof PEMB_pos. pose proof (Z.div_pos (EMB_MAX - emb_cap st) 4096 ltac:(lia) ltac:(lia)). nia. Qed.

Lemma commit_bytes_LW : forall st, LW st -> 0 <= commit_bytes st <= CBM.
Proof.
  intros st (_ & _ & N0 & N1 & HC & _). unfold commit_bytes, CBM.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX) ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  pose proof (csum_nonneg cls_mapped_bytes' st ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  lia.
Qed.
Lemma PHI_nonneg : forall st, LW st -> 0 <= PHI st.
Proof. intros st H. pose proof (commit_bytes_LW st H). unfold PHI. lia. Qed.

Lemma LW_put : forall st c r, LW st -> 1 <= c <= 31 -> cls_lw r -> LW (put_cls c r st).
Proof.
  intros st c r (S1 & S2 & N0 & N1 & HC & HE) Hc Hr. unfold LW. cbn [a_space_beg a_ptr_array a_nres put_cls set_cls].
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|]. split; [| exact HE].
  intros c' Hc'. destruct (Z.eq_dec c c') as [<-|NE].
  - rewrite get_put_eq. exact Hr.
  - rewrite get_put_ne by exact NE. apply HC. exact Hc'.
Qed.
Lemma LW_cls : forall st c, LW st -> 1 <= c <= 31 -> cls_lw (get_cls st c).
Proof. intros st c (_ & _ & _ & _ & HC & _) Hc. apply HC. exact Hc. Qed.
Lemma LW_emb : forall st, LW st -> emb_lw st.
Proof. intros st (_ & _ & _ & _ & _ & HE & _). exact HE. Qed.
Lemma LW_qok : forall st, LW st -> QOK st.
Proof. intros st (_ & _ & _ & _ & _ & _ & HQ). exact HQ. Qed.
Lemma QOK_parts : forall st, QOK st <-> Forall chunk_cls_ok (live_chunks st) /\ Forall chunk_cls_ok (qchunks (a_qloc st)) /\ Forall chunk_cls_ok (qchunks (a_qglob st)).
Proof. intros st. unfold QOK, all_chunks, qbatches. cbn [app]. rewrite qchunks_app, !Forall_app. tauto. Qed.

Lemma LW_chunks : forall st st', LW st ->
  a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> a_nres st' = a_nres st -> a_cls st' = a_cls st -> a_emb st' = a_emb st ->
  QOK st' -> LW st'.
Proof.
  intros st st' (S1 & S2 & N0 & N1 & HC & HE & _) E1 E2 E3 E4 E5 HQ. unfold LW. rewrite E1, E2, E3.
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|]. split; [| split; [| exact HQ]].
  - intros c Hc. unfold get_cls. rewrite E4. apply HC. exact Hc.
  - unfold emb_lw, emb_cap, emb_sz in *. rewrite E5. exact HE.
Qed.
Lemma LW_init_cache : forall st, LW st -> LW (init_cache st).
Proof. intros st H. unfold init_cache. destruct (a_cinit st); [exact H|]. exact H. Qed.
Lemma LW_set_nsec : forall v st, LW st -> LW (set_nsec v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_next : forall v st, LW st -> LW (set_next v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_exh : forall v st, LW st -> LW (set_exh v st). Proof. intros v st H. exact H. Qed.
Lemma LW_exh_clear : forall c st, LW st -> LW (exh_clear c st). Proof. intros c st H. exact H. Qed.
Lemma LW_exh_set : forall c st, LW st -> LW (exh_set c st). Proof. intros c st H. exact H. Qed.

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
Lemma PHI_set_exh : forall v st, PHI (set_exh v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_emb : forall v st, PHI (set_emb v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_nres : forall v st, PHI (set_nres v st) = PHI st - 8 * (v - a_nres st).
Proof. intros. unfold PHI, commit_bytes. cbn [a_nres set_nres]. unfold csum. rewrite (fold_csum_ext cls_mapped_bytes' st (set_nres v st)) by (intros; reflexivity). lia. Qed.

Lemma GP_put : forall st c r, GP (put_cls c r st) = GP st. Proof. reflexivity. Qed.
Lemma GP_init_cache : forall st, GP (init_cache st) = GP st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma GP_same_but : forall c st st', same_but c st st' -> GP st' = GP st.
Proof. intros c st st' (_&_&_&_&_&_&_&_&_&_&_&_&HE). unfold GP, emb_cap. rewrite HE. reflexivity. Qed.

Lemma mod_sub_mult : forall x y m, 0 < m -> x mod m = 0 -> y mod m = 0 -> (x - y) mod m = 0.
Proof. intros x y m Hm Hx Hy. rewrite Zminus_mod, Hx, Hy. reflexivity. Qed.

Lemma live_chunks_insert_Forall : forall (P : achunk -> Prop) st id ch,
  P ch -> Forall P (live_chunks st) -> Forall P (live_chunks (set_live (<[id := ch]> (a_live st)) st)).
Proof.
  intros P st id ch Hch H. unfold live_chunks in *. cbn [a_live set_live]. rewrite Forall_forall in *.
  intros x Hx. apply in_map_iff in Hx as ([k v] & <- & Hin). cbn [snd].
  apply list_elem_of_In, elem_of_map_to_list in Hin. apply lookup_insert_Some in Hin as [[_ <-]|[_ Hl]]; [exact Hch|].
  apply H. apply in_map_iff. exists (k, v). split; [reflexivity|]. apply list_elem_of_In, elem_of_map_to_list. exact Hl.
Qed.
Lemma live_chunks_delete_Forall : forall (P : achunk -> Prop) st id,
  Forall P (live_chunks st) -> Forall P (live_chunks (set_live (delete id (a_live st)) st)).
Proof.
  intros P st id H. unfold live_chunks in *. cbn [a_live set_live]. rewrite Forall_forall in *.
  intros x Hx. apply in_map_iff in Hx as ([k v] & <- & Hin). cbn [snd].
  apply list_elem_of_In, elem_of_map_to_list in Hin. apply lookup_delete_Some in Hin as [_ Hl].
  apply H. apply in_map_iff. exists (k, v). split; [reflexivity|]. apply list_elem_of_In, elem_of_map_to_list. exact Hl.
Qed.
Lemma LW_live_insert : forall st id ch, LW st -> chunk_cls_ok ch -> LW (set_live (<[id := ch]> (a_live st)) st).
Proof.
  intros st id ch HL Hch. apply (LW_chunks st); try reflexivity; [exact HL|]. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  apply QOK_parts. cbn [a_qloc a_qglob set_live]. split; [apply live_chunks_insert_Forall; assumption| split; assumption].
Qed.
Lemma LW_live_delete : forall st id, LW st -> LW (set_live (delete id (a_live st)) st).
Proof.
  intros st id HL. apply (LW_chunks st); try reflexivity; [exact HL|]. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  apply QOK_parts. cbn [a_qloc a_qglob set_live]. split; [apply live_chunks_delete_Forall; assumption| split; assumption].
Qed.

Lemma region_in_arena : forall st c x y, LW st -> 1 <= c <= 31 -> 0 <= x -> 0 <= y -> x + y <= K_REGION ->
  inAP (region_beg st c + x) y.
Proof.
  intros st c x y (S1 & _) Hc Hx Hy Hxy. left. unfold region_beg. rewrite S1. unfold K_REGION, K_SPACE_SIZE in *. nia.
Qed.

Lemma evq_ensure_free_array : forall {R} RP gx st c nf (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + extra) (ensure_free_array st c nf k).
Proof.
  intros R RP gx st c nf k extra HL Hc Hex Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  unfold ensure_free_array.
  destruct (nf * 4 <=? _) eqn:E1. { apply (Hk st true HL); lia. }
  destruct (K_FREEARR_MAX <? _) eqn:E2. { apply evq_aundef. }
  apply Z.leb_gt in E1. apply Z.ltb_ge in E2. assert (Hnf : 0 <= nf) by lia.
  pose proof (rup_freearr_bounds (nf * 4) ltac:(lia)) as RB.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RM.
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RG.
  set (nm := rup (nf * 4) K_FREEARR_MAP) in *.
  assert (D : (4096 | K_FREEARR_MAP)) by (exists 64; reflexivity).
  cbn -[evq Z.sub Z.add Z.mul rup region_beg K_FREEARR_OFF nm get_cls put_cls cls_set_mapped_free_array fixed_answer_ok is_err PHI GP].
  split; [reflexivity|]. split; [lia|]. split.
  { assert (M1 : nm mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod nm K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact RM]).
    assert (M2 : c_mapped_free_array (get_cls st c) mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod _ K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact F2]).
    apply mod_sub_mult; [lia| exact M1| exact M2]. }
  right. split; [reflexivity|]. split.
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
  - apply (Hk st false HL); lia.
  - replace (PHI st + extra - (nm - c_mapped_free_array (get_cls st c))) with (PHI (put_cls c r' st) + extra) by lia.
    rewrite <- (GP_put st c r'). apply Hk; [exact HL'| lia| rewrite GP_put; lia].
Qed.

Lemma evq_populate_g : forall {R} RP gx (exh : astate -> (astate -> AM R) -> AM R) (clr : astate -> astate) st c req (k : astate -> bool -> AM R) bx EX,
  (forall s, clr s = s \/ clr s = exh_clear c s) ->
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= bx -> 0 <= EX ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + bx + EX) (exh st (fun st' => k st' false)) ->
  evq RP (GP st + gx) (PHI st + bx + EX) (populate_free_array_g exh clr st c req k).
Proof.
  intros R RP gx exh clr st c req k bx EX Hclr HM HL Hc Hbx HEX Hk0 HEXH. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  replace (PHI st + bx + EX) with (PHI st + (bx + EX)) in * by lia. set (extra := bx + EX) in *. assert (Hex : 0 <= extra) by (unfold extra; lia).
  assert (Hk : forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)).
  { intros st' ok H1 H2 H3. eapply evq_mono_b; [exact HM| apply Hk0; eauto| lia| unfold extra; lia]. }
  unfold populate_free_array_g. cbv zeta.

  assert (AFTER : forall st1, LW st1 -> PHI st1 <= PHI st -> GP st1 <= GP st ->
    evq RP (GP st1 + gx) (PHI st1 + extra)
      (ensure_free_array st1 c (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c)
         (fun st2 ok => if negb ok then k st2 false else
            k (clr (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c * size_of_class c)
                            (cls_set_num_freed (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c) (get_cls st2 c))) st2)) true))).
  { intros st1 HL1 HP1 HG1. apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HP2 HG2. destruct ok; cbn [negb].
    - set (r3 := cls_set_allocated_user _ (cls_set_num_freed _ (get_cls st2 c))).
      assert (Hr3 : cls_lw r3) by (pose proof (LW_cls st2 c HL2 Hc) as X; unfold r3, cls_lw in *; cbn; exact X).
      assert (EP0 : PHI (put_cls c r3 st2) = PHI st2) by (rewrite PHI_put by exact Hc; unfold r3, cls_mapped_bytes'; cbn; lia).
      destruct (Hclr (put_cls c r3 st2)) as [EC|EC]; rewrite EC.
      + rewrite <- EP0. change (GP st2) with (GP (put_cls c r3 st2)). apply Hk; [apply LW_put; auto| lia| rewrite GP_put; lia].
      + assert (EP3 : PHI (exh_clear c (put_cls c r3 st2)) = PHI st2) by (change (PHI (exh_clear c (put_cls c r3 st2))) with (PHI (put_cls c r3 st2)); exact EP0).
        assert (EG3 : GP (exh_clear c (put_cls c r3 st2)) = GP st2) by reflexivity.
        rewrite <- EP3, <- EG3.
        apply Hk; [apply LW_exh_clear, LW_put; auto| lia| lia].
    - apply Hk; [exact HL2| lia| lia]. }
  destruct (_ <=? c_mapped_user (get_cls st c)) eqn:E1. { apply AFTER; [exact HL| lia| lia]. }
  apply Z.leb_gt in E1.
  set (ums := rup _ K_USER_MAP).
  destruct (K_FREEARR_OFF <? _) eqn:E2. { exact HEXH. }
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
        fixed_answer_ok is_err PHI GP ensure_free_array size_of_class exh_clear].
  split; [reflexivity|]. split; [lia|]. split.
  { apply Znumtheory.Zdivide_mod. apply (div4096_of_mod ums K_USER_MAP); [exact D| unfold K_USER_MAP; lia| exact RM]. }
  right. split; [reflexivity|]. split.
  { apply (region_in_arena st c); auto; try lia. unfold K_FREEARR_OFF, K_REGION in *. lia. }
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL); lia.
  - replace (PHI st + extra - ums) with (PHI (put_cls c r' st) + extra) by lia.
    rewrite <- (GP_put st c r'). apply AFTER; [exact HL'| lia| rewrite GP_put; lia].
Qed.

Lemma evq_populate : forall {R} RP gx st c req (k : astate -> bool -> AM R) extra,
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + extra + 0) (populate_free_array st c req k).
Proof. intros. unfold populate_free_array. apply evq_populate_g; auto; [lia| apply evq_aundef]. Qed.

Lemma evq_cache_alloc_g : forall {R} RP gx (pop : astate -> Z -> Z -> (astate -> bool -> AM R) -> AM R) st c (k : astate -> bool -> AM R) bx EX,
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= bx -> 0 <= EX ->
  (forall req kk,
     (forall st' ok, LW st' -> PHI st' <= PHI (init_cache st) -> GP st' <= GP (init_cache st) -> evq RP (GP st' + gx) (PHI st' + bx) (kk st' ok)) ->
     evq RP (GP (init_cache st) + gx) (PHI (init_cache st) + bx + EX) (pop (init_cache st) c req kk)) ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + bx + EX) (cache_alloc_g pop st c k).
Proof.
  intros R RP gx pop st c k bx EX HM HL Hc Hbx HEX HPOP Hk0.
  assert (Hk : forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx + EX) (k st' ok)).
  { intros st' ok H1 H2 H3. eapply evq_mono_b; [exact HM| apply Hk0; eauto| lia| lia]. }
  unfold cache_alloc_g. cbv zeta.
  destruct (0 <? _).
  { set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st c HL Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' st) = PHI st) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    rewrite <- EP, <- (GP_put st c r'). apply Hk; [apply LW_put; auto| lia| rewrite GP_put; lia]. }
  pose proof (LW_init_cache st HL) as HL1.
  assert (TAKE : forall st2, LW st2 -> PHI st2 <= PHI st -> GP st2 <= GP st ->
    evq RP (GP st2 + gx) (PHI st2 + bx)
      (if c_num_freed (get_cls st2 c) <? max_count (init_cache st) c / 2 then aundef_ (UCheck 229) (k st2 false)
       else k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)).
  { intros st2 HL2 HP2 HG2. destruct (_ <? _); [apply evq_aundef|].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' st2) = PHI st2) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    rewrite <- EP, <- (GP_put st2 c r'). apply Hk0; [apply LW_put; auto| lia| rewrite GP_put; lia]. }
  destruct (_ <=? _).
  - apply (evq_mono_b RP _ (GP (init_cache st) + gx) (GP st + gx) (PHI (init_cache st) + bx) (PHI st + bx + EX) HM).
    + apply TAKE; [exact HL1| rewrite PHI_init_cache; lia| rewrite GP_init_cache; lia].
    + rewrite GP_init_cache. lia.
    + rewrite PHI_init_cache. lia.
  - rewrite <- (PHI_init_cache st), <- (GP_init_cache st). apply HPOP.
    intros st2 ok HL2 HP2 HG2. rewrite PHI_init_cache in HP2. rewrite GP_init_cache in HG2. destruct ok.
    + apply TAKE; [exact HL2| exact HP2| exact HG2].
    + apply Hk0; [exact HL2| exact HP2| exact HG2].
Qed.

Lemma evq_cache_alloc : forall {R} RP gx st c (k : astate -> bool -> AM R) extra,
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + extra + 0) (cache_alloc st c k).
Proof.
  intros R RP gx st c k extra HM HL Hc Hex Hk. unfold cache_alloc. apply evq_cache_alloc_g; auto; [lia|].
  intros req kk Hkk. apply evq_populate; auto. apply LW_init_cache. exact HL.
Qed.

Lemma evq_cache_dealloc : forall {R} RP gx st c (k : astate -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (cache_dealloc st c k).
Proof.
  intros R RP gx st c k extra HL Hc Hex Hk. unfold cache_dealloc. cbv zeta.
  pose proof (LW_init_cache st HL) as HL1.
  destruct (_ =? _).
  - rewrite <- (PHI_init_cache st), <- (GP_init_cache st). apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HP2 HG2. rewrite PHI_init_cache in HP2. rewrite GP_init_cache in HG2. destruct ok; cbn [negb]; [|apply evq_aundef].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' st2) = PHI st2) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    rewrite <- EP, <- (GP_put st2 c r'). apply Hk; [apply LW_put; auto| lia| rewrite GP_put; lia].
  - set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls (init_cache st) c HL1 Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' (init_cache st)) = PHI st).
    { rewrite PHI_put by exact Hc. rewrite PHI_init_cache. unfold r', cls_mapped_bytes'; cbn. lia. }
    assert (EG : GP (put_cls c r' (init_cache st)) = GP st) by (rewrite GP_put; apply GP_init_cache).
    rewrite <- EP, <- EG. apply Hk; [apply LW_put; auto| lia| lia].
Qed.

Lemma a_emb_eta : forall st, a_emb st = (fst (fst (a_emb st)), emb_cap st, emb_sz st).
Proof. intros st. unfold emb_cap, emb_sz. destruct (a_emb st) as [[d cap] sz]. reflexivity. Qed.

Lemma rup_PG_mod : forall x, rup x PG mod 4096 = 0.
Proof. intros. apply (rup_mod x PG). unfold PG. lia. Qed.

Lemma evq_emb_realloc : forall {R} RP gx RESV st want (k : astate -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> emb_cap st < want -> want <= EMB_MAX - 4095 -> 0 <= bx ->
  (forall st', LW st' -> PHI st' = PHI st -> GP st' + PEMB <= GP st -> emb_sz st' = emb_sz st -> want <= emb_cap st' ->
      evq RP (GP st' + gx) (PHI st' + bx) (k st')) ->
  evq RP (GP st + gx) (PHI st + bx + EMB_MAX) (emb_realloc ATOP RESV st want k).
Proof.
  intros R RP gx RESV st want k bx HM Hgx HL Hw Hwm Hbx Hk. pose proof (LW_emb st HL) as (C1 & C2 & C3).
  unfold emb_realloc. rewrite (a_emb_eta st). cbv zeta.
  pose proof (rup_ge want PG ltac:(unfold PG; lia)) as RG. pose proof (rup_le want PG ltac:(unfold PG; lia)) as RL. pose proof (rup_PG_mod want) as RM.
  set (ncap := rup want PG) in *. unfold PG in RG, RL.
  assert (NC : emb_cap st + 4096 <= ncap <= EMB_MAX).
  { split; [| lia]. pose proof (Z.div_mod ncap 4096 ltac:(lia)). pose proof (Z.div_mod (emb_cap st) 4096 ltac:(lia)). lia. }
  assert (PC : pcost ncap <= PEMB) by (apply pcost_mono; lia).
  pose proof (PHI_nonneg st HL) as P0.

  assert (NEXT : forall mb, let st1 := set_emb (mb, ncap, emb_sz st) st in
            LW st1 /\ PHI st1 = PHI st /\ GP st1 + PEMB <= GP st /\ emb_sz st1 = emb_sz st /\ want <= emb_cap st1).
  { intros mb st1. split; [| split; [reflexivity| split; [| split; [reflexivity| cbn; lia]]]].
    - destruct HL as (S1 & S2 & N0 & N1 & HC & _ & HQ). unfold LW. split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
      split; [exact HC|]. split; [| exact HQ]. unfold emb_lw. change (emb_cap st1) with ncap. change (emb_sz st1) with (emb_sz st). lia.
    - unfold GP, st1, emb_cap. cbn [a_emb set_emb fst snd]. fold (emb_cap st). pose proof PEMB_pos.
      assert ((EMB_MAX - ncap) / 4096 + 1 <= (EMB_MAX - emb_cap st) / 4096).
      { replace (EMB_MAX - emb_cap st) with ((EMB_MAX - ncap) + (ncap - emb_cap st)) by lia.
        pose proof (Z.div_mod ncap 4096 ltac:(lia)). pose proof (Z.div_mod (emb_cap st) 4096 ltac:(lia)).
        replace (ncap - emb_cap st) with ((ncap / 4096 - emb_cap st / 4096) * 4096) by lia.
        rewrite Z.div_add by lia. lia. }
      nia. }
  cbn -[evq Z.sub Z.add PHI GP mmap_answer_ok avoids_all is_err pcost ncap set_emb EMB_MAX].
  split; [reflexivity|]. split; [lia|]. split; [exact RM|].
  left. split; [reflexivity|]. split; [reflexivity|].
  pose proof (GP_nonneg st (LW_emb st HL)) as G0.
  assert (G1 : PEMB <= GP st) by (destruct (NEXT 0) as (L1 & _ & G1 & _); pose proof (GP_nonneg _ (LW_emb _ L1)); lia).
  split; [lia|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP ncap z)); [apply evq_aundef|]. destruct (is_err z); [apply evq_aundef|].
  destruct (negb (avoids_all z ncap _)); [apply evq_aundef|].
  destruct (NEXT z) as (L1 & P1 & G2 & S1 & W1).
  assert (KK : evq RP (GP st + gx - pcost ncap) (PHI st + bx + EMB_MAX - ncap) (k (set_emb (z, ncap, emb_sz st) st))).
  { eapply evq_mono_b; [exact HM| apply Hk; [exact L1| exact P1| exact G2| exact S1| exact W1]| lia| lia]. }
  destruct (emb_cap st =? 0); [exact KK|].
  cbn -[evq Z.sub Z.add PHI GP is_err pcost ncap set_emb EMB_MAX]. intros r.
  destruct (r =? 0); [exact KK|]. destruct (is_err r); apply evq_aundef.
Qed.

Lemma evq_emb_append : forall {R} RP gx RESV st len (k : astate -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> 0 < len -> emb_sz st + len <= EMB_MAX - 4096 -> 0 <= bx ->
  (forall st', LW st' -> PHI st' = PHI st -> GP st' <= GP st -> emb_sz st' = emb_sz st + len ->
      evq RP (GP st' + gx) (PHI st' + bx) (k st')) ->
  evq RP (GP st + gx) (PHI st + bx + 2 * EMB_MAX) (emb_append ATOP RESV st len k).
Proof.
  intros R RP gx RESV st len k bx HM Hgx HL Hlen Hsz Hbx Hk. pose proof (LW_emb st HL) as (C1 & C2 & C3).
  unfold emb_append.

  assert (SET : forall st1, LW st1 -> LW (emb_set_size (emb_sz st1 + len) st1) /\ PHI (emb_set_size (emb_sz st1 + len) st1) = PHI st1
                 /\ GP (emb_set_size (emb_sz st1 + len) st1) = GP st1 /\ emb_sz (emb_set_size (emb_sz st1 + len) st1) = emb_sz st1 + len).
  { intros st1 HL1. pose proof (LW_emb st1 HL1) as (D1 & D2 & D3). unfold emb_set_size. rewrite (a_emb_eta st1).
    split; [| split; [reflexivity| split; [reflexivity| reflexivity]]].
    destruct HL1 as (S1 & S2 & N0 & N1 & HC & _ & HQ). unfold LW. split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
    split; [exact HC|]. split; [| exact HQ]. unfold emb_lw, emb_cap, emb_sz. cbn. unfold emb_cap in D1, D2. unfold emb_sz in D3. lia. }

  assert (GO : forall st1, LW st1 -> PHI st1 = PHI st -> GP st1 <= GP st -> emb_sz st1 = emb_sz st ->
            evq RP (GP st1 + gx) (PHI st1 + bx + EMB_MAX)
              (let '(_, cap, sz) := a_emb st1 in
               if cap <? sz + len then emb_realloc ATOP RESV st1 (sz + len) (fun st2 => k (emb_set_size (sz + len) st2))
               else k (emb_set_size (sz + len) st1))).
  { intros st1 HL1 HP1 HG1 HS1. rewrite (a_emb_eta st1).
    destruct (emb_cap st1 <? emb_sz st1 + len) eqn:E.
    - apply Z.ltb_lt in E. apply evq_emb_realloc; [exact HM| exact Hgx| exact HL1| exact E| lia| exact Hbx|].
      intros st2 HL2 HP2 HG2 HS2 _. destruct (SET st2 HL2) as (L3 & P3 & G3 & S3). rewrite HS2 in *.
      rewrite <- P3, <- G3. apply Hk; [exact L3| lia| pose proof PEMB_pos; lia| lia].
    - destruct (SET st1 HL1) as (L3 & P3 & G3 & S3).
      apply (evq_mono_b RP _ (GP (emb_set_size (emb_sz st1 + len) st1) + gx) (GP st1 + gx) (PHI (emb_set_size (emb_sz st1 + len) st1) + bx) (PHI st1 + bx + EMB_MAX) HM).
      + apply Hk; [exact L3| lia| lia| lia].
      + lia.
      + unfold EMB_MAX. lia. }
  rewrite (a_emb_eta st) at 1.
  destruct (emb_cap st =? 0) eqn:E0.
  - apply Z.eqb_eq in E0.
    replace (PHI st + bx + 2 * EMB_MAX) with (PHI st + (bx + EMB_MAX) + EMB_MAX) by lia.
    apply evq_emb_realloc; [exact HM| exact Hgx| exact HL| rewrite E0; reflexivity| unfold EMB_INIT, EMB_MAX; lia| lia|].
    intros st1 HL1 HP1 HG1 HS1 _. replace (PHI st1 + (bx + EMB_MAX)) with (PHI st1 + bx + EMB_MAX) by lia.
    apply GO; [exact HL1| exact HP1| pose proof PEMB_pos; lia| exact HS1].
  - eapply evq_mono_b; [exact HM| apply (GO st HL eq_refl (Z.le_refl _) eq_refl)| lia| unfold EMB_MAX; lia].
Qed.

Lemma ndigits_range : forall z, 1 <= ndigits z <= 5.
Proof. intros z. unfold ndigits. repeat (destruct (_ <? _)); lia. Qed.

Lemma evq_exh_report : forall {R} RP gx RESV c st (k : astate -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> emb_sz st + 110 <= EMB_MAX - 4096 -> 0 <= bx ->
  (forall st', LW st' -> PHI st' = PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st')) ->
  evq RP (GP st + gx) (PHI st + bx + EXB) (exh_report ATOP RESV c st k).
Proof.
  intros R RP gx RESV c st k bx HM Hgx HL Hsz Hbx Hk. unfold exh_report.
  destruct (exh_mem c st).
  { eapply evq_mono_b; [exact HM| apply (Hk st HL eq_refl (Z.le_refl _))| lia| unfold EXB, EMB_MAX; lia]. }
  pose proof (ndigits_range c). pose proof (ndigits_range (size_of_class c)).
  assert (L2 : 0 < exh_len2 c <= 70) by (unfold exh_len2; lia).
  replace (PHI st + bx + EXB) with (PHI (exh_set c st) + (bx + 2 * EMB_MAX) + 2 * EMB_MAX) by (unfold EXB; change (PHI (exh_set c st)) with (PHI st); lia).
  change (GP st) with (GP (exh_set c st)).
  apply evq_emb_append; [exact HM| exact Hgx| apply LW_exh_set; exact HL| unfold EXH_LEN1; lia| change (emb_sz (exh_set c st)) with (emb_sz st); unfold EXH_LEN1; lia| unfold EMB_MAX; lia|].
  intros st1 HL1 HP1 HG1 HS1. change (emb_sz (exh_set c st)) with (emb_sz st) in HS1. change (PHI (exh_set c st)) with (PHI st) in HP1.
  change (GP (exh_set c st)) with (GP st) in HG1.
  replace (PHI st1 + (bx + 2 * EMB_MAX)) with (PHI st1 + bx + 2 * EMB_MAX) by lia.
  apply evq_emb_append; [exact HM| exact Hgx| exact HL1| lia| unfold EXH_LEN1 in HS1; lia| exact Hbx|].
  intros st2 HL2 HP2 HG2 _. apply Hk; [exact HL2| lia| lia].
Qed.

Lemma emb_sz_init_cache : forall st, emb_sz (init_cache st) = emb_sz st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma evq_cache_alloc_x : forall {R} RP gx RESV st c (k : astate -> bool -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> 1 <= c <= 31 -> emb_sz st + 110 <= EMB_MAX - 4096 -> 0 <= bx ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + bx + EXB) (cache_alloc_x ATOP RESV st c k).
Proof.
  intros R RP gx RESV st c k bx HM Hgx HL Hc Hsz Hbx Hk. unfold cache_alloc_x.
  assert (EX0 : 0 <= EXB) by (unfold EXB, EMB_MAX; lia).
  apply evq_cache_alloc_g; [exact HM| exact HL| exact Hc| exact Hbx| exact EX0| | exact Hk].
  intros req kk Hkk. pose proof (LW_init_cache st HL) as HL1.
  unfold populate_free_array_x. destruct (c =? K_BATCH_CLASS).
  {
    eapply evq_mono_b; [exact HM| apply (evq_populate RP gx (init_cache st) c req kk bx HM HL1 Hc Hbx Hkk)| lia| lia]. }
  apply evq_populate_g; [intros s; right; reflexivity| exact HM| exact HL1| exact Hc| exact Hbx| exact EX0| exact Hkk|].
  apply evq_exh_report; [exact HM| exact Hgx| exact HL1| rewrite emb_sz_init_cache; exact Hsz| exact Hbx|].
  intros st' HL' HP' HG'. apply Hkk; [exact HL'| lia| exact HG'].
Qed.

Lemma sec_map_size_mod : forall n, sec_map_size n mod 4096 = 0.
Proof. intros. unfold sec_map_size. rewrite Z.add_mod, rup_mod by (unfold PG; lia). reflexivity. Qed.

Lemma evq_large_alloc : forall {R} RP gx RESV st n (k : astate -> option achunk -> AM R),
  RPmono RP -> 0 <= gx -> LW st -> 64512 < n <= 2^40 ->
  (forall st' ch, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> chunk_cls_ok ch -> evq RP (GP st' + gx) (PHI st' + 0) (k st' (Some ch))) ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx + pcost (sec_map_size n)) (PHI st' + 0) (k st' None)) ->
  evq RP (GP st + gx + pcost (sec_map_size n)) (PHI st + sec_map_size n) (large_alloc ATOP RESV st n k).
Proof.
  intros R RP gx RESV st n k HM Hgx HL Hn HkS HkN. pose proof HL as (S1 & S2 & N0 & N1 & HC & HE).
  pose proof (sec_map_size_ge n ltac:(lia)) as SG.
  pose proof (PHI_nonneg st HL) as P0. pose proof (GP_nonneg st (LW_emb st HL)) as G0. pose proof (pcost_nonneg (sec_map_size n) ltac:(lia)) as PC0.
  unfold large_alloc. cbv zeta. cbn [evq ev].
  split; [lia|]. split; [apply sec_map_size_mod|]. split; [lia|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP _ z)) eqn:E0; [apply evq_aundef|].
  destruct (is_err z) eqn:E1.
  { eapply evq_mono_b; [exact HM| apply (HkN st HL); lia| lia| lia]. }
  destruct (negb (avoids_all z (sec_map_size n) (RESV ++ asec_ranges st))) eqn:E2; [apply evq_aundef|].
  set (ch := CSec z (sec_map_size n) n).
  destruct (a_nsec st =? a_nres st).
  - destruct (K_PTRARR_RESERVE <? _) eqn:E3; [apply evq_aundef|]. apply Z.ltb_ge in E3.
    cbn [evq ev].
    split; [reflexivity|]. split; [unfold K_PTRARR_COMMIT; lia|]. split; [reflexivity|].
    right. split; [reflexivity|]. split.
    { right. rewrite S2. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *. lia. }
    assert (EPn : PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) = PHI st - K_PTRARR_COMMIT).
    { rewrite PHI_set_nres. cbn [a_nres set_nsec]. rewrite PHI_set_nsec. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK. lia. }
    assert (HLn : LW (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))).
    { unfold LW. cbn [a_space_beg a_ptr_array a_nres set_nres set_nsec]. split; [exact S1|]. split; [exact S2|].
      split; [unfold K_CHUNKS_BLOCK; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|]. split; [exact HC| exact HE]. }
    pose proof (PHI_nonneg _ HLn). split; [lia|].
    intros r. destruct (negb (fixed_answer_ok _ r)); [apply evq_aundef|]. destruct (is_err r); [apply evq_aundef|].
    replace (PHI st + sec_map_size n - sec_map_size n - K_PTRARR_COMMIT) with (PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + 0) by lia.
    replace (GP st + gx + pcost (sec_map_size n) - pcost (sec_map_size n)) with (GP (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + gx) by (change (GP (set_nres _ (set_nsec _ st))) with (GP st); lia).
    apply HkS; [exact HLn| rewrite EPn; unfold K_PTRARR_COMMIT; lia| change (GP (set_nres _ (set_nsec _ st))) with (GP st); lia| exact I].
  - replace (PHI st + sec_map_size n - sec_map_size n) with (PHI (set_nsec (a_nsec st + 1) st) + 0) by (rewrite PHI_set_nsec; lia).
    replace (GP st + gx + pcost (sec_map_size n) - pcost (sec_map_size n)) with (GP (set_nsec (a_nsec st + 1) st) + gx) by (change (GP (set_nsec _ st)) with (GP st); lia).
    apply HkS; [apply LW_set_nsec; exact HL| rewrite PHI_set_nsec; lia| change (GP (set_nsec _ st)) with (GP st); lia| exact I].
Qed.

Lemma evq_large_dealloc : forall {R} RP gx st mb ms (k : astate -> AM R) extra,
  LW st ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (large_dealloc st mb ms k).
Proof.
  intros R RP gx st mb ms k extra HL Hk. unfold large_dealloc, poison0, flush_shadow. cbv zeta.
  assert (UNM : evq RP (GP st + gx) (PHI st + extra)
            (ev (AMunmap mb ms) (fun r => if r =? 0 then k (set_nsec (a_nsec st - 1) st)
                                          else if is_err r then aundef_ USpin (k (set_nsec (a_nsec st - 1) st))
                                          else aundef_ UBadAnswer (k (set_nsec (a_nsec st - 1) st))))).
  { cbn [evq ev]. intros z. destruct (z =? 0).
    - replace (PHI st + extra) with (PHI (set_nsec (a_nsec st - 1) st) + extra) by (rewrite PHI_set_nsec; lia).
      change (GP st) with (GP (set_nsec (a_nsec st - 1) st)).
      apply Hk; [apply LW_set_nsec; exact HL| rewrite PHI_set_nsec; lia| change (GP (set_nsec _ st)) with (GP st); lia].
    - destruct (is_err z); apply evq_aundef. }
  destruct (flush_beg mb <? flush_end mb ms); [| exact UNM].
  cbn [evq]. intros r. destruct (r =? 0); [exact UNM| apply evq_aundef].
Qed.

Definition RPst (gp : Z) (st' : astate) : Prop := LW st' /\ GP st' <= gp.
Definition RPm (n : Z) (gp : Z) (r : astate * option AsanCtrl.aptr) : Prop :=
  LW (fst r) /\ GP (fst r) + (match snd r with Some _ => 0 | None => if is_primary n then 0 else pcost (sec_map_size n) end) <= gp.
Lemma RPst_mono : RPmono RPst. Proof. intros g g' r Hg [H1 H2]. split; [exact H1| lia]. Qed.
Lemma RPm_mono : forall n, RPmono (RPm n). Proof. intros n g g' r Hg [H1 H2]. split; [exact H1| lia]. Qed.

Lemma evq_amalloc : forall RESV st n,
  LW st -> 0 <= n -> emb_sz st + 110 <= EMB_MAX - 4096 ->
  evq (RPm n) (GP st + (if is_primary n then 0 else pcost (sec_map_size n))) (PHI st + (if is_primary n then EXB else sec_map_size n))
      (amalloc ATOP RESV st n).
Proof.
  intros RESV st n HL Hn Hsz. unfold amalloc. cbv zeta. pose proof (GP_nonneg st (LW_emb st HL)) as G0.
  destruct (_ || _) eqn:E0.
  { unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL|]. destruct (is_primary n); lia. }
  apply Bool.orb_false_iff in E0 as [E0a E0b]. apply Z.ltb_ge in E0a. apply Z.ltb_ge in E0b.

  assert (FIN : forall st1 ch gp b, LW st1 -> GP st1 <= gp -> chunk_cls_ok ch ->
            evq (RPm n) gp b
              (match ch with
               | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))
               | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7)) (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1)))
               end)).
  { intros st1 ch gp b HL1 HG1 Hch.
    assert (POST : RPm n gp (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))).
    { unfold RPm. cbn [fst snd]. split; [apply LW_set_next, LW_live_insert; assumption|].
      change (GP (set_next _ (set_live _ st1))) with (GP st1). lia. }
    destruct ch as [c0 n0|mb ms n0]; [exact POST| unfold poison0; exact POST]. }
  destruct (is_primary n) eqn:EP.
  - pose proof (primary_class_facts n Hn EP) as (C1 & _).
    replace (PHI st + EXB) with (PHI st + 0 + EXB) by lia.
    apply evq_cache_alloc_x; [apply RPm_mono| lia| exact HL| lia| exact Hsz| lia|].
    intros st1 ok HL1 HP1 HG1. destruct ok.
    + apply (FIN st1 (CPrim (class_id (needed_size n)) n)); [exact HL1| lia| cbn; lia].
    + unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL1|]. rewrite EP. lia.
  - pose proof (not_primary_large n Hn EP) as NL.
    replace (GP st + pcost (sec_map_size n)) with (GP st + 0 + pcost (sec_map_size n)) by lia.
    apply evq_large_alloc; [apply RPm_mono| lia| exact HL| lia| |].
    + intros st1 ch HL1 HP1 HG1 Hch. apply (FIN st1 ch); [exact HL1| lia| exact Hch].
    + intros st1 HL1 HP1 HG1. unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL1|]. rewrite EP. lia.
Qed.

Lemma evq_aaligned16x : forall RESV st n,
  LW st -> 16 <= n <= ALIGNED_NMAX -> n mod 16 = 0 -> emb_sz st + 110 <= EMB_MAX - 4096 ->
  evq (RPm n) (GP st + 0) (PHI st + EXB) (aaligned16x ATOP RESV st n).
Proof.
  intros RESV st n HL Hn Hm Hsz. unfold aaligned16x. cbv zeta. pose proof (GP_nonneg st (LW_emb st HL)) as G0.
  pose proof (al16_facts n Hn Hm) as F. cbv zeta in F. destruct F as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & EP).
  replace (PHI st + EXB) with (PHI st + 0 + EXB) by lia.
  apply evq_cache_alloc_x; [apply RPm_mono| lia| exact HL| lia| exact Hsz| lia|].
  intros st1 ok HL1 HP1 HG1. destruct ok.
  - unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [apply LW_set_next, LW_live_insert; [exact HL1| cbn; lia]|].
    change (GP (set_next _ (set_live _ st1))) with (GP st1). lia.
  - unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL1|]. rewrite EP. lia.
Qed.

Lemma evq_recycle_chunk : forall {R} RP gx st ch (k : astate -> AM R) extra,
  LW st -> chunk_cls_ok ch -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (recycle_chunk st ch k).
Proof.
  intros R RP gx st ch k extra HL Hch Hex Hk. destruct ch as [c n|mb ms n]; cbn [recycle_chunk].
  - apply evq_cache_dealloc; auto.
  - apply evq_large_dealloc; auto.
Qed.

Lemma evq_recycle_chunks : forall {R} RP gx l st (k : astate -> AM R) extra,
  LW st -> Forall chunk_cls_ok l -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (recycle_chunks st l k).
Proof.
  intros R RP gx l. induction l as [|ch l IH]; intros st k extra HL HF Hex Hk; cbn [recycle_chunks].
  - apply Hk; [exact HL| lia| lia].
  - apply Forall_cons_iff in HF as [Hch HF]. apply evq_recycle_chunk; auto.
    intros st1 HL1 HP1 HG1. apply IH; auto. intros st2 HL2 HP2 HG2. apply Hk; [exact HL2| lia| lia].
Qed.

Lemma batch_K : 1 <= K_BATCH_CLASS <= 31. Proof. unfold K_BATCH_CLASS. lia. Qed.

Lemma evq_do_recycle : forall {R} RP gx bs st (k : astate -> AM R) extra,
  LW st -> Forall chunk_cls_ok (qchunks bs) -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (do_recycle st bs k).
Proof.
  intros R RP gx bs. induction bs as [|b bs IH]; intros st k extra HL HF Hex Hk; cbn [do_recycle].
  - apply Hk; [exact HL| lia| lia].
  - rewrite qchunks_cons in HF. apply Forall_app in HF as [Hb HF].
    apply evq_recycle_chunks; auto. { apply Forall_rev. exact Hb. }
    intros st1 HL1 HP1 HG1. apply evq_cache_dealloc; auto; [apply batch_K|].
    intros st2 HL2 HP2 HG2. apply IH; auto. intros st3 HL3 HP3 HG3.
    apply Hk; [exact HL3| lia| lia].
Qed.

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

Lemma evq_recycle : forall {R} RP gx st mn (k : astate -> AM R) extra,
  LW st -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (recycle st mn k).
Proof.
  intros R RP gx st mn k extra HL Hex Hk. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  unfold recycle. cbv zeta.
  destruct (_ <? _); [apply evq_aundef|].
  assert (TAIL : forall gl extracted exb, incl (qchunks (gl ++ extracted)) (qchunks (a_qglob st)) ->
    evq RP (GP st + gx) (PHI st + extra)
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
  assert (HL1 : LW (set_qglob rest bytes2 st)).
  { apply (LW_chunks st); try reflexivity; [exact HL|]. apply QOK_parts. cbn [a_qloc a_qglob set_qglob]. split; [exact Q1|]. split; [exact Q2|].
    eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. right. exact Hin. }
  change (PHI st) with (PHI (set_qglob rest bytes2 st)). change (GP st) with (GP (set_qglob rest bytes2 st)).
  apply evq_do_recycle; [exact HL1| | exact Hex|].
  { eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. left. exact Hin. }
  intros st1 HL2 HP1 HG1. apply Hk; [exact HL2| exact HP1| exact HG1].
Qed.

Lemma evq_drain : forall {R} RP gx st (k : astate -> AM R) extra,
  LW st -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (drain st k).
Proof.
  intros R RP gx st k extra HL Hex Hk. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  unfold drain. cbv zeta. set (st1 := set_qglob _ _ (set_qloc [] 0 st)).
  assert (HL1 : LW st1).
  { apply (LW_chunks st); try reflexivity; [exact HL|]. apply QOK_parts. cbn. split; [exact Q1|]. split; [constructor|]. rewrite qchunks_app. apply Forall_app. auto. }
  change (PHI st) with (PHI st1). change (GP st) with (GP st1).
  destruct (Q_MAX <? _).
  - apply evq_recycle; [exact HL1| exact Hex|]. intros st2 HL2 HP2 HG2. apply Hk; [exact HL2| exact HP2| exact HG2].
  - apply Hk; [exact HL1| apply Z.le_refl| apply Z.le_refl].
Qed.

Lemma qchunks_rev_snoc : forall P rl b,
  Forall P (qchunks (rev (b :: rl))) <-> Forall P (qchunks (rev rl)) /\ Forall P (b_chunks b).
Proof. intros P rl b. cbn [rev]. rewrite qchunks_app, Forall_app, qchunks_cons. cbn. rewrite app_nil_r. tauto. Qed.

Lemma evq_enqueue : forall {R} RP gx st ch (k : astate -> AM R) extra,
  RPmono RP -> LW st -> chunk_cls_ok ch -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (enqueue st ch k).
Proof.
  intros R RP gx st ch k extra HM HL Hch Hex Hk. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  unfold enqueue. cbv zeta.
  assert (NEW : evq RP (GP st + gx) (PHI st + extra)
      (cache_alloc st K_BATCH_CLASS (fun st1 ok => if negb ok then aundef_ USpin (k st1)
         else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1)))).
  { replace (PHI st + extra) with (PHI st + extra + 0) by lia.
    apply evq_cache_alloc; [exact HM| exact HL| apply batch_K| exact Hex|]. intros st1 ok HL1 HP1 HG1. destruct ok; cbn [negb]; [|apply evq_aundef].
    set (st2 := set_qloc _ _ st1).
    assert (HL2 : LW st2).
    { apply (LW_chunks st1); try reflexivity; [exact HL1|]. pose proof (proj1 (QOK_parts st1) (LW_qok st1 HL1)) as (R1 & R2 & R3).
      apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live st2]. split; [exact R1|]. split; [| exact R3].
      rewrite qchunks_app, Forall_app. split; [exact R2|]. rewrite qchunks_cons. cbn. constructor; [exact Hch| constructor]. }
    change (PHI st1) with (PHI st2). change (GP st1) with (GP st2).
    apply Hk; [exact HL2| exact HP1| exact HG1]. }
  destruct (rev (a_qloc st)) as [|b rl] eqn:ER.
  - exact NEW.
  - destruct (b_count b =? Q_BATCH). { exact NEW. }
    set (st2 := set_qloc _ _ st).
    assert (HL2 : LW st2).
    { apply (LW_chunks st); try reflexivity; [exact HL|]. apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live st2]. split; [exact Q1|]. split; [| exact Q3].
      assert (E : a_qloc st = rev (b :: rl)) by (rewrite <- ER, rev_involutive; reflexivity).
      rewrite E in Q2. apply qchunks_rev_snoc in Q2 as [Q2a Q2b]. apply qchunks_rev_snoc. split; [exact Q2a|]. cbn. constructor; assumption. }
    change (PHI st) with (PHI st2). change (GP st) with (GP st2).
    apply Hk; [exact HL2| apply Z.le_refl| apply Z.le_refl].
Qed.

Lemma evq_afree : forall st id,
  LW st -> evq RPst (GP st + 0) (PHI st + 0) (afree st (Some id)).
Proof.
  intros st id HL. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3). unfold afree.
  destruct ((a_live st) !! id) as [ch|] eqn:Hl; [|apply evq_aundef]. cbv zeta.
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  pose proof (Permutation_Forall HPl Q1) as Q1'. apply Forall_cons_iff in Q1' as [Hch _].
  set (st1 := set_live (delete id (a_live st)) st).
  assert (HL1 : LW st1) by (apply LW_live_delete; exact HL).
  assert (AFTER : forall st2, LW st2 -> PHI st2 <= PHI st -> GP st2 <= GP st ->
    evq RPst (GP st2 + 0) (PHI st2 + 0) (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)).
  { intros st2 HL2 HP2 HG2. destruct (Q_CACHE <? _).
    - apply evq_drain; [exact HL2| lia|]. intros st3 HL3 HP3 HG3. unfold aret. cbn [evq]. split; [exact HL3| lia].
    - unfold aret. cbn [evq]. split; [exact HL2| lia]. }
  change (PHI st) with (PHI st1). change (GP st) with (GP st1). destruct (chunk_size ch <=? Q_MAX).
  - apply evq_enqueue; [apply RPst_mono| exact HL1| exact Hch| lia|]. intros st2 HL2 HP2 HG2. apply AFTER; [exact HL2| exact HP2| exact HG2].
  - apply evq_recycle_chunk; [exact HL1| exact Hch| lia|]. intros st2 HL2 HP2 HG2. apply AFTER; [exact HL2| exact HP2| exact HG2].
Qed.
End Ev.
End CANSEC1.

Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrlProps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanTotal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanFree.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition pcost (len : Z) : Z := len / 4096 + len / 32768 + 4.
Lemma pcost_nonneg : forall l, 0 <= l -> 0 <= pcost l.
Proof. intros. unfold pcost. pose proof (Z.div_pos l 4096). pose proof (Z.div_pos l 32768). lia. Qed.
Lemma pcost_mono : forall a b, a <= b -> pcost a <= pcost b.
Proof. intros a b H. unfold pcost. pose proof (Z.div_le_mono a b 4096 ltac:(lia) H). pose proof (Z.div_le_mono a b 32768 ltac:(lia) H). lia. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Ev.
Variables (SB PA : Z).

Definition inAP (a n : Z) : Prop :=
  (SB <= a /\ a + n <= SB + K_SPACE_SIZE) \/ (PA <= a /\ a + n <= PA + K_PTRARR_RESERVE).

Fixpoint evq {R} (RP : Z -> R -> Prop) (gp b : Z) (t : AM R) {struct t} : Prop :=
  match t with
  | SRet r => RP gp r
  | SVis e k =>
    match e with
    | AUndef _ => True
    | AMmap a len prot flags =>
        prot = PROT_RW /\ 0 < len /\ len mod 4096 = 0 /\
        ((flags = F_ANON /\ a = 0 /\ pcost len <= gp /\ len <= b /\ forall z, evq RP (gp - pcost len) (b - len) (k z))
         \/ (flags = F_FIXED /\ inAP a len /\ len <= b /\ forall z, evq RP gp (if is_err z then b else b - len) (k z)))
    | AMmapT len =>
        0 < len /\ len mod 4096 = 0 /\ pcost len <= gp /\ len <= b /\
        forall z, evq RP (if is_err z then gp else gp - pcost len) (if is_err z then b else b - len) (k z)
    | AMunmap a len => forall z, evq RP gp b (k z)
    | AMadvise a len => forall z, evq RP gp b (k z)
    | _ => False
    end
  end.

Lemma evq_mono : forall {R} (RP RP' : Z -> R -> Prop) (t : AM R) gp gp' b b',
  evq RP gp b t -> gp <= gp' -> b <= b' ->
  (forall g g' r, g <= g' -> RP g r -> RP' g' r) ->
  evq RP' gp' b' t.
Proof.
  intros R RP RP' t. induction t as [r|e k IH]; intros gp gp' b b' H Hg Hb HRP; cbn in H |- *.
  - eapply HRP; [exact Hg| exact H].
  - destruct e as [t0|b0|a len prot flags|a len|a l p|a len|len|w]; try exact H; try exact I.
    + destruct H as (Hp & Hl & Hm & H). split; [exact Hp|]. split; [exact Hl|]. split; [exact Hm|].
      destruct H as [(Hf & Ha & Hpc & Hlb & H)|(Hf & Hin & Hlb & H)].
      * left. split; [exact Hf|]. split; [exact Ha|]. split; [lia|]. split; [lia|].
        intros z. eapply IH; [exact (H z)| lia| lia| exact HRP].
      * right. split; [exact Hf|]. split; [exact Hin|]. split; [lia|]. intros z. eapply IH; [exact (H z)| exact Hg| destruct (is_err z); lia| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact Hg| exact Hb| exact HRP].
    + intros z. eapply IH; [exact (H z)| exact Hg| exact Hb| exact HRP].
    + destruct H as (Hl & Hm & Hpc & Hlb & H). split; [exact Hl|]. split; [exact Hm|]. split; [lia|]. split; [lia|].
      intros z. eapply IH; [exact (H z)| destruct (is_err z); lia| destruct (is_err z); lia| exact HRP].
Qed.

Definition RPmono {R} (RP : Z -> R -> Prop) : Prop := forall g g' r, g <= g' -> RP g r -> RP g' r.

Lemma evq_mono_b : forall {R} (RP : Z -> R -> Prop) (t : AM R) gp gp' b b',
  RPmono RP -> evq RP gp b t -> gp <= gp' -> b <= b' -> evq RP gp' b' t.
Proof. intros R RP t gp gp' b b' HM H Hg Hb. eapply evq_mono; eauto. Qed.

Lemma evq_aundef : forall {R} RP gp b w (k : AM R), evq RP gp b (aundef_ w k).
Proof. intros. cbn. exact I. Qed.

Definition CBM : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + K_PTRARR_RESERVE.

Definition emb_cap (st : astate) : Z := snd (fst (a_emb st)).
Definition cls_lw (r : aclass) : Prop :=
  0 <= c_mapped_user r <= K_FREEARR_OFF /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0.
Definition emb_lw (st : astate) : Prop := 0 <= emb_cap st <= EMB_MAX /\ emb_cap st mod 4096 = 0 /\ 0 <= emb_sz st.

Definition chunk_cls_ok (ch : achunk) : Prop := match ch with CPrim c _ => 1 <= c <= 31 | CSec _ _ _ => True end.
Definition QOK (st : astate) : Prop := Forall chunk_cls_ok (all_chunks [] [] st).
Definition LW (st : astate) : Prop :=
  a_space_beg st = SB /\ a_ptr_array st = PA /\ 0 <= a_nres st /\ 8 * a_nres st <= K_PTRARR_RESERVE
  /\ (forall c, 1 <= c <= 31 -> cls_lw (get_cls st c)) /\ emb_lw st /\ QOK st.

Definition PHI (st : astate) : Z := CBM - commit_bytes st.

Definition PEMB : Z := pcost EMB_MAX.
Definition GP (st : astate) : Z := PEMB * ((EMB_MAX - emb_cap st) / 4096).

Definition EXB : Z := 4 * EMB_MAX.

Lemma PEMB_pos : 0 < PEMB. Proof. reflexivity. Qed.
Lemma GP_nonneg : forall st, emb_lw st -> 0 <= GP st.
Proof. intros st (H1 & _). unfold GP. pose proof PEMB_pos. pose proof (Z.div_pos (EMB_MAX - emb_cap st) 4096 ltac:(lia) ltac:(lia)). nia. Qed.

Lemma commit_bytes_LW : forall st, LW st -> 0 <= commit_bytes st <= CBM.
Proof.
  intros st (_ & _ & N0 & N1 & HC & _). unfold commit_bytes, CBM.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX) ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  pose proof (csum_nonneg cls_mapped_bytes' st ltac:(intros c Hc; destruct (HC c Hc) as (?&?&?&?); unfold cls_mapped_bytes'; lia)).
  lia.
Qed.
Lemma PHI_nonneg : forall st, LW st -> 0 <= PHI st.
Proof. intros st H. pose proof (commit_bytes_LW st H). unfold PHI. lia. Qed.

Lemma LW_put : forall st c r, LW st -> 1 <= c <= 31 -> cls_lw r -> LW (put_cls c r st).
Proof.
  intros st c r (S1 & S2 & N0 & N1 & HC & HE) Hc Hr. unfold LW. cbn [a_space_beg a_ptr_array a_nres put_cls set_cls].
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|]. split; [| exact HE].
  intros c' Hc'. destruct (Z.eq_dec c c') as [<-|NE].
  - rewrite get_put_eq. exact Hr.
  - rewrite get_put_ne by exact NE. apply HC. exact Hc'.
Qed.
Lemma LW_cls : forall st c, LW st -> 1 <= c <= 31 -> cls_lw (get_cls st c).
Proof. intros st c (_ & _ & _ & _ & HC & _) Hc. apply HC. exact Hc. Qed.
Lemma LW_emb : forall st, LW st -> emb_lw st.
Proof. intros st (_ & _ & _ & _ & _ & HE & _). exact HE. Qed.
Lemma LW_qok : forall st, LW st -> QOK st.
Proof. intros st (_ & _ & _ & _ & _ & _ & HQ). exact HQ. Qed.
Lemma QOK_parts : forall st, QOK st <-> Forall chunk_cls_ok (live_chunks st) /\ Forall chunk_cls_ok (qchunks (a_qloc st)) /\ Forall chunk_cls_ok (qchunks (a_qglob st)).
Proof. intros st. unfold QOK, all_chunks, qbatches. cbn [app]. rewrite qchunks_app, !Forall_app. tauto. Qed.

Lemma LW_chunks : forall st st', LW st ->
  a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> a_nres st' = a_nres st -> a_cls st' = a_cls st -> a_emb st' = a_emb st ->
  QOK st' -> LW st'.
Proof.
  intros st st' (S1 & S2 & N0 & N1 & HC & HE & _) E1 E2 E3 E4 E5 HQ. unfold LW. rewrite E1, E2, E3.
  split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|]. split; [| split; [| exact HQ]].
  - intros c Hc. unfold get_cls. rewrite E4. apply HC. exact Hc.
  - unfold emb_lw, emb_cap, emb_sz in *. rewrite E5. exact HE.
Qed.
Lemma LW_init_cache : forall st, LW st -> LW (init_cache st).
Proof. intros st H. unfold init_cache. destruct (a_cinit st); [exact H|]. exact H. Qed.
Lemma LW_set_nsec : forall v st, LW st -> LW (set_nsec v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_next : forall v st, LW st -> LW (set_next v st). Proof. intros v st H. exact H. Qed.
Lemma LW_set_exh : forall v st, LW st -> LW (set_exh v st). Proof. intros v st H. exact H. Qed.
Lemma LW_exh_clear : forall c st, LW st -> LW (exh_clear c st). Proof. intros c st H. exact H. Qed.
Lemma LW_exh_set : forall c st, LW st -> LW (exh_set c st). Proof. intros c st H. exact H. Qed.

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
Lemma PHI_set_exh : forall v st, PHI (set_exh v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_emb : forall v st, PHI (set_emb v st) = PHI st. Proof. reflexivity. Qed.
Lemma PHI_set_nres : forall v st, PHI (set_nres v st) = PHI st - 8 * (v - a_nres st).
Proof. intros. unfold PHI, commit_bytes. cbn [a_nres set_nres]. unfold csum. rewrite (fold_csum_ext cls_mapped_bytes' st (set_nres v st)) by (intros; reflexivity). lia. Qed.

Lemma GP_put : forall st c r, GP (put_cls c r st) = GP st. Proof. reflexivity. Qed.
Lemma GP_init_cache : forall st, GP (init_cache st) = GP st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma GP_same_but : forall c st st', same_but c st st' -> GP st' = GP st.
Proof. intros c st st' (_&_&_&_&_&_&_&_&_&_&_&_&HE). unfold GP, emb_cap. rewrite HE. reflexivity. Qed.

Lemma mod_sub_mult : forall x y m, 0 < m -> x mod m = 0 -> y mod m = 0 -> (x - y) mod m = 0.
Proof. intros x y m Hm Hx Hy. rewrite Zminus_mod, Hx, Hy. reflexivity. Qed.

Lemma live_chunks_insert_Forall : forall (P : achunk -> Prop) st id ch,
  P ch -> Forall P (live_chunks st) -> Forall P (live_chunks (set_live (<[id := ch]> (a_live st)) st)).
Proof.
  intros P st id ch Hch H. unfold live_chunks in *. cbn [a_live set_live]. rewrite Forall_forall in *.
  intros x Hx. apply in_map_iff in Hx as ([k v] & <- & Hin). cbn [snd].
  apply list_elem_of_In, elem_of_map_to_list in Hin. apply lookup_insert_Some in Hin as [[_ <-]|[_ Hl]]; [exact Hch|].
  apply H. apply in_map_iff. exists (k, v). split; [reflexivity|]. apply list_elem_of_In, elem_of_map_to_list. exact Hl.
Qed.
Lemma live_chunks_delete_Forall : forall (P : achunk -> Prop) st id,
  Forall P (live_chunks st) -> Forall P (live_chunks (set_live (delete id (a_live st)) st)).
Proof.
  intros P st id H. unfold live_chunks in *. cbn [a_live set_live]. rewrite Forall_forall in *.
  intros x Hx. apply in_map_iff in Hx as ([k v] & <- & Hin). cbn [snd].
  apply list_elem_of_In, elem_of_map_to_list in Hin. apply lookup_delete_Some in Hin as [_ Hl].
  apply H. apply in_map_iff. exists (k, v). split; [reflexivity|]. apply list_elem_of_In, elem_of_map_to_list. exact Hl.
Qed.
Lemma LW_live_insert : forall st id ch, LW st -> chunk_cls_ok ch -> LW (set_live (<[id := ch]> (a_live st)) st).
Proof.
  intros st id ch HL Hch. apply (LW_chunks st); try reflexivity; [exact HL|]. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  apply QOK_parts. cbn [a_qloc a_qglob set_live]. split; [apply live_chunks_insert_Forall; assumption| split; assumption].
Qed.
Lemma LW_live_delete : forall st id, LW st -> LW (set_live (delete id (a_live st)) st).
Proof.
  intros st id HL. apply (LW_chunks st); try reflexivity; [exact HL|]. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  apply QOK_parts. cbn [a_qloc a_qglob set_live]. split; [apply live_chunks_delete_Forall; assumption| split; assumption].
Qed.

Lemma region_in_arena : forall st c x y, LW st -> 1 <= c <= 31 -> 0 <= x -> 0 <= y -> x + y <= K_REGION ->
  inAP (region_beg st c + x) y.
Proof.
  intros st c x y (S1 & _) Hc Hx Hy Hxy. left. unfold region_beg. rewrite S1. unfold K_REGION, K_SPACE_SIZE in *. nia.
Qed.

Lemma evq_ensure_free_array : forall {R} RP gx st c nf (k : astate -> bool -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + extra) (ensure_free_array st c nf k).
Proof.
  intros R RP gx st c nf k extra HL Hc Hex Hk. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  unfold ensure_free_array.
  destruct (nf * 4 <=? _) eqn:E1. { apply (Hk st true HL); lia. }
  destruct (K_FREEARR_MAX <? _) eqn:E2. { apply evq_aundef. }
  apply Z.leb_gt in E1. apply Z.ltb_ge in E2. assert (Hnf : 0 <= nf) by lia.
  pose proof (rup_freearr_bounds (nf * 4) ltac:(lia)) as RB.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RM.
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as RG.
  set (nm := rup (nf * 4) K_FREEARR_MAP) in *.
  assert (D : (4096 | K_FREEARR_MAP)) by (exists 64; reflexivity).
  cbn -[evq Z.sub Z.add Z.mul rup region_beg K_FREEARR_OFF nm get_cls put_cls cls_set_mapped_free_array fixed_answer_ok is_err PHI GP].
  split; [reflexivity|]. split; [lia|]. split.
  { assert (M1 : nm mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod nm K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact RM]).
    assert (M2 : c_mapped_free_array (get_cls st c) mod 4096 = 0) by (apply Znumtheory.Zdivide_mod; apply (div4096_of_mod _ K_FREEARR_MAP); [exact D| unfold K_FREEARR_MAP; lia| exact F2]).
    apply mod_sub_mult; [lia| exact M1| exact M2]. }
  right. split; [reflexivity|]. split.
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
  - apply (Hk st false HL); lia.
  - replace (PHI st + extra - (nm - c_mapped_free_array (get_cls st c))) with (PHI (put_cls c r' st) + extra) by lia.
    rewrite <- (GP_put st c r'). apply Hk; [exact HL'| lia| rewrite GP_put; lia].
Qed.

Lemma evq_populate_g : forall {R} RP gx (exh : astate -> (astate -> AM R) -> AM R) (clr : astate -> astate) st c req (k : astate -> bool -> AM R) bx EX,
  (forall s, clr s = s \/ clr s = exh_clear c s) ->
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= bx -> 0 <= EX ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + bx + EX) (exh st (fun st' => k st' false)) ->
  evq RP (GP st + gx) (PHI st + bx + EX) (populate_free_array_g exh clr st c req k).
Proof.
  intros R RP gx exh clr st c req k bx EX Hclr HM HL Hc Hbx HEX Hk0 HEXH. pose proof (LW_cls st c HL Hc) as (U1 & U2 & F1 & F2).
  replace (PHI st + bx + EX) with (PHI st + (bx + EX)) in * by lia. set (extra := bx + EX) in *. assert (Hex : 0 <= extra) by (unfold extra; lia).
  assert (Hk : forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)).
  { intros st' ok H1 H2 H3. eapply evq_mono_b; [exact HM| apply Hk0; eauto| lia| unfold extra; lia]. }
  unfold populate_free_array_g. cbv zeta.

  assert (AFTER : forall st1, LW st1 -> PHI st1 <= PHI st -> GP st1 <= GP st ->
    evq RP (GP st1 + gx) (PHI st1 + extra)
      (ensure_free_array st1 c (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c)
         (fun st2 ok => if negb ok then k st2 false else
            k (clr (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c * size_of_class c)
                            (cls_set_num_freed (c_num_freed (get_cls st1 c) + (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size_of_class c) (get_cls st2 c))) st2)) true))).
  { intros st1 HL1 HP1 HG1. apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HP2 HG2. destruct ok; cbn [negb].
    - set (r3 := cls_set_allocated_user _ (cls_set_num_freed _ (get_cls st2 c))).
      assert (Hr3 : cls_lw r3) by (pose proof (LW_cls st2 c HL2 Hc) as X; unfold r3, cls_lw in *; cbn; exact X).
      assert (EP0 : PHI (put_cls c r3 st2) = PHI st2) by (rewrite PHI_put by exact Hc; unfold r3, cls_mapped_bytes'; cbn; lia).
      destruct (Hclr (put_cls c r3 st2)) as [EC|EC]; rewrite EC.
      + rewrite <- EP0. change (GP st2) with (GP (put_cls c r3 st2)). apply Hk; [apply LW_put; auto| lia| rewrite GP_put; lia].
      + assert (EP3 : PHI (exh_clear c (put_cls c r3 st2)) = PHI st2) by (change (PHI (exh_clear c (put_cls c r3 st2))) with (PHI (put_cls c r3 st2)); exact EP0).
        assert (EG3 : GP (exh_clear c (put_cls c r3 st2)) = GP st2) by reflexivity.
        rewrite <- EP3, <- EG3.
        apply Hk; [apply LW_exh_clear, LW_put; auto| lia| lia].
    - apply Hk; [exact HL2| lia| lia]. }
  destruct (_ <=? c_mapped_user (get_cls st c)) eqn:E1. { apply AFTER; [exact HL| lia| lia]. }
  apply Z.leb_gt in E1.
  set (ums := rup _ K_USER_MAP).
  destruct (K_FREEARR_OFF <? _) eqn:E2. { exact HEXH. }
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
        fixed_answer_ok is_err PHI GP ensure_free_array size_of_class exh_clear].
  split; [reflexivity|]. split; [lia|]. split.
  { apply Znumtheory.Zdivide_mod. apply (div4096_of_mod ums K_USER_MAP); [exact D| unfold K_USER_MAP; lia| exact RM]. }
  right. split; [reflexivity|]. split.
  { apply (region_in_arena st c); auto; try lia. unfold K_FREEARR_OFF, K_REGION in *. lia. }
  split; [lia|].
  intros z. destruct (negb (fixed_answer_ok _ z)); [apply evq_aundef|]. destruct (is_err z).
  - apply (Hk st false HL); lia.
  - replace (PHI st + extra - ums) with (PHI (put_cls c r' st) + extra) by lia.
    rewrite <- (GP_put st c r'). apply AFTER; [exact HL'| lia| rewrite GP_put; lia].
Qed.

Lemma evq_populate : forall {R} RP gx st c req (k : astate -> bool -> AM R) extra,
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + extra + 0) (populate_free_array st c req k).
Proof. intros. unfold populate_free_array. apply evq_populate_g; auto; [lia| apply evq_aundef]. Qed.

Lemma evq_cache_alloc_g : forall {R} RP gx (pop : astate -> Z -> Z -> (astate -> bool -> AM R) -> AM R) st c (k : astate -> bool -> AM R) bx EX,
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= bx -> 0 <= EX ->
  (forall req kk,
     (forall st' ok, LW st' -> PHI st' <= PHI (init_cache st) -> GP st' <= GP (init_cache st) -> evq RP (GP st' + gx) (PHI st' + bx) (kk st' ok)) ->
     evq RP (GP (init_cache st) + gx) (PHI (init_cache st) + bx + EX) (pop (init_cache st) c req kk)) ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + bx + EX) (cache_alloc_g pop st c k).
Proof.
  intros R RP gx pop st c k bx EX HM HL Hc Hbx HEX HPOP Hk0.
  assert (Hk : forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx + EX) (k st' ok)).
  { intros st' ok H1 H2 H3. eapply evq_mono_b; [exact HM| apply Hk0; eauto| lia| lia]. }
  unfold cache_alloc_g. cbv zeta.
  destruct (0 <? _).
  { set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st c HL Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' st) = PHI st) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    rewrite <- EP, <- (GP_put st c r'). apply Hk; [apply LW_put; auto| lia| rewrite GP_put; lia]. }
  pose proof (LW_init_cache st HL) as HL1.
  assert (TAKE : forall st2, LW st2 -> PHI st2 <= PHI st -> GP st2 <= GP st ->
    evq RP (GP st2 + gx) (PHI st2 + bx)
      (if c_num_freed (get_cls st2 c) <? max_count (init_cache st) c / 2 then aundef_ (UCheck 229) (k st2 false)
       else k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)).
  { intros st2 HL2 HP2 HG2. destruct (_ <? _); [apply evq_aundef|].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' st2) = PHI st2) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    rewrite <- EP, <- (GP_put st2 c r'). apply Hk0; [apply LW_put; auto| lia| rewrite GP_put; lia]. }
  destruct (_ <=? _).
  - apply (evq_mono_b RP _ (GP (init_cache st) + gx) (GP st + gx) (PHI (init_cache st) + bx) (PHI st + bx + EX) HM).
    + apply TAKE; [exact HL1| rewrite PHI_init_cache; lia| rewrite GP_init_cache; lia].
    + rewrite GP_init_cache. lia.
    + rewrite PHI_init_cache. lia.
  - rewrite <- (PHI_init_cache st), <- (GP_init_cache st). apply HPOP.
    intros st2 ok HL2 HP2 HG2. rewrite PHI_init_cache in HP2. rewrite GP_init_cache in HG2. destruct ok.
    + apply TAKE; [exact HL2| exact HP2| exact HG2].
    + apply Hk0; [exact HL2| exact HP2| exact HG2].
Qed.

Lemma evq_cache_alloc : forall {R} RP gx st c (k : astate -> bool -> AM R) extra,
  RPmono RP -> LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + extra + 0) (cache_alloc st c k).
Proof.
  intros R RP gx st c k extra HM HL Hc Hex Hk. unfold cache_alloc. apply evq_cache_alloc_g; auto; [lia|].
  intros req kk Hkk. apply evq_populate; auto. apply LW_init_cache. exact HL.
Qed.

Lemma evq_cache_dealloc : forall {R} RP gx st c (k : astate -> AM R) extra,
  LW st -> 1 <= c <= 31 -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (cache_dealloc st c k).
Proof.
  intros R RP gx st c k extra HL Hc Hex Hk. unfold cache_dealloc. cbv zeta.
  pose proof (LW_init_cache st HL) as HL1.
  destruct (_ =? _).
  - rewrite <- (PHI_init_cache st), <- (GP_init_cache st). apply evq_ensure_free_array; auto.
    intros st2 ok HL2 HP2 HG2. rewrite PHI_init_cache in HP2. rewrite GP_init_cache in HG2. destruct ok; cbn [negb]; [|apply evq_aundef].
    set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls st2 c HL2 Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' st2) = PHI st2) by (rewrite PHI_put by exact Hc; unfold r', cls_mapped_bytes'; cbn; lia).
    rewrite <- EP, <- (GP_put st2 c r'). apply Hk; [apply LW_put; auto| lia| rewrite GP_put; lia].
  - set (r' := cls_set_count _ _). assert (Hr' : cls_lw r') by (pose proof (LW_cls (init_cache st) c HL1 Hc) as X; exact X).
    assert (EP : PHI (put_cls c r' (init_cache st)) = PHI st).
    { rewrite PHI_put by exact Hc. rewrite PHI_init_cache. unfold r', cls_mapped_bytes'; cbn. lia. }
    assert (EG : GP (put_cls c r' (init_cache st)) = GP st) by (rewrite GP_put; apply GP_init_cache).
    rewrite <- EP, <- EG. apply Hk; [apply LW_put; auto| lia| lia].
Qed.

Lemma a_emb_eta : forall st, a_emb st = (fst (fst (a_emb st)), emb_cap st, emb_sz st).
Proof. intros st. unfold emb_cap, emb_sz. destruct (a_emb st) as [[d cap] sz]. reflexivity. Qed.

Lemma rup_PG_mod : forall x, rup x PG mod 4096 = 0.
Proof. intros. apply (rup_mod x PG). unfold PG. lia. Qed.

Lemma evq_emb_realloc : forall {R} RP gx RESV st want (k : astate -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> emb_cap st < want -> want <= EMB_MAX - 4095 -> 0 <= bx ->
  (forall st', LW st' -> PHI st' = PHI st -> GP st' + PEMB <= GP st -> emb_sz st' = emb_sz st -> want <= emb_cap st' ->
      evq RP (GP st' + gx) (PHI st' + bx) (k st')) ->
  evq RP (GP st + gx) (PHI st + bx + EMB_MAX) (emb_realloc ATOP RESV st want k).
Proof.
  intros R RP gx RESV st want k bx HM Hgx HL Hw Hwm Hbx Hk. pose proof (LW_emb st HL) as (C1 & C2 & C3).
  unfold emb_realloc. rewrite (a_emb_eta st). cbv zeta.
  pose proof (rup_ge want PG ltac:(unfold PG; lia)) as RG. pose proof (rup_le want PG ltac:(unfold PG; lia)) as RL. pose proof (rup_PG_mod want) as RM.
  set (ncap := rup want PG) in *. unfold PG in RG, RL.
  assert (NC : emb_cap st + 4096 <= ncap <= EMB_MAX).
  { split; [| lia]. pose proof (Z.div_mod ncap 4096 ltac:(lia)). pose proof (Z.div_mod (emb_cap st) 4096 ltac:(lia)). lia. }
  assert (PC : pcost ncap <= PEMB) by (apply pcost_mono; lia).
  pose proof (PHI_nonneg st HL) as P0.

  assert (NEXT : forall mb, let st1 := set_emb (mb, ncap, emb_sz st) st in
            LW st1 /\ PHI st1 = PHI st /\ GP st1 + PEMB <= GP st /\ emb_sz st1 = emb_sz st /\ want <= emb_cap st1).
  { intros mb st1. split; [| split; [reflexivity| split; [| split; [reflexivity| cbn; lia]]]].
    - destruct HL as (S1 & S2 & N0 & N1 & HC & _ & HQ). unfold LW. split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
      split; [exact HC|]. split; [| exact HQ]. unfold emb_lw. change (emb_cap st1) with ncap. change (emb_sz st1) with (emb_sz st). lia.
    - unfold GP, st1, emb_cap. cbn [a_emb set_emb fst snd]. fold (emb_cap st). pose proof PEMB_pos.
      assert ((EMB_MAX - ncap) / 4096 + 1 <= (EMB_MAX - emb_cap st) / 4096).
      { replace (EMB_MAX - emb_cap st) with ((EMB_MAX - ncap) + (ncap - emb_cap st)) by lia.
        pose proof (Z.div_mod ncap 4096 ltac:(lia)). pose proof (Z.div_mod (emb_cap st) 4096 ltac:(lia)).
        replace (ncap - emb_cap st) with ((ncap / 4096 - emb_cap st / 4096) * 4096) by lia.
        rewrite Z.div_add by lia. lia. }
      nia. }
  cbn -[evq Z.sub Z.add PHI GP mmap_answer_ok avoids_all is_err pcost ncap set_emb EMB_MAX].
  split; [reflexivity|]. split; [lia|]. split; [exact RM|].
  left. split; [reflexivity|]. split; [reflexivity|].
  pose proof (GP_nonneg st (LW_emb st HL)) as G0.
  assert (G1 : PEMB <= GP st) by (destruct (NEXT 0) as (L1 & _ & G1 & _); pose proof (GP_nonneg _ (LW_emb _ L1)); lia).
  split; [lia|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP ncap z)); [apply evq_aundef|]. destruct (is_err z); [apply evq_aundef|].
  destruct (negb (avoids_all z ncap _)); [apply evq_aundef|].
  destruct (NEXT z) as (L1 & P1 & G2 & S1 & W1).
  assert (KK : evq RP (GP st + gx - pcost ncap) (PHI st + bx + EMB_MAX - ncap) (k (set_emb (z, ncap, emb_sz st) st))).
  { eapply evq_mono_b; [exact HM| apply Hk; [exact L1| exact P1| exact G2| exact S1| exact W1]| lia| lia]. }
  destruct (emb_cap st =? 0); [exact KK|].
  cbn -[evq Z.sub Z.add PHI GP is_err pcost ncap set_emb EMB_MAX]. intros r.
  destruct (r =? 0); [exact KK|]. destruct (is_err r); apply evq_aundef.
Qed.

Lemma evq_emb_append : forall {R} RP gx RESV st len (k : astate -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> 0 < len -> emb_sz st + len <= EMB_MAX - 4096 -> 0 <= bx ->
  (forall st', LW st' -> PHI st' = PHI st -> GP st' <= GP st -> emb_sz st' = emb_sz st + len ->
      evq RP (GP st' + gx) (PHI st' + bx) (k st')) ->
  evq RP (GP st + gx) (PHI st + bx + 2 * EMB_MAX) (emb_append ATOP RESV st len k).
Proof.
  intros R RP gx RESV st len k bx HM Hgx HL Hlen Hsz Hbx Hk. pose proof (LW_emb st HL) as (C1 & C2 & C3).
  unfold emb_append.

  assert (SET : forall st1, LW st1 -> LW (emb_set_size (emb_sz st1 + len) st1) /\ PHI (emb_set_size (emb_sz st1 + len) st1) = PHI st1
                 /\ GP (emb_set_size (emb_sz st1 + len) st1) = GP st1 /\ emb_sz (emb_set_size (emb_sz st1 + len) st1) = emb_sz st1 + len).
  { intros st1 HL1. pose proof (LW_emb st1 HL1) as (D1 & D2 & D3). unfold emb_set_size. rewrite (a_emb_eta st1).
    split; [| split; [reflexivity| split; [reflexivity| reflexivity]]].
    destruct HL1 as (S1 & S2 & N0 & N1 & HC & _ & HQ). unfold LW. split; [exact S1|]. split; [exact S2|]. split; [exact N0|]. split; [exact N1|].
    split; [exact HC|]. split; [| exact HQ]. unfold emb_lw, emb_cap, emb_sz. cbn. unfold emb_cap in D1, D2. unfold emb_sz in D3. lia. }

  assert (GO : forall st1, LW st1 -> PHI st1 = PHI st -> GP st1 <= GP st -> emb_sz st1 = emb_sz st ->
            evq RP (GP st1 + gx) (PHI st1 + bx + EMB_MAX)
              (let '(_, cap, sz) := a_emb st1 in
               if cap <? sz + len then emb_realloc ATOP RESV st1 (sz + len) (fun st2 => k (emb_set_size (sz + len) st2))
               else k (emb_set_size (sz + len) st1))).
  { intros st1 HL1 HP1 HG1 HS1. rewrite (a_emb_eta st1).
    destruct (emb_cap st1 <? emb_sz st1 + len) eqn:E.
    - apply Z.ltb_lt in E. apply evq_emb_realloc; [exact HM| exact Hgx| exact HL1| exact E| lia| exact Hbx|].
      intros st2 HL2 HP2 HG2 HS2 _. destruct (SET st2 HL2) as (L3 & P3 & G3 & S3). rewrite HS2 in *.
      rewrite <- P3, <- G3. apply Hk; [exact L3| lia| pose proof PEMB_pos; lia| lia].
    - destruct (SET st1 HL1) as (L3 & P3 & G3 & S3).
      apply (evq_mono_b RP _ (GP (emb_set_size (emb_sz st1 + len) st1) + gx) (GP st1 + gx) (PHI (emb_set_size (emb_sz st1 + len) st1) + bx) (PHI st1 + bx + EMB_MAX) HM).
      + apply Hk; [exact L3| lia| lia| lia].
      + lia.
      + unfold EMB_MAX. lia. }
  rewrite (a_emb_eta st) at 1.
  destruct (emb_cap st =? 0) eqn:E0.
  - apply Z.eqb_eq in E0.
    replace (PHI st + bx + 2 * EMB_MAX) with (PHI st + (bx + EMB_MAX) + EMB_MAX) by lia.
    apply evq_emb_realloc; [exact HM| exact Hgx| exact HL| rewrite E0; reflexivity| unfold EMB_INIT, EMB_MAX; lia| lia|].
    intros st1 HL1 HP1 HG1 HS1 _. replace (PHI st1 + (bx + EMB_MAX)) with (PHI st1 + bx + EMB_MAX) by lia.
    apply GO; [exact HL1| exact HP1| pose proof PEMB_pos; lia| exact HS1].
  - eapply evq_mono_b; [exact HM| apply (GO st HL eq_refl (Z.le_refl _) eq_refl)| lia| unfold EMB_MAX; lia].
Qed.

Lemma ndigits_range : forall z, 1 <= ndigits z <= 5.
Proof. intros z. unfold ndigits. repeat (destruct (_ <? _)); lia. Qed.

Lemma evq_exh_report : forall {R} RP gx RESV c st (k : astate -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> emb_sz st + 110 <= EMB_MAX - 4096 -> 0 <= bx ->
  (forall st', LW st' -> PHI st' = PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st')) ->
  evq RP (GP st + gx) (PHI st + bx + EXB) (exh_report ATOP RESV c st k).
Proof.
  intros R RP gx RESV c st k bx HM Hgx HL Hsz Hbx Hk. unfold exh_report.
  destruct (exh_mem c st).
  { eapply evq_mono_b; [exact HM| apply (Hk st HL eq_refl (Z.le_refl _))| lia| unfold EXB, EMB_MAX; lia]. }
  pose proof (ndigits_range c). pose proof (ndigits_range (size_of_class c)).
  assert (L2 : 0 < exh_len2 c <= 70) by (unfold exh_len2; lia).
  replace (PHI st + bx + EXB) with (PHI (exh_set c st) + (bx + 2 * EMB_MAX) + 2 * EMB_MAX) by (unfold EXB; change (PHI (exh_set c st)) with (PHI st); lia).
  change (GP st) with (GP (exh_set c st)).
  apply evq_emb_append; [exact HM| exact Hgx| apply LW_exh_set; exact HL| unfold EXH_LEN1; lia| change (emb_sz (exh_set c st)) with (emb_sz st); unfold EXH_LEN1; lia| unfold EMB_MAX; lia|].
  intros st1 HL1 HP1 HG1 HS1. change (emb_sz (exh_set c st)) with (emb_sz st) in HS1. change (PHI (exh_set c st)) with (PHI st) in HP1.
  change (GP (exh_set c st)) with (GP st) in HG1.
  replace (PHI st1 + (bx + 2 * EMB_MAX)) with (PHI st1 + bx + 2 * EMB_MAX) by lia.
  apply evq_emb_append; [exact HM| exact Hgx| exact HL1| lia| unfold EXH_LEN1 in HS1; lia| exact Hbx|].
  intros st2 HL2 HP2 HG2 _. apply Hk; [exact HL2| lia| lia].
Qed.

Lemma emb_sz_init_cache : forall st, emb_sz (init_cache st) = emb_sz st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma evq_cache_alloc_x : forall {R} RP gx RESV st c (k : astate -> bool -> AM R) bx,
  RPmono RP -> 0 <= gx -> LW st -> 1 <= c <= 31 -> emb_sz st + 110 <= EMB_MAX - 4096 -> 0 <= bx ->
  (forall st' ok, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + bx) (k st' ok)) ->
  evq RP (GP st + gx) (PHI st + bx + EXB) (cache_alloc_x ATOP RESV st c k).
Proof.
  intros R RP gx RESV st c k bx HM Hgx HL Hc Hsz Hbx Hk. unfold cache_alloc_x.
  assert (EX0 : 0 <= EXB) by (unfold EXB, EMB_MAX; lia).
  apply evq_cache_alloc_g; [exact HM| exact HL| exact Hc| exact Hbx| exact EX0| | exact Hk].
  intros req kk Hkk. pose proof (LW_init_cache st HL) as HL1.
  unfold populate_free_array_x. destruct (c =? K_BATCH_CLASS).
  {
    eapply evq_mono_b; [exact HM| apply (evq_populate RP gx (init_cache st) c req kk bx HM HL1 Hc Hbx Hkk)| lia| lia]. }
  apply evq_populate_g; [intros s; right; reflexivity| exact HM| exact HL1| exact Hc| exact Hbx| exact EX0| exact Hkk|].
  apply evq_exh_report; [exact HM| exact Hgx| exact HL1| rewrite emb_sz_init_cache; exact Hsz| exact Hbx|].
  intros st' HL' HP' HG'. apply Hkk; [exact HL'| lia| exact HG'].
Qed.

Lemma sec_map_size_mod : forall n, sec_map_size n mod 4096 = 0.
Proof. intros. unfold sec_map_size. rewrite Z.add_mod, rup_mod by (unfold PG; lia). reflexivity. Qed.

Lemma evq_large_alloc : forall {R} RP gx RESV st n (k : astate -> option achunk -> AM R),
  RPmono RP -> 0 <= gx -> LW st -> 64512 < n <= 2^40 ->
  (forall st' ch, LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> chunk_cls_ok ch -> evq RP (GP st' + gx) (PHI st' + 0) (k st' (Some ch))) ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx + pcost (sec_map_size n)) (PHI st' + 0) (k st' None)) ->
  evq RP (GP st + gx + pcost (sec_map_size n)) (PHI st + sec_map_size n) (large_alloc ATOP RESV st n k).
Proof.
  intros R RP gx RESV st n k HM Hgx HL Hn HkS HkN. pose proof HL as (S1 & S2 & N0 & N1 & HC & HE).
  pose proof (sec_map_size_ge n ltac:(lia)) as SG.
  pose proof (PHI_nonneg st HL) as P0. pose proof (GP_nonneg st (LW_emb st HL)) as G0. pose proof (pcost_nonneg (sec_map_size n) ltac:(lia)) as PC0.
  unfold large_alloc. cbv zeta. cbn [evq ev].
  split; [lia|]. split; [apply sec_map_size_mod|]. split; [lia|]. split; [lia|].
  intros z. destruct (negb (mmap_answer_ok ATOP _ z)) eqn:E0; [apply evq_aundef|].
  destruct (is_err z) eqn:E1.
  { eapply evq_mono_b; [exact HM| apply (HkN st HL); lia| lia| lia]. }
  destruct (negb (avoids_all z (sec_map_size n) (RESV ++ asec_ranges st))) eqn:E2; [apply evq_aundef|].
  set (ch := CSec z (sec_map_size n) n).
  destruct (a_nsec st =? a_nres st).
  - destruct (K_PTRARR_RESERVE <? _) eqn:E3; [apply evq_aundef|]. apply Z.ltb_ge in E3.
    cbn [evq ev].
    split; [reflexivity|]. split; [unfold K_PTRARR_COMMIT; lia|]. split; [reflexivity|].
    right. split; [reflexivity|]. split.
    { right. rewrite S2. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *. lia. }
    assert (EPn : PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) = PHI st - K_PTRARR_COMMIT).
    { rewrite PHI_set_nres. cbn [a_nres set_nsec]. rewrite PHI_set_nsec. unfold K_PTRARR_COMMIT, K_CHUNKS_BLOCK. lia. }
    assert (HLn : LW (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))).
    { unfold LW. cbn [a_space_beg a_ptr_array a_nres set_nres set_nsec]. split; [exact S1|]. split; [exact S2|].
      split; [unfold K_CHUNKS_BLOCK; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|]. split; [exact HC| exact HE]. }
    pose proof (PHI_nonneg _ HLn). split; [lia|].
    intros r. destruct (negb (fixed_answer_ok _ r)); [apply evq_aundef|]. destruct (is_err r); [apply evq_aundef|].
    replace (PHI st + sec_map_size n - sec_map_size n - K_PTRARR_COMMIT) with (PHI (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + 0) by lia.
    replace (GP st + gx + pcost (sec_map_size n) - pcost (sec_map_size n)) with (GP (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) + gx) by (change (GP (set_nres _ (set_nsec _ st))) with (GP st); lia).
    apply HkS; [exact HLn| rewrite EPn; unfold K_PTRARR_COMMIT; lia| change (GP (set_nres _ (set_nsec _ st))) with (GP st); lia| exact I].
  - replace (PHI st + sec_map_size n - sec_map_size n) with (PHI (set_nsec (a_nsec st + 1) st) + 0) by (rewrite PHI_set_nsec; lia).
    replace (GP st + gx + pcost (sec_map_size n) - pcost (sec_map_size n)) with (GP (set_nsec (a_nsec st + 1) st) + gx) by (change (GP (set_nsec _ st)) with (GP st); lia).
    apply HkS; [apply LW_set_nsec; exact HL| rewrite PHI_set_nsec; lia| change (GP (set_nsec _ st)) with (GP st); lia| exact I].
Qed.

Lemma evq_large_dealloc : forall {R} RP gx st mb ms (k : astate -> AM R) extra,
  LW st ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (large_dealloc st mb ms k).
Proof.
  intros R RP gx st mb ms k extra HL Hk. unfold large_dealloc, poison0, flush_shadow. cbv zeta.
  assert (UNM : evq RP (GP st + gx) (PHI st + extra)
            (ev (AMunmap mb ms) (fun r => if r =? 0 then k (set_nsec (a_nsec st - 1) st)
                                          else if is_err r then aundef_ USpin (k (set_nsec (a_nsec st - 1) st))
                                          else aundef_ UBadAnswer (k (set_nsec (a_nsec st - 1) st))))).
  { cbn [evq ev]. intros z. destruct (z =? 0).
    - replace (PHI st + extra) with (PHI (set_nsec (a_nsec st - 1) st) + extra) by (rewrite PHI_set_nsec; lia).
      change (GP st) with (GP (set_nsec (a_nsec st - 1) st)).
      apply Hk; [apply LW_set_nsec; exact HL| rewrite PHI_set_nsec; lia| change (GP (set_nsec _ st)) with (GP st); lia].
    - destruct (is_err z); apply evq_aundef. }
  destruct (flush_beg mb <? flush_end mb ms); [| exact UNM].
  cbn [evq]. intros r. destruct (r =? 0); [exact UNM| apply evq_aundef].
Qed.

Definition RPst (gp : Z) (st' : astate) : Prop := LW st' /\ GP st' <= gp.
Definition RPm (n : Z) (gp : Z) (r : astate * option AsanCtrl.aptr) : Prop :=
  LW (fst r) /\ GP (fst r) + (match snd r with Some _ => 0 | None => if is_primary n then 0 else pcost (sec_map_size n) end) <= gp.
Lemma RPst_mono : RPmono RPst. Proof. intros g g' r Hg [H1 H2]. split; [exact H1| lia]. Qed.
Lemma RPm_mono : forall n, RPmono (RPm n). Proof. intros n g g' r Hg [H1 H2]. split; [exact H1| lia]. Qed.

Lemma evq_amalloc : forall RESV st n,
  LW st -> 0 <= n -> emb_sz st + 110 <= EMB_MAX - 4096 ->
  evq (RPm n) (GP st + (if is_primary n then 0 else pcost (sec_map_size n))) (PHI st + (if is_primary n then EXB else sec_map_size n))
      (amalloc ATOP RESV st n).
Proof.
  intros RESV st n HL Hn Hsz. unfold amalloc. cbv zeta. pose proof (GP_nonneg st (LW_emb st HL)) as G0.
  destruct (_ || _) eqn:E0.
  { unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL|]. destruct (is_primary n); lia. }
  apply Bool.orb_false_iff in E0 as [E0a E0b]. apply Z.ltb_ge in E0a. apply Z.ltb_ge in E0b.

  assert (FIN : forall st1 ch gp b, LW st1 -> GP st1 <= gp -> chunk_cls_ok ch ->
            evq (RPm n) gp b
              (match ch with
               | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))
               | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7)) (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1)))
               end)).
  { intros st1 ch gp b HL1 HG1 Hch.
    assert (POST : RPm n gp (set_next (N.succ (a_next st1)) (set_live (<[a_next st1:=ch]> (a_live st1)) st1), Some (a_next st1))).
    { unfold RPm. cbn [fst snd]. split; [apply LW_set_next, LW_live_insert; assumption|].
      change (GP (set_next _ (set_live _ st1))) with (GP st1). lia. }
    destruct ch as [c0 n0|mb ms n0]; [exact POST| unfold poison0; exact POST]. }
  destruct (is_primary n) eqn:EP.
  - pose proof (primary_class_facts n Hn EP) as (C1 & _).
    replace (PHI st + EXB) with (PHI st + 0 + EXB) by lia.
    apply evq_cache_alloc_x; [apply RPm_mono| lia| exact HL| lia| exact Hsz| lia|].
    intros st1 ok HL1 HP1 HG1. destruct ok.
    + apply (FIN st1 (CPrim (class_id (needed_size n)) n)); [exact HL1| lia| cbn; lia].
    + unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL1|]. rewrite EP. lia.
  - pose proof (not_primary_large n Hn EP) as NL.
    replace (GP st + pcost (sec_map_size n)) with (GP st + 0 + pcost (sec_map_size n)) by lia.
    apply evq_large_alloc; [apply RPm_mono| lia| exact HL| lia| |].
    + intros st1 ch HL1 HP1 HG1 Hch. apply (FIN st1 ch); [exact HL1| lia| exact Hch].
    + intros st1 HL1 HP1 HG1. unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL1|]. rewrite EP. lia.
Qed.

Lemma evq_aaligned16x : forall RESV st n,
  LW st -> 16 <= n <= ALIGNED_NMAX -> n mod 16 = 0 -> emb_sz st + 110 <= EMB_MAX - 4096 ->
  evq (RPm n) (GP st + 0) (PHI st + EXB) (aaligned16x ATOP RESV st n).
Proof.
  intros RESV st n HL Hn Hm Hsz. unfold aaligned16x. cbv zeta. pose proof (GP_nonneg st (LW_emb st HL)) as G0.
  pose proof (al16_facts n Hn Hm) as F. cbv zeta in F. destruct F as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & EP).
  replace (PHI st + EXB) with (PHI st + 0 + EXB) by lia.
  apply evq_cache_alloc_x; [apply RPm_mono| lia| exact HL| lia| exact Hsz| lia|].
  intros st1 ok HL1 HP1 HG1. destruct ok.
  - unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [apply LW_set_next, LW_live_insert; [exact HL1| cbn; lia]|].
    change (GP (set_next _ (set_live _ st1))) with (GP st1). lia.
  - unfold aret. cbn [evq]. unfold RPm. cbn [fst snd]. split; [exact HL1|]. rewrite EP. lia.
Qed.

Lemma evq_recycle_chunk : forall {R} RP gx st ch (k : astate -> AM R) extra,
  LW st -> chunk_cls_ok ch -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (recycle_chunk st ch k).
Proof.
  intros R RP gx st ch k extra HL Hch Hex Hk. destruct ch as [c n|mb ms n]; cbn [recycle_chunk].
  - apply evq_cache_dealloc; auto.
  - apply evq_large_dealloc; auto.
Qed.

Lemma evq_recycle_chunks : forall {R} RP gx l st (k : astate -> AM R) extra,
  LW st -> Forall chunk_cls_ok l -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (recycle_chunks st l k).
Proof.
  intros R RP gx l. induction l as [|ch l IH]; intros st k extra HL HF Hex Hk; cbn [recycle_chunks].
  - apply Hk; [exact HL| lia| lia].
  - apply Forall_cons_iff in HF as [Hch HF]. apply evq_recycle_chunk; auto.
    intros st1 HL1 HP1 HG1. apply IH; auto. intros st2 HL2 HP2 HG2. apply Hk; [exact HL2| lia| lia].
Qed.

Lemma batch_K : 1 <= K_BATCH_CLASS <= 31. Proof. unfold K_BATCH_CLASS. lia. Qed.

Lemma evq_do_recycle : forall {R} RP gx bs st (k : astate -> AM R) extra,
  LW st -> Forall chunk_cls_ok (qchunks bs) -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (do_recycle st bs k).
Proof.
  intros R RP gx bs. induction bs as [|b bs IH]; intros st k extra HL HF Hex Hk; cbn [do_recycle].
  - apply Hk; [exact HL| lia| lia].
  - rewrite qchunks_cons in HF. apply Forall_app in HF as [Hb HF].
    apply evq_recycle_chunks; auto. { apply Forall_rev. exact Hb. }
    intros st1 HL1 HP1 HG1. apply evq_cache_dealloc; auto; [apply batch_K|].
    intros st2 HL2 HP2 HG2. apply IH; auto. intros st3 HL3 HP3 HG3.
    apply Hk; [exact HL3| lia| lia].
Qed.

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

Lemma evq_recycle : forall {R} RP gx st mn (k : astate -> AM R) extra,
  LW st -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (recycle st mn k).
Proof.
  intros R RP gx st mn k extra HL Hex Hk. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  unfold recycle. cbv zeta.
  destruct (_ <? _); [apply evq_aundef|].
  assert (TAIL : forall gl extracted exb, incl (qchunks (gl ++ extracted)) (qchunks (a_qglob st)) ->
    evq RP (GP st + gx) (PHI st + extra)
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
  assert (HL1 : LW (set_qglob rest bytes2 st)).
  { apply (LW_chunks st); try reflexivity; [exact HL|]. apply QOK_parts. cbn [a_qloc a_qglob set_qglob]. split; [exact Q1|]. split; [exact Q2|].
    eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. right. exact Hin. }
  change (PHI st) with (PHI (set_qglob rest bytes2 st)). change (GP st) with (GP (set_qglob rest bytes2 st)).
  apply evq_do_recycle; [exact HL1| | exact Hex|].
  { eapply Forall_incl'; [exact Q3|]. intros ch Hin. apply INC. apply in_app_iff. left. exact Hin. }
  intros st1 HL2 HP1 HG1. apply Hk; [exact HL2| exact HP1| exact HG1].
Qed.

Lemma evq_drain : forall {R} RP gx st (k : astate -> AM R) extra,
  LW st -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (drain st k).
Proof.
  intros R RP gx st k extra HL Hex Hk. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  unfold drain. cbv zeta. set (st1 := set_qglob _ _ (set_qloc [] 0 st)).
  assert (HL1 : LW st1).
  { apply (LW_chunks st); try reflexivity; [exact HL|]. apply QOK_parts. cbn. split; [exact Q1|]. split; [constructor|]. rewrite qchunks_app. apply Forall_app. auto. }
  change (PHI st) with (PHI st1). change (GP st) with (GP st1).
  destruct (Q_MAX <? _).
  - apply evq_recycle; [exact HL1| exact Hex|]. intros st2 HL2 HP2 HG2. apply Hk; [exact HL2| exact HP2| exact HG2].
  - apply Hk; [exact HL1| apply Z.le_refl| apply Z.le_refl].
Qed.

Lemma qchunks_rev_snoc : forall P rl b,
  Forall P (qchunks (rev (b :: rl))) <-> Forall P (qchunks (rev rl)) /\ Forall P (b_chunks b).
Proof. intros P rl b. cbn [rev]. rewrite qchunks_app, Forall_app, qchunks_cons. cbn. rewrite app_nil_r. tauto. Qed.

Lemma evq_enqueue : forall {R} RP gx st ch (k : astate -> AM R) extra,
  RPmono RP -> LW st -> chunk_cls_ok ch -> 0 <= extra ->
  (forall st', LW st' -> PHI st' <= PHI st -> GP st' <= GP st -> evq RP (GP st' + gx) (PHI st' + extra) (k st')) ->
  evq RP (GP st + gx) (PHI st + extra) (enqueue st ch k).
Proof.
  intros R RP gx st ch k extra HM HL Hch Hex Hk. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3).
  unfold enqueue. cbv zeta.
  assert (NEW : evq RP (GP st + gx) (PHI st + extra)
      (cache_alloc st K_BATCH_CLASS (fun st1 ok => if negb ok then aundef_ USpin (k st1)
         else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (chunk_size ch + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + chunk_size ch + Q_BATCH_BYTES) st1)))).
  { replace (PHI st + extra) with (PHI st + extra + 0) by lia.
    apply evq_cache_alloc; [exact HM| exact HL| apply batch_K| exact Hex|]. intros st1 ok HL1 HP1 HG1. destruct ok; cbn [negb]; [|apply evq_aundef].
    set (st2 := set_qloc _ _ st1).
    assert (HL2 : LW st2).
    { apply (LW_chunks st1); try reflexivity; [exact HL1|]. pose proof (proj1 (QOK_parts st1) (LW_qok st1 HL1)) as (R1 & R2 & R3).
      apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live st2]. split; [exact R1|]. split; [| exact R3].
      rewrite qchunks_app, Forall_app. split; [exact R2|]. rewrite qchunks_cons. cbn. constructor; [exact Hch| constructor]. }
    change (PHI st1) with (PHI st2). change (GP st1) with (GP st2).
    apply Hk; [exact HL2| exact HP1| exact HG1]. }
  destruct (rev (a_qloc st)) as [|b rl] eqn:ER.
  - exact NEW.
  - destruct (b_count b =? Q_BATCH). { exact NEW. }
    set (st2 := set_qloc _ _ st).
    assert (HL2 : LW st2).
    { apply (LW_chunks st); try reflexivity; [exact HL|]. apply QOK_parts. cbn [a_qloc a_qglob set_qloc a_live st2]. split; [exact Q1|]. split; [| exact Q3].
      assert (E : a_qloc st = rev (b :: rl)) by (rewrite <- ER, rev_involutive; reflexivity).
      rewrite E in Q2. apply qchunks_rev_snoc in Q2 as [Q2a Q2b]. apply qchunks_rev_snoc. split; [exact Q2a|]. cbn. constructor; assumption. }
    change (PHI st) with (PHI st2). change (GP st) with (GP st2).
    apply Hk; [exact HL2| apply Z.le_refl| apply Z.le_refl].
Qed.

Lemma evq_afree : forall st id,
  LW st -> evq RPst (GP st + 0) (PHI st + 0) (afree st (Some id)).
Proof.
  intros st id HL. pose proof (proj1 (QOK_parts st) (LW_qok st HL)) as (Q1 & Q2 & Q3). unfold afree.
  destruct ((a_live st) !! id) as [ch|] eqn:Hl; [|apply evq_aundef]. cbv zeta.
  pose proof (live_chunks_delete st id ch Hl) as HPl.
  pose proof (Permutation_Forall HPl Q1) as Q1'. apply Forall_cons_iff in Q1' as [Hch _].
  set (st1 := set_live (delete id (a_live st)) st).
  assert (HL1 : LW st1) by (apply LW_live_delete; exact HL).
  assert (AFTER : forall st2, LW st2 -> PHI st2 <= PHI st -> GP st2 <= GP st ->
    evq RPst (GP st2 + 0) (PHI st2 + 0) (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)).
  { intros st2 HL2 HP2 HG2. destruct (Q_CACHE <? _).
    - apply evq_drain; [exact HL2| lia|]. intros st3 HL3 HP3 HG3. unfold aret. cbn [evq]. split; [exact HL3| lia].
    - unfold aret. cbn [evq]. split; [exact HL2| lia]. }
  change (PHI st) with (PHI st1). change (GP st) with (GP st1). destruct (chunk_size ch <=? Q_MAX).
  - apply evq_enqueue; [apply RPst_mono| exact HL1| exact Hch| lia|]. intros st2 HL2 HP2 HG2. apply AFTER; [exact HL2| exact HP2| exact HG2].
  - apply evq_recycle_chunk; [exact HL1| exact Hch| lia|]. intros st2 HL2 HP2 HG2. apply AFTER; [exact HL2| exact HP2| exact HG2].
Qed.
End Ev.
End CANSEC1.
End TwinB.
