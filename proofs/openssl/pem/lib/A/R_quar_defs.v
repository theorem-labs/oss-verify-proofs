(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Mem Cells Frame Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_cache_defs R_glue_defs R_depot_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Notation batch := (Z * list (Z * Z))%type (only parsing).
Definition bsum (ents : list (Z * Z)) : Z := fold_right (fun e acc => snd e + acc) 0 ents.
Definition qbytes (bs : list batch) : Z := fold_right (fun b acc => 8192 + bsum (snd b) + acc) 0 bs.
Definition qfirst (bs : list batch) : Z := match bs with [] => 0 | (b, _) :: _ => b end.
Definition qlast (bs : list batch) : Z := last (map fst bs) 0.

(* [comment removed for export] *)
Lemma qcache_rep_iff : forall (m : mem) Q bs, qcache_rep m Q bs <->
  rw_cells asegs m Q [C8 (Z_to_bv 64 (Z.of_nat (length bs))); C8 (Z_to_bv 64 (qfirst bs)); C8 (Z_to_bv 64 (qlast bs));
                      C8 (Z_to_bv 64 (qbytes bs))] /\ qchain m bs.
Proof. intros m Q bs. unfold qcache_rep, qfirst, qlast, qbytes, bsum. reflexivity. Qed.

Lemma qbatch_iff : forall (m : mem) b nxt ents, qbatch m b nxt ents <->
  rw_cells asegs m b [C8 (Z_to_bv 64 nxt); C8 (Z_to_bv 64 (8192 + bsum ents)); C8 (Z_to_bv 64 (Z.of_nat (length ents)))]
  /\ (exists ws, u64arr asegs m (b + 0x18) ws /\ length ws = 1021%nat /\ firstn (length ents) ws = map (fun e => Z_to_bv 64 (fst e)) ents)
  /\ (length ents <= 1021)%nat.
Proof. intros. unfold qbatch, bsum. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint qchain_to (m : mem) (bs : list batch) (tl : Z) : Prop :=
  match bs with
  | [] => True
  | (b, ents) :: rest => qbatch m b (match rest with [] => tl | (b', _) :: _ => b' end) ents /\ qchain_to m rest tl
  end.

Lemma qchain_to_0 : forall (m : mem) bs, qchain m bs <-> qchain_to m bs 0.
Proof.
  intros m bs. induction bs as [|[b ents] rest IH]; [cbn; tauto|].
  cbn [qchain qchain_to]. rewrite IH. reflexivity.
Qed.

Lemma qchain_to_snoc : forall (m : mem) pre b ents tl,
  qchain_to m (pre ++ [(b, ents)]) tl <-> qchain_to m pre b /\ qbatch m b tl ents.
Proof.
  intros m pre. induction pre as [|[b0 e0] pre IH]; intros b ents tl; [cbn; tauto|].
  cbn [app qchain_to]. rewrite IH.
  destruct pre as [|[b1 e1] pre']; cbn [app]; tauto.
Qed.

Lemma qbatch_frame : forall W (m m' : mem) b nxt ents, qbatch m b nxt ents -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W b 8192 -> qbatch m' b nxt ents.
Proof.
  intros W m m' b nxt ents QB MU WM HD. apply qbatch_iff in QB. apply qbatch_iff.
  destruct QB as (H & (ws & A & L & P) & Le). split; [| split; [exists ws; split; [| split; [exact L| exact P]]| exact Le]].
  - apply (rw_cells_transport asegs W m m' _ _ H MU WM). cbn [cells_size csize Nat.add]. eapply dep_disj_sub; [exact HD| |]; lia.
  - apply (u64arr_transport asegs W m m' _ _ A MU WM). rewrite L. eapply dep_disj_sub; [exact HD| |]; lia.
Qed.

Lemma qchain_to_frame : forall W (m m' : mem) bs tl, qchain_to m bs tl -> munch W m m' -> wmono asegs m m' ->
  Forall (fun e => disjoint_from W (fst e) 8192) bs -> qchain_to m' bs tl.
Proof.
  intros W m m' bs tl. induction bs as [|[b ents] rest IH]; intros QC MU WM HF; [exact I|].
  cbn [qchain_to] in *. destruct QC as (QB & QR). inversion HF as [|x l H1 H2]; subst.
  split; [eapply qbatch_frame; eassumption| apply IH; assumption].
Qed.

(* [comment removed for export] *)
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. intros l1 l2. unfold bsum. induction l1 as [|e l1 IH]; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.

Lemma qbytes_app : forall l1 l2, qbytes (l1 ++ l2) = qbytes l1 + qbytes l2.
Proof. intros l1 l2. unfold qbytes. induction l1 as [|e l1 IH]; cbn [app fold_right]; [lia| rewrite IH; lia]. Qed.

Lemma qbytes_snoc : forall pre b ents, qbytes (pre ++ [(b, ents)]) = qbytes pre + 8192 + bsum ents.
Proof. intros. rewrite qbytes_app. unfold qbytes. cbn [fold_right snd]. lia. Qed.

Lemma qlast_snoc : forall pre b ents, qlast (pre ++ [(b, ents)]) = b.
Proof. intros. unfold qlast. rewrite map_app. cbn [map]. apply last_last. Qed.

Lemma qfirst_snoc : forall pre b e e', qfirst (pre ++ [(b, e)]) = qfirst (pre ++ [(b, e')]).
Proof. intros pre b e e'. destruct pre as [|[b0 e0] pre]; reflexivity. Qed.

Lemma length_snoc' : forall {X} (pre : list X) x y, length (pre ++ [x]) = length (pre ++ [y]).
Proof. intros. rewrite !app_length. reflexivity. Qed.

Lemma firstn_upd_snoc : forall {X} (ws : list X) k x, (k < length ws)%nat -> firstn (S k) (upd ws k x) = firstn k ws ++ [x].
Proof.
  intros X ws. induction ws as [|w ws IH]; intros k x Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [upd firstn app]. f_equal. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition r24 (SB : Z) : Z := SB + 24 * 2 ^ 32.
Definition qwf (SB : Z) (bs : list batch) : Prop :=
  List.NoDup (map fst bs)
  /\ Forall (fun e => fst e mod 8192 = 0 /\ r24 SB <= fst e /\ fst e + 8192 <= r24 SB + 2 ^ 32 /\ (length (snd e) <= 1021)%nat
                     /\ Forall (fun x => 0 <= snd x) (snd e)) bs.

Lemma align_disj : forall x y, x mod 8192 = 0 -> y mod 8192 = 0 -> x <> y -> x + 8192 <= y \/ y + 8192 <= x.
Proof. intros x y Hx Hy Hne. Z.div_mod_to_equations. lia. Qed.

Lemma qwf_snoc_disj : forall SB pre b ents, qwf SB (pre ++ [(b, ents)]) ->
  Forall (fun e => fst e + 8192 <= b \/ b + 8192 <= fst e) pre.
Proof.
  intros SB pre b ents (ND & HF). rewrite map_app in ND. cbn [map fst] in ND.
  pose proof (NoDup_remove_2 (map fst pre) [] b ND) as NI. rewrite app_nil_r in NI.
  apply Forall_forall. intros [b' e'] Hin. cbn [fst].
  pose proof (proj1 (Forall_forall _ _) HF (b', e') ltac:(apply in_or_app; left; exact Hin)) as (A1 & _).
  pose proof (proj1 (Forall_forall _ _) HF (b, ents) ltac:(apply in_or_app; right; left; reflexivity)) as (A2 & _).
  cbn [fst] in *.
  apply align_disj; [exact A1| exact A2|]. intros ->. apply NI. apply in_map_iff. exists (b, e'). split; [reflexivity| exact Hin].
Qed.

Lemma qwf_last : forall SB pre b ents, qwf SB (pre ++ [(b, ents)]) ->
  b mod 8192 = 0 /\ r24 SB <= b /\ b + 8192 <= r24 SB + 2 ^ 32 /\ (length ents <= 1021)%nat /\ Forall (fun x => 0 <= snd x) ents.
Proof.
  intros SB pre b ents (_ & HF). exact (proj1 (Forall_forall _ _) HF (b, ents) ltac:(apply in_or_app; right; left; reflexivity)).
Qed.

Lemma bsum_nonneg : forall ents, Forall (fun x => 0 <= snd x) ents -> 0 <= bsum ents.
Proof. intros ents H. induction H as [|x l Hx Hl IH]; [cbn; lia|]. unfold bsum in *. cbn [fold_right]. lia. Qed.

Lemma qbytes_ge : forall SB bs, qwf SB bs -> 8192 * Z.of_nat (length bs) <= qbytes bs.
Proof.
  intros SB bs (_ & HF). induction HF as [|e l (_ & _ & _ & _ & He) Hl IH]; [cbn; lia|].
  pose proof (bsum_nonneg _ He). unfold qbytes in *. cbn [length fold_right]. lia.
Qed.

Lemma qbytes_nonneg : forall SB bs, qwf SB bs -> 0 <= qbytes bs.
Proof. intros SB bs H. pose proof (qbytes_ge SB bs H). lia. Qed.

Lemma qwf_region : forall SB bs, qwf SB bs -> Forall (fun e => r24 SB <= fst e /\ fst e + 8192 <= r24 SB + 2 ^ 32) bs.
Proof.
  intros SB bs (_ & HF). apply Forall_forall. intros e Hin. pose proof (proj1 (Forall_forall _ _) HF e Hin) as (_ & A & B & _).
  split; assumption.
Qed.

(* [comment removed for export] *)
Lemma qwf_app_last : forall SB pre b ents x, qwf SB (pre ++ [(b, ents)]) -> (length ents < 1021)%nat -> 0 <= snd x ->
  qwf SB (pre ++ [(b, ents ++ [x])]).
Proof.
  intros SB pre b ents x (ND & HF) HL Hx. split.
  - rewrite map_app in *. exact ND.
  - apply Forall_app in HF. destruct HF as (H1 & H2). apply Forall_app. split; [exact H1|].
    inversion H2 as [|y l (A & B & C & D & E) H3]; subst. constructor; [| constructor].
    cbn [fst snd] in *. rewrite app_length. cbn [length]. repeat split; try assumption; [lia|].
    apply Forall_app. split; [exact E| constructor; [exact Hx| constructor]].
Qed.

(* [comment removed for export] *)
Fixpoint q_dec64 (k : nat) (bs : list byte) : list word :=
  match k with O => [] | S k' => le_bytes_to_word (firstn 8 bs) :: q_dec64 k' (skipn 8 bs) end.

Lemma q_dec64_length : forall k bs, length (q_dec64 k bs) = k.
Proof. induction k as [|k IH]; intros bs; cbn [q_dec64 length]; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma q_u64s_dec64 : forall k bs, length bs = (8 * k)%nat -> u64s (q_dec64 k bs) = bs.
Proof.
  induction k as [|k IH]; intros bs H; [destruct bs; [reflexivity| cbn in H; lia]|].
  cbn [q_dec64 u64s]. rewrite dep_le8_of_bytes by (rewrite firstn_length; lia).
  rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.

Lemma q_rw_cells_u64arr : forall (m : mem) A k bs, rw_cells asegs m A [CB (8 * k) bs] -> u64arr asegs m A (q_dec64 k bs).
Proof.
  intros m A k bs [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (HL & _).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  split.
  - rewrite q_u64s_dec64 by lia. exact HB.
  - rewrite q_dec64_length. cbn [cells_size csize] in HW. replace (8 * Z.of_nat k) with (Z.of_nat (8 * k + 0)) by lia. exact HW.
Qed.

Lemma q_u64arr_rw : forall (m : mem) A ws, u64arr asegs m A ws -> rw_cells asegs m A [CB (8 * length ws) (u64s ws)].
Proof.
  intros m A ws [HB HW]. split.
  - split; [cbn; split; [rewrite u64s_length; reflexivity| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. replace (Z.of_nat (8 * length ws + 0)) with (8 * Z.of_nat (length ws)) by lia. exact HW.
Qed.

Lemma q_wr_at_app : forall segs (m : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m a n1 -> wr_at segs m (a + n1) n2 -> wr_at segs m a (n1 + n2).
Proof.
  intros segs m a n1 n2 H1 H2 (Ha & Hb & HA) (Ha' & Hb' & HB). unfold wr_at. repeat split; try lia.
  intros i Hi. destruct (Z.lt_ge_cases i n1).
  - apply HA. lia.
  - replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_cons : forall (m : mem) A w ws, rw_cells asegs m A [C8 w] -> u64arr asegs m (A + 8) ws -> u64arr asegs m A (w :: ws).
Proof.
  intros m A w ws [[_ HB] HW] [HB2 HW2]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  cbn [cells_size csize Nat.add] in HW. split.
  - cbn [u64s]. apply bytes_at_app. split; [exact HB| rewrite length_le8; exact HB2].
  - cbn [length]. replace (8 * Z.of_nat (S (length ws))) with (8 + 8 * Z.of_nat (length ws)) by lia.
    apply q_wr_at_app; [lia| lia| exact HW| exact HW2].
Qed.

(* [comment removed for export] *)
Lemma batch_of_cb : forall (m : mem) B jb, rw_cells asegs m B [CB 8192 jb] ->
  exists (w0 w1 w2 : word) (ws : list word),
    rw_cells asegs m B [C8 w0; C8 w1; C8 w2] /\ u64arr asegs m (B + 24) ws /\ length ws = 1021%nat.
Proof.
  intros m B jb [[Hwf HB] HW]. cbv [cells_wf cell_wf] in Hwf.
  let v := eval vm_compute in 8192%nat in change 8192%nat with v in Hwf. destruct Hwf as (HL & _).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. cbn [cells_size csize] in HW.
  assert (L : length jb = 8192%nat) by exact HL.
  exists (le_bytes_to_word (firstn 8 jb)), (le_bytes_to_word (firstn 8 (skipn 8 jb))),
         (le_bytes_to_word (firstn 8 (skipn 16 jb))), (q_dec64 1021 (skipn 24 jb)).
  assert (E : jb = firstn 24 jb ++ skipn 24 jb) by (symmetry; apply firstn_skipn).
  rewrite E in HB. apply bytes_at_app in HB. destruct HB as (HB1 & HB2).
  rewrite firstn_length in HB2. replace (Z.of_nat (Nat.min 24 (length jb))) with 24%Z in HB2 by (rewrite L; reflexivity).
  assert (W1 : wr_at asegs m B 24) by (destruct HW as (A1 & A2 & A3); split; [lia| split; [lia| intros i Hi; apply A3; lia]]).
  assert (W2 : wr_at asegs m (B + 24) (8 * 1021))
    by (destruct HW as (A1 & A2 & A3); split; [lia| split; [lia|]]; intros i Hi; replace (B + 24 + i) with (B + (24 + i)) by lia;
        apply A3; lia).
  split; [| split; [| apply q_dec64_length]].
  - split; [split; [cbn; repeat split| ]|].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r.
      rewrite !dep_le8_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia).
      replace (firstn 8 jb ++ firstn 8 (skipn 8 jb) ++ firstn 8 (skipn 16 jb)) with (firstn 24 jb); [exact HB1|].
      replace 24%nat with (8 + 16)%nat by reflexivity. rewrite <- (firstn_skipn 8 jb) at 1. rewrite firstn_app.
      rewrite firstn_length, L. replace (8 + 16 - Nat.min 8 8192)%nat with 16%nat by reflexivity.
      rewrite firstn_firstn. replace (Nat.min (8 + 16) 8) with 8%nat by reflexivity. f_equal.
      rewrite <- (firstn_skipn 8 (skipn 8 jb)) at 1. rewrite firstn_app, firstn_length, skipn_length, L.
      replace (16 - Nat.min 8 (8192 - 8))%nat with 8%nat by reflexivity. rewrite firstn_firstn, skipn_skipn.
      replace (Nat.min 16 8) with 8%nat by reflexivity. reflexivity.
    + cbn [cells_size csize Nat.add]. exact W1.
  - split.
    + rewrite q_u64s_dec64 by (rewrite skipn_length, L; reflexivity). exact HB2.
    + rewrite q_dec64_length. exact W2.
Qed.

Lemma qfirst_app_ne : forall l1 l2, l1 <> [] -> qfirst (l1 ++ l2) = qfirst l1.
Proof. intros l1 l2 H. destruct l1 as [|[b e] l1]; [congruence| reflexivity]. Qed.

Lemma snoc_ne : forall {X} (l : list X) x, l ++ [x] <> [].
Proof. intros X l x H. apply app_eq_nil in H. destruct H as (_ & H). discriminate. Qed.

Lemma qwf_prefix : forall SB l1 l2, qwf SB (l1 ++ l2) -> qwf SB l1.
Proof.
  intros SB l1 l2 (ND & HF). split.
  - rewrite map_app in ND. apply NoDup_app_remove_r in ND. exact ND.
  - apply Forall_app in HF. exact (proj1 HF).
Qed.

(* [comment removed for export] *)
Lemma qchain_to_app : forall (m : mem) l1 l2 tl, l2 <> [] ->
  (qchain_to m (l1 ++ l2) tl <-> qchain_to m l1 (qfirst l2) /\ qchain_to m l2 tl).
Proof.
  intros m l1. induction l1 as [|[b e] l1 IH]; intros l2 tl Hne; [cbn; tauto|].
  cbn [app qchain_to]. rewrite IH by exact Hne.
  destruct l1 as [|[b1 e1] l1']; cbn [app].
  - destruct l2 as [|[b2 e2] l2']; [congruence| cbn [qfirst]; tauto].
  - cbn [qfirst]. tauto.
Qed.

Lemma qbytes_nil : qbytes [] = 0.
Proof. reflexivity. Qed.

Lemma last_app_cons : forall {X} (l1 l2 : list X) x d, last (l1 ++ x :: l2) d = last (x :: l2) d.
Proof.
  intros X l1 l2 x d. induction l1 as [|y l1 IH]; [reflexivity|]. cbn [app]. rewrite <- IH. destruct l1 as [|z l1]; reflexivity.
Qed.

Lemma qlast_app_ne : forall l1 l2, l2 <> [] -> qlast (l1 ++ l2) = qlast l2.
Proof.
  intros l1 l2 H. unfold qlast. rewrite map_app.
  destruct l2 as [|x l2]; [congruence|]. cbn [map]. apply last_app_cons.
Qed.
