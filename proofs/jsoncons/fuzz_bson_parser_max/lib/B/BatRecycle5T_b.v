(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPoison_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatSecAllocPost_b
     BatRecycle2C_b BatRecycle3L_b BatRecycle4P_b BatRecycle4S_b BatRecycle5A_b BatRecycle5I_b BatRecycle5G_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Tr.
Variables (HI t ctx tp key tsd spb ris qs parr : Z).
Hypothesis GEO : art_geo HI t ctx tp tsd spb ris qs.

Fixpoint art_rels_pre (G : art_rg) (es : list art_rel) : Prop :=
  match es with [] => True | e :: r => art_rel_pre G e /\ art_rels_pre (art_rel_step e G) r end.
Fixpoint art_rels_fp (sp1 : Z) (G : art_rg) (es : list art_rel) : list (Z * Z) :=
  match es with [] => [] | e :: r => art_rel_fp t spb ris parr sp1 G e ++ art_rels_fp sp1 (art_rel_step e G) r end.
Definition art_rels_events (es : list art_rel) : list aev := flat_map art_rel_events es.
Definition art_zapart (e : art_rel) (zlo zlen : Z) : Prop := apart (fst (art_rel_zone spb e)) (snd (art_rel_zone spb e)) zlo zlen.
Fixpoint art_rels_sep (es : list art_rel) : Prop :=
  match es with [] => True | e :: r => Forall (fun e' => art_zapart e (fst (art_rel_zone spb e')) (snd (art_rel_zone spb e'))) r /\ art_rels_sep r end.

#[using="Type"] Lemma art_rel_steps_app : forall es1 es2 G, art_rel_steps (es1 ++ es2) G = art_rel_steps es2 (art_rel_steps es1 G).
Proof. intros. unfold art_rel_steps. apply fold_left_app. Qed.
#[using="Type"] Lemma art_rels_fp_app : forall sp1 es1 es2 G, art_rels_fp sp1 G (es1 ++ es2) = art_rels_fp sp1 G es1 ++ art_rels_fp sp1 (art_rel_steps es1 G) es2.
Proof. intros sp1 es1. induction es1 as [|e r IH]; intros es2 G; cbn [app art_rels_fp art_rel_steps fold_left]; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
#[using="Type"] Lemma art_rels_events_app : forall es1 es2, art_rels_events (es1 ++ es2) = art_rels_events es1 ++ art_rels_events es2.
Proof. intros. unfold art_rels_events. apply flat_map_app. Qed.
#[using="Type"] Lemma art_rels_pre_app : forall es1 es2 G, art_rels_pre G (es1 ++ es2) <-> art_rels_pre G es1 /\ art_rels_pre (art_rel_steps es1 G) es2.
Proof. induction es1 as [|e r IH]; intros es2 G; cbn [app art_rels_pre art_rel_steps fold_left]; [tauto|]. rewrite IH. unfold art_rel_steps. tauto. Qed.

(* [comment removed for export] *)
Definition art_rel_static (G : art_rg) (e : art_rel) : Prop :=
  match e with
  | REP c w d b1 n => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (rg_cls G c)) w
                      /\ 0 <= d /\ d mod 16 = 0 /\ d + 16 + (n + 7) / 8 * 8 <= AsanTab.class_size c /\ 0 <= b1 < 256 /\ 0 <= n < 2 ^ 32
  | RES mb ms m b1 n => In (mb, ms) (rg_bl G) /\ mb + 4096 <= m /\ m + 16 <= mb + ms /\ 0 <= b1 < 256 /\ 0 <= n < 2 ^ 32
  | REB wb => art_cptr_ok 8192 (cl_au (rg_cls G 24)) wb
  end.
#[using="Type"] Lemma art_rel_pre_static : forall G e, art_rel_pre G e -> art_rel_static G e.
Proof. intros G [c w d b1 n|mb ms m b1 n|wb]; cbn; tauto. Qed.
#[using="Type"] Lemma art_rel_step_au : forall e G c, cl_au (rg_cls (art_rel_step e G) c) = cl_au (rg_cls G c).
Proof.
  intros [c0 w d b1 n|mb ms m b1 n|wb] G c; cbn [art_rel_step rg_cls]; [|reflexivity|].
  - unfold art_cls_upd. destruct (c =? c0) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. subst. apply art_cls_dealloc_au.
  - unfold art_cls_upd. destruct (c =? 24) eqn:E; [|reflexivity]. apply Z.eqb_eq in E. subst. apply art_cls_dealloc_au.
Qed.
#[using="Type"] Lemma art_rel_steps_au : forall es G c, cl_au (rg_cls (art_rel_steps es G) c) = cl_au (rg_cls G c).
Proof. induction es as [|e r IH]; intros G c; cbn [art_rel_steps fold_left]; [reflexivity|]. unfold art_rel_steps in IH. rewrite IH. apply art_rel_step_au. Qed.
#[using="Type"] Lemma art_rel_step_bl_in : forall e G x, In x (rg_bl (art_rel_step e G)) -> In x (rg_bl G).
Proof. intros [c0 w d b1 n|mb ms m b1 n|wb] G x; cbn [art_rel_step rg_bl]; [tauto| |tauto]. apply art_swap_remove_in. Qed.
#[using="Type"] Lemma art_rel_static_back : forall e G e', art_rel_static (art_rel_step e G) e' -> art_rel_static G e'.
Proof.
  intros e G [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_static]; rewrite ?art_rel_step_au; [tauto| |tauto].
  intros (H1 & H2). split; [eapply art_rel_step_bl_in; exact H1|exact H2].
Qed.
#[using="Type"] Lemma art_rels_pre_static : forall es G, art_rels_pre G es -> Forall (art_rel_static G) es.
Proof.
  induction es as [|e r IH]; intros G H; [constructor|]. destruct H as [H1 H2]. constructor; [apply art_rel_pre_static; exact H1|].
  eapply Forall_impl; [|exact (IH _ H2)]. intros e'. apply art_rel_static_back.
Qed.

(* [comment removed for export] *)
Definition art_rel_pzone (e : art_rel) : Z * Z :=
  match e with REP c w _ _ _ => (spb + c * 2 ^ 32 + 16 * w, AsanTab.class_size c) | RES _ _ m _ _ => (m, 8) | REB wb => (spb + 24 * 2 ^ 32 + 16 * wb, 8192) end.

#[using="Type"] Lemma art_rel_static_prot : forall nt G (M : word -> option byte) e, art_rcy_inv HI t ctx tp key tsd spb ris qs parr nt G M -> art_rel_static G e ->
  art_rcy_prot spb G (fst (art_rel_pzone e)) (snd (art_rel_pzone e)) /\ 0 < snd (art_rel_pzone e)
  /\ (forall zlo zlen, art_zapart e zlo zlen -> art_zapart e zlo zlen)
  /\ fst (art_rel_zone spb e) <= fst (art_rel_pzone e) /\ fst (art_rel_pzone e) + snd (art_rel_pzone e) <= fst (art_rel_zone spb e) + snd (art_rel_zone spb e).
Proof.
  intros nt G M e (ICLS & _) ST. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_static art_rel_pzone art_rel_zone fst snd] in *.
  - destruct ST as (Hc & (Hw0 & Hwsz & _) & _). destruct (ICLS c Hc) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
    pose proof (art_class_size_facts c Hc) as (Hsz & _).
    split; [left; exists c; split; [exact Hc|lia]|]. split; [lia|]. split; [tauto|]. lia.
  - destruct ST as (Hin & H1 & H2 & _). split; [right; exists (mb, ms); cbn [fst snd]; split; [exact Hin|lia]|]. split; [lia|]. split; [tauto|]. lia.
  - destruct ST as (Hw0 & Hwsz & _). destruct (ICLS 24 ltac:(lia)) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
    split; [left; exists 24; split; [lia|lia]|]. split; [lia|]. split; [tauto|]. lia.
Qed.

#[using="Type"] Lemma art_rel_mem_tr : forall G e (M M' : word -> option byte), art_rel_static G e ->
  (forall a (k : nat) v, fst (art_rel_pzone e) <= a -> a + Z.of_nat k <= fst (art_rel_pzone e) + snd (art_rel_pzone e) -> cellA M a k v -> cellA M' a k v) ->
  art_rel_mem spb e M -> art_rel_mem spb e M'.
Proof.
  intros G e M M' ST T MEM. destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_static art_rel_pzone art_rel_mem fst snd] in *; [| |exact I].
  - destruct ST as (Hc & _ & Hd & _ & Hdsz & _ & Hn). destruct MEM as (C1 & C2 & C3).
    assert (Hrs : 0 <= (n + 7) / 8 * 8). { pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as B. lia. }
    split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|]. intros NE. apply T; [lia|cbn; lia|exact (C3 NE)].
  - destruct MEM as (C1 & C2). split; [apply T; [lia|cbn; lia|exact C1]|apply T; [lia|cbn; lia|exact C2]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rcy_prot_step : forall G e zlo zlen, art_bl_geo HI t ctx spb parr G -> art_rel_geo G e -> 0 < zlen -> art_rcy_prot spb G zlo zlen -> art_zapart e zlo zlen ->
  art_rcy_prot spb (art_rel_step e G) zlo zlen.
Proof.
  intros G e zlo zlen (ISG & _) RG Hz PROT AP. destruct PROT as [K|(b & Hb & Z1 & Z2)]; [left; exact K|]. right. exists b. split; [|split; assumption].
  destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_step rg_bl]; [exact Hb| |exact Hb].
  cbn [art_rel_geo] in RG. pose proof (art_bl_idx_nth (rg_bl G) mb ms RG (art_sec_geo_inj HI t ctx parr (rg_bl G) ISG)) as Hnth.
  apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hnth; discriminate|exact Hb|].
  rewrite (nth_error_nth _ _ (0, 0) Hnth). intros ->. unfold art_zapart, apart in AP. cbn [art_rel_zone fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Definition art_rcy_tr (sp1 : Z) (G : art_rg) (es : list art_rel) (M M' : word -> option byte) : Prop :=
  (forall x : word, sp1 <= U x -> M' x = M x)
  /\ (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ Forall (fun e => art_zapart e a n) es) -> wrA M a n -> wrA M' a n)   (* [comment removed for export] *)
  /\ (forall zlo zlen, 0 < zlen -> art_rcy_prot spb G zlo zlen -> Forall (fun e => art_zapart e zlo zlen) es ->
        art_rcy_prot spb (art_rel_steps es G) zlo zlen
        /\ forall a (k : nat) v, zlo <= a -> a + Z.of_nat k <= zlo + zlen -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M' a k v)
  /\ art_agree (art_rels_fp sp1 G es) M M'.

#[using="Type"] Lemma art_rcy_tr_nil : forall sp1 G M, art_rcy_tr sp1 G [] M M.
Proof.
  intros sp1 G M. split; [intros; reflexivity|]. split; [intros; assumption|]. split; [|apply (art_agree_refl [])].
  intros zlo zlen _ P _. split; [exact P|]. intros; assumption.
Qed.

#[using="tp tsd qs GEO"] Lemma art_rcy_tr_one : forall sp1 G e (M M' : word -> option byte), art_rel_geo G e -> art_bl_geo HI t ctx spb parr G -> HI <= sp1 - 320 -> sp1 < 2 ^ 47 ->
  art_agree (art_rel_fp t spb ris parr sp1 G e) M M' ->
  (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ art_zapart e a n) -> wrA M a n -> wrA M' a n) ->
  art_rcy_tr sp1 G [e] M M'.
Proof.
  intros sp1 G e M M' RG BG HHI Hsp' AG WT.
  split. { intros x Hx. apply AG. eapply art_gap_out; [apply (art_rel_fp_above HI t ctx tp tsd spb ris qs parr GEO sp1 G e (U x) 1 RG BG HHI Hsp' Hx); lia|lia]. }
  split; [intros a n Ha Hn Hh Wa; apply (WT a n Ha Hn); [destruct Hh as [H|H]; [left; exact H|right; exact (Forall_inv H)]|exact Wa]|]. split; [|cbn [art_rels_fp]; rewrite app_nil_r; exact AG].
  intros zlo zlen Hz P Hf. apply Forall_inv in Hf. split.
  - cbn [art_rel_steps fold_left]. apply art_rcy_prot_step; assumption.
  - intros a k v Ha Hk Ha0 Hk' C. apply (art_cell_tr _ M M' a k v AG); [|exact Ha0|exact Hk'|exact C].
    apply (art_rel_fp_prot HI t ctx tp tsd spb ris qs parr GEO sp1 G e zlo zlen a (Z.of_nat k) RG BG HHI Hsp' Hz P Hf Ha Hk). lia.
Qed.

#[using="Type"] Lemma art_rcy_tr_app : forall sp1 G es1 es2 (M M1 M2 : word -> option byte), art_rcy_tr sp1 G es1 M M1 -> art_rcy_tr sp1 (art_rel_steps es1 G) es2 M1 M2 ->
  art_rcy_tr sp1 G (es1 ++ es2) M M2.
Proof.
  intros sp1 G es1 es2 M M1 M2 (F1 & W1 & P1 & A1) (F2 & W2 & P2 & A2).
  split; [intros x Hx; rewrite (F2 x Hx); apply F1; exact Hx|]. split.
  { intros a n Ha Hn Hh Wa. apply W2; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj2 (proj1 (Forall_app _ _ _) H))]|].
    apply W1; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj1 (proj1 (Forall_app _ _ _) H))]|exact Wa]. }
  split; [|rewrite art_rels_fp_app; eapply art_agree_trans; eassumption].
  intros zlo zlen Hz P Hf. apply Forall_app in Hf. destruct Hf as [Hf1 Hf2].
  destruct (P1 zlo zlen Hz P Hf1) as [P' T1]. destruct (P2 zlo zlen Hz P' Hf2) as [P'' T2].
  split; [rewrite art_rel_steps_app; exact P''|]. intros a k v Ha Hk Ha0 Hk' C. apply T2; try assumption. apply T1; assumption.
Qed.

(* [comment removed for export] *)
Definition art_rcy_trx (sp1 hi : Z) (G : art_rg) (es : list art_rel) (M M' : word -> option byte) : Prop :=
  (forall x : word, hi <= U x -> M' x = M x)
  /\ (forall a n, 0 <= a -> a + n < 2 ^ 64 -> (HI <= a \/ Forall (fun e => art_zapart e a n) es) -> wrA M a n -> wrA M' a n)   (* [comment removed for export] *)
  /\ (forall zlo zlen, 0 < zlen -> zlo + zlen <= HI -> art_rcy_prot spb G zlo zlen -> Forall (fun e => art_zapart e zlo zlen) es ->
        art_rcy_prot spb (art_rel_steps es G) zlo zlen
        /\ forall a (k : nat) v, zlo <= a -> a + Z.of_nat k <= zlo + zlen -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M' a k v)
  /\ art_agree (art_rels_fp sp1 G es ++ [(sp1, hi - sp1)]) M M'.

#[using="Type"] Lemma art_rcy_trx_of_tr : forall sp1 hi G es M M', sp1 <= hi -> art_rcy_tr sp1 G es M M' -> art_rcy_trx sp1 hi G es M M'.
Proof.
  intros sp1 hi G es M M' Hh (F & W & P & A). split; [intros x Hx; apply F; lia|]. split; [exact W|]. split; [intros zlo zlen Hz _ Pz Hf; exact (P zlo zlen Hz Pz Hf)|].
  eapply art_agree_sub; [exact A|]. intros z Hz H. apply art_out_app in H. tauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_rcy_trx_own : forall sp1 hi G (M M' : word -> option byte), HI <= sp1 -> sp1 <= hi -> mem_grows M M' -> art_agree [(sp1, hi - sp1)] M M' -> art_rcy_trx sp1 hi G [] M M'.
Proof.
  intros sp1 hi G M M' HHI Hh GW A.
  split. { intros x Hx. apply A. cbn [art_out fst snd]. split; [lia|exact I]. }
  split; [intros a n _ _ _ Wa; eapply wr_grows; [exact GW|exact Wa]|].
  split; [|cbn [art_rels_fp app]; exact A].
  intros zlo zlen Hz Hzh Pz _. split; [exact Pz|]. intros a k v Ha Hk Ha0 Hk' C.
  apply (art_cell_tr _ M M' a k v A); [cbn [art_gap fst snd]; split; [unfold apart; lia|exact I]|exact Ha0|exact Hk'|exact C].
Qed.

#[using="Type"] Lemma art_rcy_trx_app : forall sp1 hi G es1 es2 (M M1 M2 : word -> option byte), art_rcy_trx sp1 hi G es1 M M1 -> art_rcy_trx sp1 hi (art_rel_steps es1 G) es2 M1 M2 ->
  art_rcy_trx sp1 hi G (es1 ++ es2) M M2.
Proof.
  intros sp1 hi G es1 es2 M M1 M2 (F1 & W1 & P1 & A1) (F2 & W2 & P2 & A2).
  split; [intros x Hx; rewrite (F2 x Hx); apply F1; exact Hx|]. split.
  { intros a n Ha Hn Hh Wa. apply W2; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj2 (proj1 (Forall_app _ _ _) H))]|].
    apply W1; [exact Ha|exact Hn|destruct Hh as [H|H]; [left; exact H|right; exact (proj1 (proj1 (Forall_app _ _ _) H))]|exact Wa]. }
  split.
  - intros zlo zlen Hz Hzh P Hf. apply Forall_app in Hf. destruct Hf as [Hf1 Hf2].
    destruct (P1 zlo zlen Hz Hzh P Hf1) as [P' T1]. destruct (P2 zlo zlen Hz Hzh P' Hf2) as [P'' T2].
    split; [rewrite art_rel_steps_app; exact P''|]. intros a k v Ha Hk Ha0 Hk' C. apply T2; try assumption. apply T1; assumption.
  - eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. rewrite art_rels_fp_app. intros z Hz H.
    rewrite !art_out_app in H. rewrite !art_out_app. tauto.
Qed.

(* [comment removed for export] *)
Definition art_zsep (e e' : art_rel) : Prop := art_zapart e (fst (art_rel_zone spb e')) (snd (art_rel_zone spb e')).
#[using="Type"] Lemma art_rels_sep_app : forall l1 l2, art_rels_sep (l1 ++ l2) <-> art_rels_sep l1 /\ art_rels_sep l2 /\ Forall (fun e => Forall (art_zsep e) l2) l1.
Proof.
  induction l1 as [|e r IH]; intros l2; cbn [app art_rels_sep].
  - split; [intros H; split; [exact I|split; [exact H|constructor]]|tauto].
  - rewrite IH. rewrite Forall_app. split.
    + intros ((A & B) & C & D & E). split; [split; assumption|]. split; [exact D|]. constructor; assumption.
    + intros ((A & C) & D & E). pose proof (Forall_inv E) as E1. pose proof (Forall_inv_tail E) as E2. tauto.
Qed.

#[using="tp tsd ris qs GEO"] Lemma art_rcy_prot_below : forall G zlo zlen, art_bl_geo HI t ctx spb parr G -> art_rcy_prot spb G zlo zlen -> 0x696000 <= zlo /\ zlo + zlen <= HI.
Proof.
  intros G zlo zlen ((_ & _ & _ & _ & _ & _ & GB & _) & _) P.
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & _).
  destruct P as [(c' & Hc' & Z1 & Z2)|(b & Hb & Z1 & Z2)]; [lia|]. destruct (GB _ Hb) as (_ & _ & _ & B0 & B1 & _). lia.
Qed.

(* [comment removed for export] *)
#[using="GEO"] Lemma art_rels_mem_trx : forall nt sp1 hi G es es' (M M' : word -> option byte), art_rcy_inv HI t ctx tp key tsd spb ris qs parr nt G M ->
  Forall (art_rel_static G) es' -> Forall (fun e => Forall (art_zsep e) es') es -> art_rcy_trx sp1 hi G es M M' ->
  Forall (fun e' => art_rel_mem spb e' M) es' -> Forall (fun e' => art_rel_mem spb e' M') es'.
Proof.
  intros nt sp1 hi G es es' M M' INV ST SEP (_ & _ & P & _) MEM. apply Forall_forall. intros e' Hin.
  pose proof (proj1 (Forall_forall _ _) ST e' Hin) as Se. pose proof (proj1 (Forall_forall _ _) MEM e' Hin) as Me.
  destruct (art_rel_static_prot nt G M e' INV Se) as (Pz & Hz & _ & Z1 & Z2).
  pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ISG & IBK & IPK).
  destruct (art_rcy_prot_below G _ _ (conj ISG (conj IBK IPK)) Pz) as (Lo & Hi).
  assert (Hf : Forall (fun e => art_zapart e (fst (art_rel_pzone e')) (snd (art_rel_pzone e'))) es).
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) SEP e He) e' Hin) as Ap. unfold art_zsep, art_zapart, apart in *. lia. }
  destruct (P _ _ Hz Hi Pz Hf) as (_ & T).
  apply (art_rel_mem_tr G e' M M' Se); [|exact Me]. intros a k v Ha Hk C. apply T; [exact Ha|exact Hk|lia| |exact C].
  pose proof GEO as (G1 & G2 & _). lia.
Qed.
End Tr.
