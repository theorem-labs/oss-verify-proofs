(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_unwind_defs R_asan_malloc R_asan_free RT_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fp_bad (f lim : Z) : Prop := f < lim \/ f mod 8 <> 0 \/ 2 ^ 63 <= f.

(* [comment removed for export] *)
Fixpoint chain_inv (lim f : Z) (ch : list (Z * Z)) : Prop :=
  match ch with
  | [] => fp_bad f lim
  | (_, fp) :: ch' => lim + 16 <= f /\ f + 16 <= USTACK_TOP /\ chain_inv f fp ch'
  end.

Lemma fr_ok_bad : forall lim hi f, hi <= 2 ^ 63 -> fp_bad f lim -> fr_ok lim hi f = false.
Proof.
  intros lim hi f Hhi [H|[H|H]]; unfold fr_ok.
  - rewrite (proj2 (Z.ltb_ge lim f)) by lia. reflexivity.
  - rewrite (proj2 (Z.eqb_neq (f mod 8) 0)) by exact H. rewrite !andb_false_r. reflexivity.
  - rewrite (proj2 (Z.ltb_ge f hi)) by lia. rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma uw_loop_prefix : forall pc page hi maxd ch lim f ra acc,
  hi <= 2 ^ 63 -> page <= ra -> ra <> pc ->
  Forall (fun rf => page <= fst rf /\ fst rf <> pc) ch ->
  Z.of_nat (length acc) <= maxd ->
  chain_inv lim f ch ->
  exists pre, lprefix pre (ra :: map fst ch)
    /\ uw_loop pc page hi maxd ((ra, f) :: ch) lim acc = Some (acc ++ pre)
    /\ Z.of_nat (length (acc ++ pre)) <= maxd.
Proof.
  intros pc page hi maxd ch. induction ch as [|[ra1 fp1] ch IH]; intros lim f ra acc Hhi Hra Hne Hall Hlen Hinv.
  - cbn [chain_inv] in Hinv. cbn [uw_loop].
    destruct (Z.leb_spec maxd (Z.of_nat (length acc))) as [Hm|Hm].
    + exists []. split; [exact I|]. rewrite app_nil_r. split; [reflexivity| exact Hlen].
    + rewrite (proj2 (Z.ltb_ge ra page)) by lia.
      rewrite (proj2 (Z.eqb_neq ra pc)) by exact Hne. rewrite (fr_ok_bad lim hi f Hhi Hinv).
      exists [ra]. split; [cbn [lprefix]; split; [reflexivity| exact I]|]. split; [reflexivity|].
      rewrite length_app. cbn [length]. lia.
  - cbn [chain_inv] in Hinv. destruct Hinv as (H1 & H2 & Hinv').
    inversion Hall as [|? ? [Hra1 Hne1] Hall']; subst. cbn [fst] in Hra1, Hne1.
    change (uw_loop pc page hi maxd ((ra, f) :: (ra1, fp1) :: ch) lim acc)
      with (if maxd <=? Z.of_nat (length acc) then Some acc
            else if ra <? page then Some acc
            else let acc' := if ra =? pc then acc else acc ++ [ra] in
                 if fr_ok lim hi f then uw_loop pc page hi maxd ((ra1, fp1) :: ch) f acc' else Some acc').
    destruct (Z.leb_spec maxd (Z.of_nat (length acc))) as [Hm|Hm].
    + exists []. split; [exact I|]. rewrite app_nil_r. split; [reflexivity| exact Hlen].
    + rewrite (proj2 (Z.ltb_ge ra page)) by lia.
      rewrite (proj2 (Z.eqb_neq ra pc)) by exact Hne. cbv zeta.
      assert (Hl' : Z.of_nat (length (acc ++ [ra])) <= maxd) by (rewrite length_app; cbn [length]; lia).
      destruct (fr_ok lim hi f).
      * destruct (IH f fp1 ra1 (acc ++ [ra]) Hhi Hra1 Hne1 Hall' Hl' Hinv') as (pre & Hpre & Hloop & Hle).
        exists (ra :: pre). split; [cbn [map fst lprefix] in *; split; [reflexivity| exact Hpre]|].
        rewrite Hloop, <- app_assoc. cbn [app]. split; [reflexivity|]. rewrite <- app_assoc in Hle. exact Hle.
      * exists [ra]. split; [cbn [lprefix]; split; [reflexivity| exact I]|]. split; [reflexivity| exact Hl'].
Qed.

(* [comment removed for export] *)
Lemma trace_k_cases : forall pc bot top usp ra f ch, 4096 <= top -> top <= 2 ^ 63 ->
  4096 <= ra -> ra <> pc -> Forall (fun rf => 4096 <= fst rf /\ fst rf <> pc) ch ->
  chain_inv usp f ch ->
  exists tr pre, unwind_trace pc 4096 bot top 30 usp ((ra, f) :: ch) = Some tr
    /\ lprefix pre (ra :: map fst ch) /\ tr = pc :: pre /\ (length pre <= 29)%nat.
Proof.
  intros pc bot top usp ra f ch H1 H2 Hra Hne Hall Hinv.
  unfold unwind_trace. rewrite (proj2 (Z.eqb_neq (top / 4096) 0)) by (Z.div_mod_to_equations; lia).
  destruct (fr_ok bot (top - 16) usp).
  - destruct (uw_loop_prefix pc 4096 (top - 16) 30 ch usp f ra [pc] ltac:(lia) Hra Hne Hall ltac:(cbn [length Z.of_nat]; lia) Hinv)
      as (pre & Hpre & Hloop & Hle).
    exists ([pc] ++ pre), pre. split; [exact Hloop|]. split; [exact Hpre|]. split; [reflexivity|].
    rewrite length_app in Hle. cbn [length] in Hle. lia.
  - exists [pc], []. split; [reflexivity|]. split; [exact I|]. split; [reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fp_invalid_bad : forall s0 lim : word, fp_invalid s0 lim -> fp_bad (bv_unsigned s0) (bv_unsigned lim).
Proof. intros s0 lim H. exact H. Qed.

Lemma u64r : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn [Z.of_N] in H. exact H. Qed.

(* [comment removed for export] *)
Definition fp_below (W : list (Z * Z)) (lim : Z) : Prop := Forall (fun r => snd r <= lim) W.

Lemma disjoint_from_below : forall W lim a n, fp_below W lim -> lim <= a -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros lim a n HW Ha; cbn [disjoint_from]; [exact I|].
  inversion HW as [|? ? Hr HW']; subst. cbn [snd] in Hr. split; [lia| exact (IH lim a n HW' Ha)].
Qed.

Lemma fp_below_mono : forall W lim lim', fp_below W lim -> lim <= lim' -> fp_below W lim'.
Proof. intros W lim lim' H Hle. eapply Forall_impl; [|exact H]. cbv beta. intros r Hr. lia. Qed.

Lemma uw_chain_ghost : forall W m ras (lim f : word),
  Forall (fun ra => 0 <= ra < 2 ^ 64) ras ->
  fp_below W (bv_unsigned lim) ->
  uw_chain m lim f ras ->
  exists ch, map fst ch = ras /\ chain_cells W m (bv_unsigned f) ch /\ chain_inv (bv_unsigned lim) (bv_unsigned f) ch.
Proof.
  intros W m ras. induction ras as [|ra ras IH]; intros lim f Hr HW H.
  - exists []. split; [reflexivity|]. split; [exact I| exact (fp_invalid_bad f lim H)].
  - cbn [uw_chain] in H. destruct H as (H1 & H2 & fp' & Hc & Hrest).
    inversion Hr as [|? ? Hra Hr']; subst.
    destruct (IH f fp' Hr' (fp_below_mono W (bv_unsigned lim) (bv_unsigned f) HW ltac:(lia)) Hrest) as (ch & Hm & Hcc & Hinv).
    exists ((ra, bv_unsigned fp') :: ch). split; [cbn [map fst]; rewrite Hm; reflexivity|]. split.
    + cbn [chain_cells]. rewrite Z_to_bv_bv_unsigned.
      replace (bv_unsigned f + -16) with (bv_unsigned f - 16) by lia.
      split; [exact Hc|]. split; [split; [exact Hra| split; [apply u64r| pose proof (u64r f); pose proof (u64r lim); lia]]|].
      split; [apply (disjoint_from_below W (bv_unsigned lim)); [exact HW| lia]| exact Hcc].
    + cbn [chain_inv]. split; [exact H1|]. split; [exact H2| exact Hinv].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma alloc_pcs : map snd ALLOC_EPS = [PC_MALLOC; PC_FREE; PC_REALLOC; PC_MEMALIGN].
Proof. reflexivity. Qed.

Lemma alloc_eps_pc_range : forall E pc, In (E, pc) ALLOC_EPS -> 0 <= pc < 2 ^ 64.
Proof.
  intros E pc H. unfold ALLOC_EPS, PC_MALLOC, PC_FREE, PC_REALLOC, PC_MEMALIGN in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.

(* [comment removed for export] *)
Lemma alloc_ras_facts : forall ra, In ra ALLOC_RAS -> cg_site_ok (map snd ALLOC_EPS) ra.
Proof.
  intros ra HRA. unfold cg_site_ok. rewrite alloc_pcs. unfold ALLOC_RAS, PC_MALLOC, PC_FREE, PC_REALLOC, PC_MEMALIGN in *.
  repeat (destruct HRA as [<-|HRA]; [split; [lia|]; cbn [In]; intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]).
  destruct HRA.
Qed.

Lemma site_ok_ne : forall E pc r, In (E, pc) ALLOC_EPS -> cg_site_ok (map snd ALLOC_EPS) r -> 4096 <= r < 2 ^ 64 /\ r <> pc.
Proof.
  intros E pc r H [R N]. split; [exact R|]. intros ->. apply N. apply in_map_iff. exists (E, pc). split; [reflexivity| exact H].
Qed.

(* [comment removed for export] *)
Definition uw_tr_shape (cg : cgraph) (E pc : Z) (tr : list Z) : Prop :=
  In (E, pc) ALLOC_EPS /\ cg_wf cg ALLOC_EPS ALLOC_RAS N_TR
  /\ (tr = [pc]
      \/ (exists ra, In ra ALLOC_RAS /\ tr = [pc; ra])
      \/ (exists ch r t, cg_ctx cg E ch /\ lprefix (r :: t) ch /\ (length t <= 28)%nat /\ tr = pc :: r :: t)).

Lemma uw_tr_shape_main : forall cg E pc tr, uw_tr_shape cg E pc tr ->
  In tr (T_MAIN cg) /\ (1 <= length tr <= 30)%nat /\ Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros cg E pc tr (HE & WF & HS). pose proof (alloc_eps_pc_range E pc HE) as Rpc. unfold T_MAIN.
  destruct HS as [-> | [(ra & HRA & ->) | (ch & r & t & HC & HP & Hl & ->)]].
  - split; [exact (cg_traces_pc cg ALLOC_EPS ALLOC_RAS E pc HE)|]. split; [cbn; lia| constructor; [exact Rpc| constructor]].
  - destruct (alloc_ras_facts ra HRA) as (R & _). split; [exact (cg_traces_drv cg ALLOC_EPS ALLOC_RAS E pc ra HE HRA)|].
    split; [cbn; lia| constructor; [exact Rpc| constructor; [lia| constructor]]].
  - split; [exact (cg_traces_chain cg ALLOC_EPS ALLOC_RAS E pc ch r t HE HC HP Hl)|].
    split; [cbn [length]; lia|]. constructor; [exact Rpc|].
    apply (lprefix_Forall _ (r :: t) ch); [|exact HP].
    eapply Forall_impl; [|exact (cg_ctx_sites_ok cg ALLOC_EPS ALLOC_RAS N_TR E ch WF HC)]. cbv beta. intros a (Ra & _). lia.
Qed.

Arguments uw_tr_shape_main {cg E pc} tr _.

(* [comment removed for export] *)
Lemma unwind_ok_trace : forall cg E pc W m (ra s0 sp : word) bot top,
  In (E, pc) ALLOC_EPS -> cg_wf cg ALLOC_EPS ALLOC_RAS N_TR -> 4096 <= top -> top <= 2 ^ 63 ->
  fp_below W (bv_unsigned sp) ->
  unwind_ok cg E m ra s0 sp ->
  exists ch tr, chain_cells W m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ uw_tr_shape cg E pc tr.
Proof.
  intros cg E pc W m ra s0 sp bot top HE WF Ht1 Ht2 HW HU.
  destruct HU as [(HRA & HS0) | (ras & HC & HUW)].
  - destruct (site_ok_ne E pc _ HE (alloc_ras_facts _ HRA)) as (Rra & Hne).
    destruct (trace_k_cases pc bot top (bv_unsigned sp) (bv_unsigned ra) (bv_unsigned s0) [] Ht1 Ht2 ltac:(lia) Hne
                ltac:(constructor) (fp_invalid_bad s0 sp HS0)) as (tr & pre & HTR & Hpre & -> & _).
    exists [], (pc :: pre). split; [exact I|]. split; [exact HTR|]. split; [exact HE|]. split; [exact WF|].
    cbn [map] in Hpre. destruct pre as [|x pre]; [left; reflexivity|]. destruct Hpre as [-> Hpre].
    destruct pre; [|destruct Hpre]. right; left. exists (bv_unsigned ra). split; [exact HRA| reflexivity].
  - pose proof (cg_ctx_sites_ok cg ALLOC_EPS ALLOC_RAS N_TR E _ WF HC) as Hall.
    inversion Hall as [|? ? Hra Hall']; subst.
    destruct (site_ok_ne E pc _ HE Hra) as (Rra & Hne).
    destruct (uw_chain_ghost W m ras sp s0) as (ch & Hmap & Hcc & Hinv);
      [eapply Forall_impl; [|exact Hall']; cbv beta; intros a (R & _); lia| exact HW| exact HUW|].
    destruct (trace_k_cases pc bot top (bv_unsigned sp) (bv_unsigned ra) (bv_unsigned s0) ch Ht1 Ht2 ltac:(lia) Hne) as (tr & pre & HTR & Hpre & -> & Hl);
      [| exact Hinv|].
    { apply Forall_forall. intros [r fp] Hin. cbn [fst].
      assert (Hr : In r ras) by (rewrite <- Hmap; apply (in_map fst _ _ Hin)).
      destruct (site_ok_ne E pc r HE (proj1 (Forall_forall _ _) Hall' r Hr)) as (X1 & X2). split; [lia| exact X2]. }
    exists ch, (pc :: pre). split; [exact Hcc|]. split; [exact HTR|]. split; [exact HE|]. split; [exact WF|].
    rewrite Hmap in Hpre. destruct pre as [|r t]; [left; reflexivity|].
    right; right. exists (bv_unsigned ra :: ras), r, t. split; [exact HC|]. split; [exact Hpre|]. split; [cbn [length] in Hl; lia| reflexivity].
Qed.
