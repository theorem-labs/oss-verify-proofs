(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac StoreFast.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import RT_iface RT_traces RT_gaps_iface D_kit LeptTac.
From stdpp Require list_basics.
Import ListNotations.
Open Scope Z_scope.

Lemma asegs_below : segs_below_b asegs SEGTOP_A = true.
Proof. lazy. reflexivity. Qed.
Lemma asegs_wx : wx_segs_nowrap asegs.
Proof. apply wx_segs_nowrap_of_b. lazy. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asegs_w_r : forallb (fun seg => negb (seg_writable seg) || seg_readable seg) asegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; eapply IH; eassumption].
Qed.

Lemma wview_mrd_A : forall (m : mem) a, wview asegs m a <> None -> exists b, mrd asegs m a = Some b.
Proof.
  intros m a H. unfold wview, mrd in *. destruct (m a) as [b|]; [exists b; reflexivity|].
  unfold seg_rom, memory_read.
  destruct (find_segment asegs (bv_unsigned a) 1) as [seg|] eqn:FS; [| contradiction].
  change (Z.of_N 1) with 1. rewrite FS.
  pose proof (find_segment_in _ _ _ _ FS) as IN.
  pose proof asegs_w_r as W. rewrite forallb_forall in W. specialize (W seg IN).
  destruct (seg_writable seg) eqn:SW; [| contradiction]. cbn in W. rewrite W.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at _ _) as [b|]; [| contradiction]. exists b. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wr_at_stk : forall (m : mem) d n, wr_at asegs m d n -> stk asegs m d (d + n).
Proof.
  intros m d n (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  assert (W : wview asegs m (wa a) <> None) by (replace a with (d + (a - d)) by lia; apply H; lia).
  split; [exact W| exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_rw_CB : forall (m : mem) d n, wr_at asegs m d n -> 0 <= n -> exists junk, rw_cells asegs m d [CB (Z.to_nat n) junk].
Proof.
  intros m d n W N0. pose proof (wr_at_stk m d n W) as S.
  destruct (stk_carve asegs m d (d + n) (Z.to_nat n) S ltac:(lia)) as [_ (junk & FR)].
  exists junk. replace (d + n - Z.of_nat (Z.to_nat n)) with d in FR by lia. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wr_at_app : forall (m : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at asegs m a (n1 + n2) <-> wr_at asegs m a n1 /\ wr_at asegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall (m : mem) A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

Lemma rw_cells_head : forall (m : mem) A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. exact (proj1 (proj1 (rw_cells_app m A [c] cs) H)). Qed.

Lemma rw_cells_tail : forall (m : mem) A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. pose proof (proj2 (proj1 (rw_cells_app m A [c] cs) H)) as H2. cbn [cells_size Nat.add] in H2.
  rewrite Nat.add_0_r in H2. exact H2. Qed.

Lemma wr_at_sub : forall (m : mem) a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H1 H2 H3. split; [lia| split; [lia|]].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

Lemma wr_at_rw_C1 : forall (m : mem) a, wr_at asegs m a 1 -> exists b, rw_cells asegs m a [C1 b].
Proof.
  intros m a W. destruct (wr_at_rw_CB m a 1 W ltac:(lia)) as (junk & H).
  destruct H as [[W1 B] R]. cbn in W1. destruct junk as [|b [|? ?]]; cbn in W1; try (destruct W1; discriminate).
  exists b. split; [split; [cbn; split; [reflexivity| exact I]| exact B]| exact R].
Qed.


Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma PMc_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof using AF. intros Σ PMc H. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact H]. Qed.

Lemma asta_evt' : forall Σ PMc Pm Q, mat_stable PMc -> (forall ms, Pm ms -> evt asegs Q ms) ->
  cps asegs (ASTA RT Σ PMc Pm) (ASTA RT Σ PMc Q).
Proof using AF.
  intros Σ PMc Pm Q HM H. unfold ASTA.
  apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable; exact HM| exact H].
Qed.

(* [comment removed for export] *)
Lemma cps_walk_lemma : forall Σ PMc ms Q, mat_stable PMc ->
  evt asegs (fun ms' => cps asegs (ASTA RT Σ PMc (eq ms')) Q) ms -> cps asegs (ASTA RT Σ PMc (eq ms)) Q.
Proof using AF.
  intros Σ PMc ms Q HM H T c Hc Hk.
  pose proof (asta_evt' Σ PMc (eq ms) (fun ms' => cps asegs (ASTA RT Σ PMc (eq ms')) Q) HM ltac:(intros ? <-; exact H)) as W.
  apply (W T c Hc). intros c' Hc'.
  destruct Hc' as (H1 & H2 & H3 & H4).
  apply (H2 T c'); [| exact Hk]. split; [exact H1|]. split; [reflexivity|]. split; [exact H3| exact H4].
Qed.

(* [comment removed for export] *)
Lemma cps_ex_l : forall {X} (P : X -> config -> Prop) Q, (forall x, cps asegs (P x) Q) -> cps asegs (fun c => exists x, P x c) Q.
Proof. intros X P Q H. apply cps_ex. exact H. Qed.
Lemma cps_and_pure_r : forall (P : config -> Prop) (phi : Prop) Q, (phi -> cps asegs P Q) -> cps asegs (fun c => P c /\ phi) Q.
Proof. intros P phi Q H. apply cps_pure. exact H. Qed.
Lemma cps_ASTA_ex : forall {X} Σ PMc (Pm : X -> machine_state -> Prop) Q,
  (forall x, cps asegs (ASTA RT Σ PMc (Pm x)) Q) -> cps asegs (ASTA RT Σ PMc (fun ms => exists x, Pm x ms)) Q.
Proof. intros X Σ PMc Pm Q H. unfold ASTA in *. apply cps_AST_ex. exact H. Qed.
Lemma cps_ASTA_pure_r : forall Σ PMc Pm (phi : Prop) Q,
  (phi -> cps asegs (ASTA RT Σ PMc Pm) Q) -> cps asegs (ASTA RT Σ PMc (fun ms => Pm ms /\ phi)) Q.
Proof. intros Σ PMc Pm phi Q H. unfold ASTA in *. apply cps_AST_pure. exact H. Qed.
Lemma cps_ASTA_pure_l : forall Σ PMc Pm (phi : Prop) Q,
  (phi -> cps asegs (ASTA RT Σ PMc Pm) Q) -> cps asegs (ASTA RT Σ PMc (fun ms => phi /\ Pm ms)) Q.
Proof.
  intros Σ PMc Pm phi Q H. eapply cps_conseq; [apply (cps_ASTA_pure_r Σ PMc Pm phi Q H)| | auto].
  intros c Hc. unfold ASTA in *. eapply AST_conseq; [exact Hc| | auto]. intros ms [H1 H2]. split; assumption.
Qed.
Lemma cps_ASTA_eq_sym : forall Σ PMc ms0 Q,
  cps asegs (ASTA RT Σ PMc (eq ms0)) Q -> cps asegs (ASTA RT Σ PMc (fun ms => ms = ms0)) Q.
Proof.
  intros Σ PMc ms0 Q H. eapply cps_conseq; [exact H| | auto].
  intros c Hc. unfold ASTA in *. eapply AST_conseq; [exact Hc| | auto]. intros ms E. symmetry. exact E.
Qed.
Lemma cps_ASTA_conseq : forall Σ PMc (Pm Pm' : machine_state -> Prop) Q,
  cps asegs (ASTA RT Σ PMc Pm) Q -> (forall ms, Pm' ms -> Pm ms) -> cps asegs (ASTA RT Σ PMc Pm') Q.
Proof.
  intros Σ PMc Pm Pm' Q H HP. eapply cps_conseq; [exact H| | auto].
  intros c Hc. unfold ASTA in *. eapply AST_conseq; [exact Hc| exact HP| auto].
Qed.

(* [comment removed for export] *)
Fixpoint ivls_client (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> aclient live frames sp x) /\ ivls_client live frames sp W'
  end.

Lemma outside_or_client : forall live frames sp W x, ivls_client live frames sp W -> outside W x \/ aclient live frames sp x.
Proof.
  intros live frames sp W x. induction W as [|[lo hi] W IH]; intros H; cbn in *; [left; exact I|].
  destruct H as [H1 H2]. destruct (IH H2) as [HO|HC]; [| right; exact HC].
  destruct (Z_le_dec lo x) as [L|L]; [destruct (Z_lt_dec x hi) as [U|U]|].
  - right. apply H1. lia.
  - left. split; [lia| exact HO].
  - left. split; [lia| exact HO].
Qed.

Lemma art_client_writes : forall Σ (m m' : mem) (sp : Z) W, ART RT Σ m -> munch W m m' -> wmono asegs m m' ->
  rt_sp0 RT Σ - STACK_WIN <= sp -> ivls_client (rt_live RT Σ) (rt_frames RT Σ) sp W -> ART RT Σ m'.
Proof using AF.
  intros Σ m m' sp W HA MU WM Hsp HW. apply (af_frame RT AF Σ m m' sp HA Hsp); [| exact WM].
  intros a Ha. apply MU. destruct (outside_or_client _ _ _ W (bv_unsigned a) HW) as [H|H]; [exact H| contradiction].
Qed.

(* [comment removed for export] *)
Lemma live_remove_sub : forall (l : list (Z * Z)) p e, In e (live_remove p l) -> In e l.
Proof.
  intros l p e He. unfold live_remove in He. apply stdpp.base.list_elem_of_In in He.
  apply stdpp.list_basics.list.list_elem_of_filter in He. apply stdpp.base.list_elem_of_In. exact (proj2 He).
Qed.
Lemma live_remove_keep : forall (l : list (Z * Z)) p e, In e l -> fst e <> p -> In e (live_remove p l).
Proof.
  intros l p e He Hp. unfold live_remove. apply stdpp.base.list_elem_of_In. apply stdpp.list_basics.list.list_elem_of_filter.
  split; [| apply stdpp.base.list_elem_of_In; exact He]. apply Z.eqb_neq in Hp. rewrite Hp. exact I.
Qed.

(* [comment removed for export] *)
Lemma acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> acc asegs m p n.
Proof using AF. intros Σ m p n H1 H2. exact (proj2 (af_acc_live RT AF Σ m p n H1 H2)). Qed.

(* [comment removed for export] *)
Lemma ushadow_length : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = (n + 7) / 8.
Proof.
  intros n Hn. unfold ushadow. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length]; rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia);
    Z.div_mod_to_equations; lia.
Qed.
Definition own_live (live : list (Z * Z)) (a n : Z) : Prop := exists p k, In (p, k) live /\ p <= a /\ a + n <= p + k.
Definition own_frame (frames : list (Z * nat)) (m : mem) (a n : Z) : Prop :=
  exists f k, In (f, k) frames /\ f <= a /\ a + n <= f + fs_size k - 8 /\ a mod 8 = 0 /\ 0 <= a /\ a + n + 8 <= 2^47
              /\ bytes_at asegs m (shad a) (ushadow n).
Definition accok (live : list (Z * Z)) (frames : list (Z * nat)) (m : mem) (a n : Z) : Prop :=
  own_live live a n \/ own_frame frames m a n.

Lemma accok_acc : forall Σ m a n, ART RT Σ m -> 0 <= n -> accok (rt_live RT Σ) (rt_frames RT Σ) m a n -> acc asegs m a n.
Proof using AF.
  intros Σ m a n HA Hn [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)].
  - apply (acc_sub asegs m p k); [exact (acc_live Σ m p k HA Hin)| lia| lia].
  - exact (acc_ushadow asegs m a n H8 H0 Hn Hb).
Qed.

Lemma accok_acc' : forall Σ m lv frs a n, ART RT Σ m -> 0 <= n -> rt_live RT Σ = lv -> rt_frames RT Σ = frs ->
  accok lv frs m a n -> acc asegs m a n.
Proof using AF. intros Σ m lv frs a n HA Hn <- <- H. exact (accok_acc Σ m a n HA Hn H). Qed.

Lemma accok_aclient : forall live frames m sp a n x, accok live frames m a n -> a <= x < a + n -> aclient live frames sp x.
Proof.
  intros live frames m sp a n x [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)] Hx.
  - right; right; left. exists p, k. split; [exact Hin| lia].
  - right; right; right; left. exists f, k. split; [exact Hin| lia].
Qed.

Lemma aclient_mono : forall live frames sp live' frames' sp' a,
  aclient live frames sp a -> (forall e, In e live -> In e live') -> (forall e, In e frames -> In e frames') -> sp' <= sp ->
  aclient live' frames' sp' a.
Proof.
  intros live frames sp live' frames' sp' a H HL HF Hsp. destruct H as [H|[H|[H|[H|H]]]].
  - left. lia.
  - right; left. exact H.
  - right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [apply HL; exact Hin| exact Hp].
  - right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
  - right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [apply HF; exact Hin| exact Hf].
Qed.

Lemma accok_mono : forall lv frs lv' frs' (m : mem) a n, accok lv frs m a n ->
  (forall e, In e lv -> In e lv') -> (forall e, In e frs -> In e frs') -> accok lv' frs' m a n.
Proof.
  intros lv frs lv' frs' m a n [(p & k & Hin & H)|(f & k & Hin & H)] HL HF.
  - left. exists p, k. split; [exact (HL _ Hin)| exact H].
  - right. exists f, k. split; [exact (HF _ Hin)| exact H].
Qed.
Lemma accok_acc_sub : forall Σ m lv frs a n, ART RT Σ m -> 0 <= n ->
  (forall e, In e lv -> In e (rt_live RT Σ)) -> (forall e, In e frs -> In e (rt_frames RT Σ)) ->
  accok lv frs m a n -> acc asegs m a n.
Proof using AF. intros Σ m lv frs a n HA Hn HL HF H. exact (accok_acc Σ m a n HA Hn (accok_mono _ _ _ _ m a n H HL HF)). Qed.

(* [comment removed for export] *)
Lemma accok_keep_sub : forall live frames (m m' : mem) live' frames' sp a n, accok live frames m a n ->
  agree_on (aclient live' frames' sp) m m' -> 0 <= n ->
  (forall e, In e frames -> In e frames') -> accok live frames m' a n.
Proof.
  intros live frames m m' live' frames' sp a n [H|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn HF; [left; exact H| right].
  exists f, k. repeat (split; [first [assumption | lia]|]).
  apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
  rewrite (ushadow_length n Hn) in Hx.
  right; right; right; right. exists f, k. split; [exact (HF _ Hin)|]. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma accok_keep_fp : forall live frames (m m' : mem) live' frames' sp W a n, accok live frames m a n ->
  agree_on (fun x => aclient live' frames' sp x /\ outside W x) m m' -> 0 <= n ->
  (forall e, In e frames -> In e frames') -> (forall x, shad a <= x < shad a + (n + 7) / 8 -> outside W x) ->
  accok live frames m' a n.
Proof.
  intros live frames m m' live' frames' sp W a n [H|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn HF HW; [left; exact H| right].
  exists f, k. repeat (split; [first [assumption | lia]|]).
  apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
  rewrite (ushadow_length n Hn) in Hx. split; [| apply HW; exact Hx].
  right; right; right; right. exists f, k. split; [exact (HF _ Hin)|]. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma accok_write_out : forall live frames (m : mem) x bs a n (k : Z),
  Z.of_nat (length bs) = k -> 0 <= x -> x + k <= 2^64 -> 0 <= n ->
  accok live frames m a n -> (x + k <= 2147450880 \/ 17594333495296 <= x) ->
  accok live frames (write_to_mem m (wa x) bs) a n.
Proof.
  intros live frames m x bs a n k Hk Hx Hl Hn [H|(f & kf & Hin & H1 & H2 & H8 & H0 & HT & Hb)] Hd; [left; exact H| right].
  exists f, kf. repeat (split; [first [assumption | lia]|]).
  apply (bytes_at_write_other_n asegs m x bs _ _ k Hk Hx Hl Hb). rewrite (ushadow_length n Hn).
  pose proof (shad_range a ltac:(lia)). assert (shad a + (n + 7) / 8 <= 17594333495296) by (unfold shad, SHB; Z.div_mod_to_equations; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma accok_keep : forall live frames (m m' : mem) live' sp a n, accok live frames m a n ->
  agree_on (aclient live' frames sp) m m' -> 0 <= n ->
  (forall p k, In (p, k) live -> p <= a -> a + n <= p + k -> In (p, k) live') ->
  accok live' frames m' a n.
Proof.
  intros live frames m m' live' sp a n [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn HL.
  - left. exists p, k. split; [exact (HL p k Hin H1 H2)| lia].
  - right. exists f, k. repeat (split; [first [assumption | lia]|]).
    apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    rewrite (ushadow_length n Hn) in Hx.
    right; right; right; right. exists f, k. split; [exact Hin|]. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

Lemma client_static_below : forall a, client_static a -> a < SEGTOP_A.
Proof.
  intros a ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma client_static_ge : forall a, client_static a -> 0x10000 <= a.
Proof.
  intros a ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma aclient_split : forall Σ m usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m usp a ART0 [H|[H|[H|[H|H]]]].
  - left; lia.
  - right. pose proof (client_static_below a H). pose proof (af_sp0_range RT AF Σ m ART0). unfold SEGTOP_A, STACK_WIN in *. lia.
  - right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0).
    unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma new_frame_apart : forall Σ' (m : mem) f k frs live0 usp a,
  ART RT Σ' m -> rt_frames RT Σ' = (f, k) :: frs -> (forall e, In e live0 -> In e (rt_live RT Σ')) ->
  usp <= rt_sp0 RT Σ' -> rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a ->
  (a < f \/ f + fs_size k <= a) /\ (a < shad f \/ shad (f + fs_size k) <= a).
Proof using AF.
  intros Σ' m f k frs live0 usp a HA FRS LV SPU SPL Ha.
  assert (INF : In (f, k) (rt_frames RT Σ')) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ' m f k HA INF) as (F0 & FHI & FSEG & FLV).
  pose proof (af_frames_hi RT AF Σ' m f k HA INF) as FSH.
  pose proof (af_fshadow_apart RT AF Σ' m f k HA INF) as (SA1 & SA2).
  pose proof (af_frames_align RT AF Σ' m f k HA INF) as (F64 & _).
  pose proof (af_sp0_range RT AF Σ' m HA) as SP0R. pose proof (af_sp0_win RT AF Σ' m HA) as SP0W.
  assert (FS0 : 64 <= fs_size k) by (unfold fs_size; rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k)); nia).
  assert (FS64 : fs_size k mod 64 = 0).
  { unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; [right; lia|]. right. unfold shad, SHB. Z.div_mod_to_equations. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    split; [lia|]. left. unfold shad, SHB. Z.div_mod_to_equations. lia.
  - destruct H as (p & n & Hin & Hp). pose proof (LV _ Hin) as Hin'. split; [specialize (FLV p n Hin'); lia|].
    specialize (SA1 p n Hin'). lia.
  - destruct H as (f' & k' & Hin & Hf).
    assert (Hin' : In (f', k') ([] ++ frs)) by exact Hin.
    pose proof (af_frames_disj RT AF Σ' m f k f' k' [] frs HA FRS Hin') as D.
    split; [lia|]. specialize (SA2 f' k' ltac:(rewrite FRS; right; exact Hin)). lia.
  - destruct H as (f' & k' & Hin & Hf).
    assert (INF' : In (f', k') (rt_frames RT Σ')) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ' m f' k' HA INF') as (_ & SB2). specialize (SB2 f k INF).
    split; [lia|].
    assert (Hin' : In (f', k') ([] ++ frs)) by exact Hin.
    pose proof (af_frames_disj RT AF Σ' m f k f' k' [] frs HA FRS Hin') as D.
    pose proof (af_frames_align RT AF Σ' m f' k' HA INF') as (F64' & _).
    pose proof (af_frames_range RT AF Σ' m f' k' HA INF') as (F0' & _).
    assert (FS64' : fs_size k' mod 64 = 0).
    { unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
    unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma cps_ASTA_switch : forall Σ Σ' PMc Pm Q, rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) ->
  cps asegs (ASTA RT Σ' PMc Pm) Q -> cps asegs (ASTA RT Σ PMc Pm) Q.
Proof.
  intros Σ Σ' PMc Pm Q EA HM H. eapply cps_conseq; [exact H| | auto].
  intros c Hc. unfold ASTA in *. rewrite EA. eapply AST_conseq; [exact Hc| auto|]. intros mo [H1 H2]. split; [exact (HM mo H1)| exact H2].
Qed.

(* [comment removed for export] *)
Lemma flag_apart : forall live frames (fl lo hi : Z), ~ aclient live frames USTACK_TOP fl ->
  (forall x, lo <= x < hi -> aclient live frames USTACK_TOP x) -> fl < lo \/ hi <= fl.
Proof.
  intros live frames fl lo hi HN HR. destruct (Z_lt_ge_dec fl lo) as [L|L]; [left; exact L|].
  destruct (Z_lt_ge_dec fl hi) as [U|U]; [| right; lia]. exfalso. apply HN. apply HR. lia.
Qed.

(* [comment removed for export] *)
Lemma flag_not_client : forall live frames live0 frames0 (fl lo sp : Z), ~ aclient live frames USTACK_TOP fl ->
  fl + 1 <= lo -> lo <= sp -> (forall e, In e live0 -> In e live) -> (forall e, In e frames0 -> In e frames) ->
  ~ aclient live0 frames0 sp fl.
Proof.
  intros live frames live0 frames0 fl lo sp HN H1 H2 HL HF [H|[H|[H|[H|H]]]]; [lia| | | |]; apply HN.
  - right; left. exact H.
  - right; right; left. destruct H as (p & n & Hin & Hp). exists p, n. split; [exact (HL _ Hin)| exact Hp].
  - right; right; right; left. destruct H as (f & k & Hin & Hf). exists f, k. split; [exact (HF _ Hin)| exact Hf].
  - right; right; right; right. destruct H as (f & k & Hin & Hf). exists f, k. split; [exact (HF _ Hin)| exact Hf].
Qed.

Lemma cps_finish : forall (P Q : config -> Prop), (forall c, P c -> Q c) -> cps asegs P Q.
Proof. intros P Q H. eapply cps_conseq; [apply cps_refl| intros c Hc; exact Hc| exact H]. Qed.

Lemma ASTA_conseq : forall Σ PMc Pm Pm' c, ASTA RT Σ PMc Pm c -> (forall ms, Pm ms -> Pm' ms) -> ASTA RT Σ PMc Pm' c.
Proof. intros Σ PMc Pm Pm' c H HP. unfold ASTA in *. eapply AST_conseq; [exact H| exact HP| auto]. Qed.

End Kit.

(* [comment removed for export] *)
Ltac cps_walk AF MST := apply (cps_walk_lemma _ AF _ _ _ _ MST).
(* [comment removed for export] *)
Ltac cps_stop := apply evt_done.

Ltac lept_transport_extra2 m a bs n Hn Ha Hl :=
  lept_transport_extra m a bs n Hn Ha Hl;
  repeat match goal with
  | H : accok ?lv ?frs m ?A ?N |- _ =>
      first [ apply (accok_write_out lv frs m a bs A N n Hn Ha Hl) in H; [ | tlia | tlia ]
            | idtac "note: dropping accok fact (store may alias its shadow):" H; clear H ]
  end.
Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= lept_transport_extra2 m a bs n Hn Ha Hl.

Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.

(* [comment removed for export] *)
Ltac to_entry :=
  lazymatch goal with
  | |- cps _ (ASTA _ _ _ (eq (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro))) _ =>
    let g k := (let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
                let v := eval cbv beta iota delta [tget mkR] in (tget p R) in lazymatch v with Some ?x => x end) in
    let x1 := g 1 in let x2 := g 2 in let x3 := g 3 in let x4 := g 4 in let x5 := g 5 in let x6 := g 6 in let x7 := g 7 in let x8 := g 8 in
    let x9 := g 9 in let x10 := g 10 in let x11 := g 11 in let x12 := g 12 in let x13 := g 13 in let x14 := g 14 in let x15 := g 15 in
    let x16 := g 16 in let x17 := g 17 in let x18 := g 18 in let x19 := g 19 in let x20 := g 20 in let x21 := g 21 in let x22 := g 22 in
    let x23 := g 23 in let x24 := g 24 in let x25 := g 25 in let x26 := g 26 in let x27 := g 27 in let x28 := g 28 in let x29 := g 29 in
    let x30 := g 30 in let x31 := g 31 in
    change (MS R F (Z_to_bv 64 pc) fc None m ro) with
      (entry_st x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc pc m)
  end.

(* [comment removed for export] *)
Ltac cps_open1 RT :=
  first [ apply cps_ex_l; intro
        | apply cps_and_pure_r; intro
        | apply (cps_ASTA_ex RT); intro
        | apply (cps_ASTA_pure_r RT); intro
        | apply (cps_ASTA_eq_sym RT) ].
Ltac cps_open RT := unfold malloc_post, free_post, icpt_post, ret_st; repeat (cps_open1 RT).

(* [comment removed for export] *)
Ltac in_live_tac :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat first [ eassumption | left; reflexivity
               | apply live_remove_keep; [ | cbn [fst]; first [assumption | congruence | lia] ]
               | right ].
(* [comment removed for export] *)
Ltac live_sub_tac :=
  let e := fresh "e" in let He := fresh "He" in intros e He;
  try solve [destruct He];   (* [comment removed for export] *)
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
  repeat first [ exact He | eapply live_remove_sub; first [exact He | eassumption] ];
  first [ exact He
        | apply live_remove_sub in He; exact He
        | apply live_remove_sub in He; apply live_remove_sub in He; exact He ].
Ltac frames_sub_tac :=
  let e := fresh "e" in let He := fresh "He" in intros e He;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H in * end;
  first [ exact He | right; exact He | right; right; exact He ].
Ltac live_sub_tac_pk :=
  lazymatch goal with Hin : In (?p, ?k) _ |- In (?p, ?k) _ =>
    repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H in * end;
    first [ exact Hin
          | apply live_remove_sub in Hin; exact Hin
          | apply live_remove_sub in Hin; apply live_remove_sub in Hin; exact Hin
          | apply live_remove_keep; [ first [exact Hin | apply live_remove_sub in Hin; exact Hin] | cbn [fst]; first [assumption|congruence|lia] ] ]
  end.
Ltac static_tac :=
  match goal with
  | GP : rt_gaps ?RT |- aclient _ _ _ ?x =>
      right; left; apply (gp_globals_client RT GP); unfold in_ranges, LEPT_GLOBALS; cbn [map fst snd];
      first [ exists 0xd2300, (0xd2300 + 4); split; [left; reflexivity | lia]
            | exists 0xd2320, (0xd2320 + 8); split; [right; left; reflexivity | lia]
            | exists 0xd2340, (0xd2340 + 8); split; [right; right; left; reflexivity | lia]
            | exists 0xd2360, (0xd2360 + 8); split; [right; right; right; left; reflexivity | lia] ]
  end.
Ltac frames_in_tac :=
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat first [ eassumption | left; reflexivity | right ].
Ltac fframe_tac :=
  match goal with
  | FRSx : rt_frames _ _ = (?f, ?k) :: _ |- aclient _ _ _ ?x =>
      let v := eval vm_compute in (fs_size k) in
      first [ right; right; right; left; exists f, k; split; [ solve [frames_in_tac] | change (fs_size k) with v; lia ]
            | right; right; right; right; exists f, k; split;
              [ solve [frames_in_tac] | change (fs_size k) with v; unfold shad, SHB in *; Z.div_mod_to_equations; lia ] ]
  end.
Ltac aclient_tac :=
  first [ left; ul
        | static_tac
        | fframe_tac
        | match goal with
          | H : In (?p, ?k) _ |- aclient _ _ _ ?x =>
              right; right; left; exists p, k; split; [ solve [in_live_tac] | ul ]
          end
        | match goal with
          | H : accok ?lv ?frs ?m ?a ?n |- aclient ?lv' ?frs' ?sp' ?x =>
              apply (aclient_mono lv frs sp' lv' frs' sp' x);
              [ exact (accok_aclient lv frs m sp' a n x H ltac:(ul)) | live_sub_tac | frames_sub_tac | lia ]
          end
        | assumption ].

(* [comment removed for export] *)
Ltac head_var A := lazymatch A with (?b + _)%Z => head_var b | (?b - _)%Z => head_var b | ?b => b end.
Ltac acl_dispatch A :=
  lazymatch A with
  | context [(_ / 8)%Z] => fframe_tac
  | _ =>
    let b := head_var A in
    lazymatch b with
    | Zpos _ =>
        let inb := eval vm_compute in (existsb (fun r => (fst r <=? b) && (b <? fst r + snd r))%Z LEPT_GLOBALS) in
        lazymatch inb with true => static_tac end
    | _ =>
      first [ lazymatch goal with _ : rt_frames _ _ = (b, _) :: _ |- _ => fframe_tac end
            | lazymatch goal with _ : In (b, _) _ |- _ =>
                match goal with
                | H : In (b, ?k) _ |- aclient _ _ _ ?x => right; right; left; exists b, k; split; [ solve [in_live_tac] | ul ]
                end end
            | lazymatch goal with _ : accok _ _ _ b _ |- _ =>
                match goal with
                | H : accok ?lv ?frs ?m b ?n |- aclient ?lv' ?frs' ?sp' ?x =>
                    apply (aclient_mono lv frs sp' lv' frs' sp' x);
                    [ exact (accok_aclient lv frs m sp' b n x H ltac:(ul)) | live_sub_tac | frames_sub_tac | lia ]
                end end
            | left; ul ]
    end
  end.

Ltac agree_range AG A acl :=
  eapply agree_sub; [exact AG|]; cbv beta;
  let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; acl A.

(* [comment removed for export] *)
Ltac kit_unpark := idtac.
(* [comment removed for export] *)
Ltac accok_fp_on := fail.
(* [comment removed for export] *)
Ltac rt_transport_extra m m' AG := idtac.

Ltac rt_transport m m' AG acl :=
  rt_transport_extra m m' AG;
  repeat match goal with
  | H : rw_cells asegs m ?A ?cs |- _ =>
      first [ apply (rw_cells_agree_nw asegs m m' A cs) in H; [ | solve [agree_range AG A acl] ]
            | idtac "note: dropping (not provably client memory):" H; clear H ]
  | H : ro_cells asegs m ?A ?cs |- _ =>
      first [ apply (ro_cells_agree asegs m m' A cs) in H; [ | solve [agree_range AG A acl] ]
            | clear H ]
  | H : bytes_at asegs m ?A ?bs |- _ =>
      first [ apply (bytes_at_agree asegs m m' A bs) in H; [ | solve [agree_range AG A acl] ]
            | idtac "note: dropping (not provably client memory):" H; clear H ]
  | H : wr_at asegs m ?A ?n |- _ =>
      first [ match goal with WMx : wmono asegs m m' |- _ => apply (wr_at_transport asegs m m' A n) in H; [ | exact WMx ] end
            | apply (wr_at_agree_nw asegs m m' A n) in H; [ | solve [agree_range AG A acl] ]
            | clear H ]
  | H : accok ?lv ?frs m ?a ?n |- _ =>
      lazymatch type of AG with
      | agree_on (aclient ?lv' ?frs' ?sp') _ _ =>
        first [ apply (accok_keep_sub lv frs m m' lv' frs' sp' a n) in H; [ | exact AG | lia | solve [frames_sub_tac] ]
              | idtac "note: dropping accok fact:" H; clear H ]
      | agree_on (fun x => aclient ?lv' ?frs' ?sp' x /\ outside ?W x) _ _ =>
        first [ accok_fp_on; apply (accok_keep_fp lv frs m m' lv' frs' sp' W a n) in H;
                [ | exact AG | lia | solve [frames_sub_tac]
                  | let x := fresh "x" in let Hx := fresh "Hx" in
                    solve [intros x Hx; unfold shad, SHB in Hx; cbn [outside]; repeat split; try exact I;
                           kit_unpark; intro; Z.div_mod_to_equations; lia] ]
              | idtac "note: dropping accok fact (footprint call):" H; clear H ]
      | _ => idtac "note: dropping accok fact (rt_pres_ex call):" H; clear H
      end
  | H : acc asegs m _ _ |- _ => clear H
  | H : mem_inv asegs m |- _ => clear H
  | H : stk asegs m _ _ |- _ => clear H
  | H : munch _ _ m |- _ => clear H
  | H : wmono asegs ?m0 m |- _ =>
      first [ match goal with WMx : wmono asegs m m' |- _ => apply (fun h => wmono_trans asegs m0 m m' h WMx) in H end
            | clear H ]
  end.

(* [comment removed for export] *)
Ltac split_hyps :=
  repeat match goal with
  | H : _ /\ _ |- _ => let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]
  end.
Ltac fix_ret_pc :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] => rewrite (ret_pc_even z) by (first [lia | reflexivity])
  end.
(* [comment removed for export] *)
Ltac after_call_unfold := idtac.
(* [comment removed for export] *)
Ltac fold_zdefs :=
  repeat match goal with
  | x := ?b : Z |- _ =>
      match goal with
      | H : context [b] |- _ => lazymatch H with x => fail | _ => progress (change b with x in H) end
      | |- context [b] => progress (change b with x)
      end
  end.
(* [comment removed for export] *)
Ltac norm_fshadow :=
  repeat match goal with
  | H : context [(?f + Zpos ?c) / 8] |- _ =>
      let c8 := eval vm_compute in (Zpos c / 8) in
      replace ((f + Zpos c) / 8) with (f / 8 + c8) in H by (clear; Z.div_mod_to_equations; lia)
  end.
(* [comment removed for export] *)
Ltac notin_side :=
  repeat match goal with |- ~ (_ <= ?x < _) => match goal with H : context [x] |- _ => revert H end end; tlia.
Ltac outside_side := cbn [outside]; first [ exact I | repeat split; notin_side ].

Ltac after_call RT AF :=
  cps_open RT;
  after_call_unfold;
  fold_zdefs;
  unfold rt_after, rt_after_f in *;
  split_hyps;
  unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *;
  repeat match goal with
  | H : context [bv_unsigned (Z_to_bv 64 ?e)] |- _ => rewrite (unsigned_lit e) in H by lia
  end;
  (* [comment removed for export] *)
  lazymatch goal with
  | P : rt_pres ?lv ?frs ?spc ?ma ?mb |- _ =>
      let AG := fresh "AG" in
      assert (AG : agree_on (aclient lv frs spc) ma mb) by (intros ? Ha; exact (P _ Ha));
      clear P;
      rt_transport ma mb AG ltac:(fun A => acl_dispatch A)
  | P : rt_pres_ex ?lv ?frs ?spc ?d ?n ?ma ?mb |- _ =>
      let AG := fresh "AG" in
      assert (AG : agree_on (fun a => aclient lv frs spc a /\ ~ (d <= a < d + n)) ma mb) by (intros ? [Ha Hb]; exact (P _ Ha Hb));
      clear P;
      rt_transport ma mb AG ltac:(fun A => split; [acl_dispatch A | notin_side])
  | P : rt_pres_fp ?lv ?frs ?spc ?W ?ma ?mb |- _ =>
      let AG := fresh "AG" in
      assert (AG : agree_on (fun a => aclient lv frs spc a /\ outside W a) ma mb) by (intros ? [Ha Hb]; exact (P _ Ha Hb));
      clear P;
      rt_transport ma mb AG ltac:(fun A => split; [acl_dispatch A | outside_side])
  | _ => idtac
  end;
  fix_ret_pc.

(* [comment removed for export] *)
Ltac refresh RT AF :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?m' _))) _ =>
      lazymatch goal with
      | A : ART RT S m' |- _ =>
          let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
          destruct (af_client_consts RT AF S m' A) as (G1 & G2 & G3 & G4);
          unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in G1, G2, G3, G4;
          repeat match goal with
          | H : In (?p, ?n) _ |- _ =>
              lazymatch goal with
              | _ : acc asegs m' p n |- _ => fail
              | _ => let AC := fresh "ACC" in
                     assert (AC : acc asegs m' p n) by (apply (acc_live RT AF S m' p n A); solve [in_live_tac])
              end
          end;
          repeat match goal with
          | H : accok ?lv ?frs m' ?a ?n |- _ =>
              lazymatch goal with
              | _ : acc asegs m' a n |- _ => fail
              | _ => let AC := fresh "ACC" in
                     assert (AC : acc asegs m' a n)
                       by (apply (accok_acc_sub RT AF S m' lv frs a n A ltac:(lia)); [ solve [live_sub_tac] | solve [frames_sub_tac] | exact H ])
              end
          end
      | _ => fail "refresh: no ART fact for the current state"
      end
  end.

(* [comment removed for export] *)
Ltac agf_munch AGF MU side :=
  lazymatch type of AGF with agree_on ?PF ?m0 ?m =>
    lazymatch type of MU with munch ?Wk m ?m1 =>
      let N := fresh "AGF" in
      assert (N : agree_on PF m0 m1)
        by (apply (agree_trans PF m0 m m1 AGF); apply (agree_of_munch Wk m m1 PF MU);
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; side Hx);
      clear AGF; rename N into AGF
    end end.
Ltac agf_call AGF AG side :=
  lazymatch type of AGF with agree_on ?PF ?m0 ?m =>
    lazymatch type of AG with agree_on ?P2 m ?m1 =>
      let N := fresh "AGF" in
      assert (N : agree_on PF m0 m1)
        by (apply (agree_trans PF m0 m m1 AGF); apply (agree_sub P2 PF m m1 AG);
            let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; side Hx);
      clear AGF; rename N into AGF
    end end.

(* [comment removed for export] *)
Ltac walk_to AF MST W stops :=
  cps_walk AF MST;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      (* [comment removed for export] *)
      repeat match goal with H : munch _ _ mm |- _ => clear H end;
      let MU := fresh "MU" in let WM := fresh "WM" in
      pose proof (munch_refl W mm) as MU; pose proof (wmono_refl asegs mm) as WM
  end;
  awalk stops.

(* [comment removed for export] *)
Ltac art_now RT AF ivt :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS ?R _ _ _ _ ?mf _))) _ =>
      lazymatch goal with
      | _ : ART RT S mf |- _ => idtac
      | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf, STx : stk asegs mf ?lo _ |- _ =>
          let N := fresh "ARTc" in
          assert (N : ART RT S mf)
            by (apply (art_client_writes RT AF S mm mf lo W A MUx WMx);
                [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | ivt ])
      end
  end.

Ltac at_call RT AF ivt pft :=
  cps_stop; art_now RT AF ivt; to_entry;
  lazymatch goal with
  | AGF : agree_on ?PF _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PF; agf_munch AGF MUx pft
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac fold_ag side :=
  lazymatch goal with
  | AGF : agree_on ?PF ?m0 ?m, AG : agree_on ?P2 ?m ?m1 |- _ => is_var PF; agf_call AGF AG side; clear AG
  end.

(* [comment removed for export] *)
Ltac call_ok_tac :=
  unfold call_ok; rewrite ?unsigned_lit by ul;
  split; [ eassumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul ].

(* [comment removed for export] *)
Ltac norm_cells H :=
  repeat match type of H with
  | context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H
  end;
  repeat match type of H with
  | context [(?a + ?b + ?c)%Z] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (b + c)%Z in
        replace (a + b + c)%Z with (a + v)%Z in H by lia
  end.
(* [comment removed for export] *)
Ltac split_cells H pre H2 :=
  apply (rw_cells_app _ _ pre _) in H; destruct H as [H H2]; norm_cells H2.

(* [comment removed for export] *)
Ltac rt_side0 :=
  lazymatch goal with
  | |- rt_frames _ _ = _ => assumption
  | |- @eq word _ _ => reflexivity
  | |- @eq Z _ _ => first [ reflexivity | lia ]
  | |- ART _ _ _ => assumption
  | |- mem_inv _ _ => assumption
  | |- fdfs_only _ => assumption
  | |- mat_stable _ => assumption
  | |- io_ssp _ => assumption
  | |- In _ set_shadow_vals => unfold set_shadow_vals; repeat first [ left; reflexivity | right ]
  | |- In _ LEPT_FMTS => first [ assumption | unfold LEPT_FMTS; repeat first [ left; reflexivity | right ] ]
  | |- In _ (rt_live _ _) => solve [in_live_tac]
  | |- call_ok _ _ _ _ _ => call_ok_tac
  | |- forall i, _ -> in_fframe_shadow _ _ =>
      let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
      match goal with
      | FRSx : rt_frames _ _ = (?f, ?k) :: _ |- _ =>
          exists f, k; split; [ solve [frames_in_tac] |
            let v := eval vm_compute in (fs_size k) in change (fs_size k) with v; unfold shad, SHB in *; Z.div_mod_to_equations; lia ]
      end
  | |- rw_cells _ _ _ _ => assumption
  | |- wr_at _ _ _ _ => assumption
  | |- stk _ _ _ _ => assumption
  | |- (_ \/ _ \/ _)%nat => first [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ]
  | |- (_ <= _ < _)%Z => first [ lia | ul ]
  | |- (_ <= _)%Z => first [ lia | ul | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H in * end; ul ]
  | |- (_ < _)%Z => first [ lia | ul ]
  | |- (_ = _ :> Z) => first [ lia | ul ]
  | |- (_ < _)%nat => first [ assumption | repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; cbn [length]; unfold FRAMES_MAX in *; lia ]
  | |- _ => assumption
  end.
Ltac rt_side extra :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
  end;
  first [ solve [rt_side0] | extra ].

(* [comment removed for export] *)
Ltac list_firstn k l :=
  lazymatch k with
  | O => constr:(@nil cell)
  | S ?k' => lazymatch l with ?c :: ?l' => let r := list_firstn k' l' in constr:(c :: r) end
  end.
Ltac list_skipn k l :=
  lazymatch k with
  | O => l
  | S ?k' => lazymatch l with _ :: ?l' => list_skipn k' l' end
  end.
Ltac list_len l := lazymatch l with nil => constr:(O) | _ :: ?l' => let n := list_len l' in constr:(S n) end.

(* [comment removed for export] *)
Ltac split_at H k H2 :=
  lazymatch type of H with
  | rw_cells _ _ _ ?cs =>
      let k' := eval cbv in k in
      let pre := list_firstn k' cs in
      let post := list_skipn k' cs in
      change cs with (pre ++ post) in H; split_cells H pre H2
  end.
(* [comment removed for export] *)
Ltac split_last_CB H sizes :=
  lazymatch type of H with
  | rw_cells _ _ _ ?cs =>
      let n := list_len cs in
      lazymatch n with
      | S ?k =>
          let pre := list_firstn k cs in
          let lst := list_skipn k cs in
          lazymatch lst with
          | [CB ?sz ?j] =>
              change cs with (pre ++ CB sz j :: []) in H;
              apply (rw_cells_split_CB asegs _ _ pre sz j [] sizes) in H; [ | reflexivity ];
              cbn [mk_CB_cells app] in H
          end
      end
  end.

(* [comment removed for export] *)
Ltac idx_of c l :=
  lazymatch l with
  | c :: _ => constr:(O)
  | _ :: ?l' => let n := idx_of c l' in constr:(S n)
  end.
Ltac split_before H c H2 :=
  lazymatch type of H with
  | rw_cells _ _ _ ?cs => let k := idx_of c cs in split_at H k H2
  end.
