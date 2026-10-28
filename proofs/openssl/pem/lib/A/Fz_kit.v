(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx I_lkit.
From stdpp Require list_basics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

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

Lemma rw_cells_recast : forall (m : mem) A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma wr_at_rw_C1 : forall (m : mem) a, wr_at asegs m a 1 -> exists b, rw_cells asegs m a [C1 b].
Proof.
  intros m a W. destruct (wr_at_rw_CB m a 1 W ltac:(lia)) as (junk & H).
  destruct H as [[W1 B] R]. cbn in W1. destruct junk as [|b [|? ?]]; cbn in W1; try (destruct W1; discriminate).
  exists b. split; [split; [cbn; split; [reflexivity| exact I]| exact B]| exact R].
Qed.

(* [comment removed for export] *)
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

Lemma pres_fp_refl : forall live frames sp W m, rt_pres_fp live frames sp W m m.
Proof. intros live frames sp W m a _ _. reflexivity. Qed.

Lemma pres_fp_trans : forall live frames sp W m1 m2 m3,
  rt_pres_fp live frames sp W m1 m2 -> rt_pres_fp live frames sp W m2 m3 -> rt_pres_fp live frames sp W m1 m3.
Proof. intros live frames sp W m1 m2 m3 H1 H2 a Ha Ho. rewrite (H2 a Ha Ho). exact (H1 a Ha Ho). Qed.

Lemma pres_fp_of_pres : forall live frames sp W m m', rt_pres live frames sp m m' -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W m m' H a Ha _. exact (H a Ha). Qed.

(* [comment removed for export] *)
Lemma pres_fp_sub : forall live frames sp W live' frames' sp' W' m m',
  rt_pres_fp live' frames' sp' W' m m' ->
  (forall x, aclient live frames sp x -> outside W x -> aclient live' frames' sp' x /\ outside W' x) ->
  rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W live' frames' sp' W' m m' H HS a Ha Ho. destruct (HS _ Ha Ho) as [H1 H2]. exact (H a H1 H2). Qed.

Lemma pres_fp_of_munch : forall live frames sp W W' m m', munch W' m m' ->
  (forall x, aclient live frames sp x -> outside W x -> outside W' x) -> rt_pres_fp live frames sp W m m'.
Proof. intros live frames sp W W' m m' MU H a Ha Ho. apply MU. exact (H _ Ha Ho). Qed.

Lemma pres_fp_of_ex : forall live frames sp d n W m m', rt_pres_ex live frames sp d n m m' ->
  (forall x, d <= x < d + n -> ~ outside W x) -> rt_pres_fp live frames sp W m m'.
Proof.
  intros live frames sp d n W m m' H HW a Ha Ho. apply H; [exact Ha|]. intros Hd. exact (HW _ Hd Ho).
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
Lemma live_remove_notin : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. unfold live_remove in *. cbn.
  assert (E : (fst e =? p) = false) by (apply Z.eqb_neq; apply H; left; reflexivity).
  rewrite E. cbn. destruct (stdpp.base.decide True) as [_|N]; [| exfalso; apply N; exact I].
  f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.
Lemma live_remove_head : forall p n (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p ((p, n) :: l) = l.
Proof.
  intros p n l H. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn.
  destruct (stdpp.base.decide False) as [N|_]; [destruct N|]. exact (live_remove_notin p l H).
Qed.

(* [comment removed for export] *)
Lemma acl_stack : forall live frames sp y, sp <= y < USTACK_TOP -> aclient live frames sp y.
Proof. intros. left. assumption. Qed.
Lemma acl_static : forall live frames sp y, client_static y -> aclient live frames sp y.
Proof. intros. right; left. assumption. Qed.
Lemma acl_live : forall live frames sp p n y, In (p, n) live -> p <= y < p + n -> aclient live frames sp y.
Proof. intros live frames sp p n y H1 H2. right; right; left. exists p, n. split; assumption. Qed.
Lemma acl_frame : forall live frames sp f k y, In (f, k) frames -> f <= y < f + fs_size k - 8 -> aclient live frames sp y.
Proof. intros live frames sp f k y H1 H2. right; right; right; left. exists f, k. split; assumption. Qed.
Lemma acl_fshadow : forall live frames sp f k y, In (f, k) frames -> shad f <= y < shad (f + fs_size k) -> aclient live frames sp y.
Proof. intros live frames sp f k y H1 H2. right; right; right; right. exists f, k. split; assumption. Qed.

Lemma shad_add64 : forall f j, f mod 64 = 0 -> shad (f + 64 * j) = shad f + 8 * j.
Proof. intros f j H. unfold shad. Z.div_mod_to_equations. lia. Qed.


(* [comment removed for export] *)
Lemma acc_agree : forall (m m' : mem) a n, acc asegs m a n -> 0 <= a ->
  agree_on (fun x => shad a <= x <= shad (a + n - 1)) m m' -> acc asegs m' a n.
Proof.
  intros m m' a n H Ha AG i Hi. destruct (H i Hi) as (b & Hb & Hs). exists b. split; [| exact Hs].
  apply (bytes_at_agree asegs m m' _ _ Hb). intros x Hx. apply AG. cbn [length] in Hx. unfold shad in *.
  pose proof (Z.div_le_mono a (a + i) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (a + i) (a + n - 1) 8 ltac:(lia) ltac:(lia)).
  cbv beta. lia.
Qed.

(* [comment removed for export] *)
Lemma uw_chain_agree : forall ras (m m' : mem) lim f, uw_chain m lim f ras ->
  agree_on (fun x => bv_unsigned lim <= x < USTACK_TOP) m m' -> uw_chain m' lim f ras.
Proof.
  induction ras as [|ra ras IH]; intros m m' lim f H AG; [exact H|].
  cbn [uw_chain] in *. destruct H as (H1 & H2 & fp' & HC & HR). split; [exact H1|]. split; [exact H2|]. exists fp'. split.
  - apply (rw_cells_agree_nw asegs m m' _ _ HC). intros x Hx. apply AG. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
  - apply (IH m m' f fp' HR). intros x Hx. apply AG. cbv beta in *. lia.
Qed.


Lemma rw_cells_join2 : forall (m : mem) a c1 c2, rw_cells asegs m a [c1] -> rw_cells asegs m (a + Z.of_nat (csize c1)) [c2] ->
  rw_cells asegs m a [c1; c2].
Proof.
  intros m a c1 c2 H1 H2. apply (proj2 (rw_cells_app m a [c1] [c2])). split; [exact H1|]. cbn [cells_size Nat.add].
  rewrite Nat.add_0_r. exact H2.
Qed.
Lemma rw_cells_skip : forall (m : mem) A cs1 cs2, rw_cells asegs m A (cs1 ++ cs2) -> rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. intros m A cs1 cs2 H. exact (proj2 (proj1 (rw_cells_app m A cs1 cs2) H)). Qed.
Lemma stk_wr_at : forall (m : mem) lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at asegs m a n.
Proof.
  intros m lo hi a n (S0 & S1 & S) Ha Hn H0. split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (S (a + i) ltac:(lia))).
Qed.

Lemma stk_munch : forall W (m m' : mem) lo hi, stk asegs m lo hi -> munch W m m' -> wmono asegs m m' ->
  (forall x, lo <= x < hi -> outside W x) -> stk asegs m' lo hi.
Proof. intros W m m' lo hi H MU WM HO. apply (stk_agree asegs m m' lo hi H); [| exact WM]. exact (agree_of_munch W m m' _ MU HO). Qed.

(* [comment removed for export] *)
Lemma uw_chain_agree_fp : forall ras (m m' : mem) lim f, uw_chain m lim f ras ->
  agree_on (fun x => bv_unsigned f - 16 <= x < USTACK_TOP) m m' -> uw_chain m' lim f ras.
Proof.
  induction ras as [|ra ras IH]; intros m m' lim f H AG; [exact H|].
  cbn [uw_chain] in *. destruct H as (H1 & H2 & fp' & HC & HR). split; [exact H1|]. split; [exact H2|]. exists fp'. split.
  - apply (rw_cells_agree_nw asegs m m' _ _ HC). intros x Hx. apply AG. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
  - destruct ras as [|ra' ras']; [exact HR|]. apply (IH m m' f fp' HR). intros x Hx. apply AG. cbv beta in *.
    cbn [uw_chain] in HR. destruct HR as (HR1 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma ro_C8_func : forall (m : mem) a (v w : word), ro_cells asegs m a [C8 v] -> ro_cells asegs m a [C8 w] -> v = w.
Proof.
  intros m a v w [_ (_ & _ & H1)] [_ (_ & _ & H2)]. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
  assert (E : le8 v = le8 w).
  { apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [Hi|Hi].
    - rewrite <- H1 by (rewrite length_le8; exact Hi). rewrite <- H2 by (rewrite length_le8; exact Hi). reflexivity.
    - rewrite (proj2 (nth_error_None (le8 v) i)) by (rewrite length_le8; exact Hi).
      rewrite (proj2 (nth_error_None (le8 w) i)) by (rewrite length_le8; exact Hi). reflexivity. }
  rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity.
Qed.

Section CKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma PMc_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof using AF. intros Σ PMc H. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact H]. Qed.

(* [comment removed for export] *)
Lemma asta_evt' : forall Σ PMc Pm Q, mat_stable PMc -> (forall ms, Pm ms -> evt asegs Q ms) ->
  cps asegs (ASTA RT Σ PMc Pm) (ASTA RT Σ PMc Q).
Proof using AF.
  intros Σ PMc Pm Q HM H. unfold ASTA.
  apply (ast_evt asegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable; exact HM| exact H].
Qed.

(* [comment removed for export] *)
Lemma ASTA_switch : forall (Σ Σ' : rts RT) PMc Pm c, ASTA RT Σ PMc Pm c -> rt_allow RT Σ' = rt_allow RT Σ ->
  (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> ASTA RT Σ' PMc Pm c.
Proof.
  intros Σ Σ' PMc Pm c H HA HM. unfold ASTA in *. rewrite HA.
  eapply AST_conseq; [exact H| auto|]. intros mo [H1 H2]. split; [apply HM; exact H1| exact H2].
Qed.

(* [comment removed for export] *)
Lemma aclient_split : forall Σ m usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m usp a ART0 [H|[H|[H|[H|H]]]].
  - left; lia.
  - right. pose proof (client_static_range a H). pose proof (af_sp0_range RT AF Σ m ART0). ul.
  - right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0).
    unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma newframe_apart : forall (Σ Σ1 : rts RT) (m1 : mem) Fr k usp a,
  ART RT Σ1 m1 -> rt_frames RT Σ1 = (Fr, k) :: rt_frames RT Σ -> rt_live RT Σ1 = rt_live RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  ~ (Fr <= a < Fr + fs_size k) /\ ~ (shad Fr <= a < shad (Fr + fs_size k)).
Proof using AF.
  intros Σ Σ1 m1 Fr k usp a ART1 FRS LV SP0 LU Ha.
  assert (INF : In (Fr, k) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m1 Fr k ART1 INF) as (R0 & R1 & R2 & R3).
  pose proof (af_fshadow_apart RT AF Σ1 m1 Fr k ART1 INF) as (SL & SF).
  pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SPR. pose proof (af_sp0_win RT AF Σ1 m1 ART1) as SPW.
  rewrite SP0 in R1, SPR, SPW.
  assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (SH1 : shad (Fr + fs_size k) <= 2^44 + SHB).
  { unfold shad. assert ((Fr + fs_size k) / 8 <= 2^44) by (apply Z.div_le_upper_bound; ul). lia. }
  assert (SH0 : SHB <= shad Fr) by (unfold shad; assert (0 <= Fr / 8) by (apply Z.div_pos; lia); lia).
  assert (SHM : shad Fr <= shad (Fr + fs_size k)) by (unfold shad; pose proof (Z.div_le_mono Fr (Fr + fs_size k) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Ha as [H|[H|[H|[H|H]]]].
  - split; unfold SHB in *; ul.
  - pose proof (client_static_range a H). split; [destruct R2; unfold SEGTOP_A in *; lia|]. unfold SHB, SEGTOP_A in *. lia.
  - destruct H as (p & n & Hin & Hp). rewrite <- LV in Hin. destruct (R3 p n Hin); destruct (SL p n Hin); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D];
      (destruct (SF f k' ltac:(rewrite FRS; right; exact Hin)) as [E|E]); split; lia.
  - destruct H as (f & k' & Hin & Hf).
    assert (INf : In (f, k') (rt_frames RT Σ1)) by (rewrite FRS; right; exact Hin).
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k' ART1 INf) as (_ & SF').
    destruct (af_frames_disj RT AF Σ1 m1 Fr k f k' [] (rt_frames RT Σ) ART1 FRS Hin) as [D|D].
    + pose proof (Z.div_le_mono (Fr + fs_size k) f 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
    + assert (FSZ' : 0 <= fs_size k') by (unfold fs_size; apply Z.shiftl_nonneg; lia).
      pose proof (Z.div_le_mono (f + fs_size k') Fr 8 ltac:(lia) D). destruct (SF' Fr k INF) as [E|E]; split; unfold shad in *; lia.
Qed.

(* [comment removed for export] *)
Lemma newchunk_apart : forall (Σ Σ1 : rts RT) (m1 : mem) p n usp a,
  ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
  rt_sp0 RT Σ - STACK_WIN <= usp -> 0 <= n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
  intros Σ Σ1 m1 p n usp a ART1 LV FRS SP0 LU Hn Ha.
  assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (R0 & R1 & R2). rewrite SP0 in R1.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - lia.
  - pose proof (client_static_range a H). unfold SEGTOP_A in *. lia.
  - destruct H as (p2 & n2 & Hin & Hp).
    destruct (af_live_disj RT AF Σ1 m1 p n p2 n2 [] (rt_live RT Σ) ART1 LV Hin); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hin) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hin) as (SL & _). destruct (SL p n INL); lia.
Qed.

(* [comment removed for export] *)
Lemma live_fresh : forall Σ (m : mem) l1 p n l2, ART RT Σ m -> rt_live RT Σ = l1 ++ (p, n) :: l2 -> 0 < n ->
  (forall e, In e (l1 ++ l2) -> 0 < snd e) -> forall e, In e (l1 ++ l2) -> fst e <> p.
Proof using AF.
  intros Σ m l1 p n l2 ART0 LV N0 POS e He E. destruct e as (p2, n2). cbn [fst] in E. subst p2.
  pose proof (af_live_disj RT AF Σ m p n p n2 l1 l2 ART0 LV He) as D. pose proof (POS _ He) as P2. cbn [snd] in P2. lia.
Qed.

End CKit.

(* [comment removed for export] *)
Lemma wr_at_wm : forall (m m' : mem) a n, wr_at asegs m a n -> wmono asegs m m' -> wr_at asegs m' a n.
Proof. intros m m' a n (A1 & B1 & C1) WM. split; [exact A1|]. split; [exact B1|]. intros i Hi. apply WM. exact (C1 i Hi). Qed.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

(* [comment removed for export] *)

Lemma outside_app_intro : forall (W1 W2 : list (Z * Z)) x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H1 H2; cbn [app outside] in *; [exact H2|]. destruct H1 as (A & B). split; [exact A | exact (IH W2 x B H2)]. Qed.

Lemma outside_dec : forall (W : list (Z * Z)) x, {outside W x} + {~ outside W x}.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [O|O]; [|right; intros (_ & H); exact (O H)].
  destruct (Z_le_gt_dec lo x) as [A|A]; [|left; split; [lia | exact O]].
  destruct (Z_lt_ge_dec x hi) as [B|B]; [right; intros (H & _); apply H; lia | left; split; [lia | exact O]].
Qed.
Section CallGlue.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

(* [comment removed for export] *)
Lemma cl_split : forall Σ (m : mem) usp d x, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= usp - d -> 0 <= d ->
  aclient (rt_live RT Σ) (rt_frames RT Σ) usp x -> usp <= x \/ x < usp - d.
Proof using AF. intros Σ m usp d x HA H1 H2 Hx. destruct (aclient_split RT AF Σ m usp x HA Hx) as [H|H]; [left; exact H | right; lia]. Qed.

(* [comment removed for export] *)
Lemma cl_seg_ART : forall Σ (m m' : mem) usp d (W : list (Z * Z)), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= usp - d -> usp <= USTACK_TOP ->
  munch (W ++ [(usp - d, usp)]) m m' -> (forall x, ~ outside W x -> client_static x) -> wmono asegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ m m' usp d W HA H1 H2 MU HW WM. apply (af_frame RT AF Σ m m' (usp - d) HA H1); [|exact WM].
  intros a Ha. apply MU. apply outside_app_intro.
  - destruct (outside_dec W (bv_unsigned a)) as [O|O]; [exact O|]. exfalso. apply Ha. right; left. exact (HW _ O).
  - cbn [outside]. split; [intros Hin; apply Ha; left; lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma cl_seg_pres : forall Σ (m m' : mem) usp d (W : list (Z * Z)), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= usp - d -> 0 <= d ->
  munch (W ++ [(usp - d, usp)]) m m' -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp W m m'.
Proof using AF.
  intros Σ m m' usp d W HA H1 H2 MU a Ha Ho. apply MU. apply outside_app_intro; [exact Ho|].
  cbn [outside]. split; [destruct (cl_split Σ m usp d _ HA H1 H2 Ha); lia | exact I].
Qed.

(* [comment removed for export] *)
Lemma cl_chain_call : forall cg Fn G r (m m1 : mem) (ra s0 sp sp' : word) outer,
  cg_ctx cg Fn (bv_unsigned ra :: outer) -> In (r, Fn) (cg_site cg) -> In (r, G) (cg_call cg) ->
  uw_chain m sp s0 outer -> agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1 ->
  rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
  bv_unsigned sp' + 16 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  cg_ctx cg G (r :: bv_unsigned ra :: outer) /\ uw_chain m1 sp' sp (bv_unsigned ra :: outer).
Proof.
  intros cg Fn G r m m1 ra s0 sp sp' outer CTX HS HC UW AG FR H1 H2. split; [exact (cg_ctx_call _ _ _ _ _ CTX HS HC)|].
  cbn [uw_chain]. split; [exact H1|]. split; [exact H2|]. exists s0. rewrite (Z_to_bv_bv_unsigned ra). split; [exact FR|].
  exact (uw_chain_agree outer m m1 sp s0 UW AG).
Qed.

(* [comment removed for export] *)
Lemma cl_unwind_call : forall cg Fn G r (m m1 : mem) (ra s0 sp sp' : word) outer,
  cg_ctx cg Fn (bv_unsigned ra :: outer) -> In (r, Fn) (cg_site cg) -> In (r, G) (cg_call cg) -> 0 <= r < 2 ^ 64 ->
  uw_chain m sp s0 outer -> agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1 ->
  rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra] ->
  bv_unsigned sp' + 16 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
  unwind_ok cg G m1 (Z_to_bv 64 r) sp sp'.
Proof.
  intros cg Fn G r m m1 ra s0 sp sp' outer CTX HS HC Hr UW AG FR H1 H2. right. exists (bv_unsigned ra :: outer).
  rewrite (unsigned_lit r) by exact Hr. exact (cl_chain_call cg Fn G r m m1 ra s0 sp sp' outer CTX HS HC UW AG FR H1 H2).
Qed.

End CallGlue.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac cl_lift W HA c' H' :=
  lazymatch type of HA with
  | ASTA ?RT ?S ?PMc _ ?c =>
      lazymatch goal with AFh : art_facts RT, MSTh : mat_stable PMc |- _ =>
        let W' := fresh "W'" in
        lazymatch type of W with evt asegs _ ?X => assert (W' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W) end;
        clear W; apply (cps_realizes asegs _ _ _ c (asta_evt' RT AFh S PMc _ _ MSTh W') HA); clear W'; intros c' H'
      end
  end.
(* [comment removed for export] *)
Ltac cl_keep H AG WM H' :=
  lazymatch type of H with
  | rw_cells _ ?m ?a ?cs =>
      lazymatch type of WM with wmono _ m ?m' =>
        assert (H' : rw_cells asegs m' a cs)
          by (apply (rw_cells_agree asegs m m' a cs H); [apply AG; [lia | cbn [cells_size csize Nat.add]; unfold USTACK_TOP in *; lia] | exact WM]) end
  end.
(* [comment removed for export] *)
Ltac cl_eu usp k E :=
  assert (E : bv_unsigned (Z_to_bv 64 (usp + k)) = usp + k) by (apply unsigned_lit; unfold USTACK_TOP, RT_STACK, STACK_WIN in *; lia).
(* [comment removed for export] *)
Ltac cl_call_ok EU ST LOW SPA q :=
  unfold call_ok; rewrite EU; split; [exact ST|]; split; [exact LOW|]; split; [unfold RT_STACK in *; lia|]; split; [unfold USTACK_TOP in *; lia|];
  apply Z.mod_divide; [lia|]; apply Z.mod_divide in SPA; [|lia]; let x := fresh "q" in let Hx := fresh "Hq" in destruct SPA as (x & Hx); exists (x - q); lia.

(* [comment removed for export] *)
Lemma acc_granule0 : forall (m : mem) a n g, acc asegs m a n -> a <= g -> g + 8 <= a + n -> g mod 8 = 0 -> 0 <= g ->
  bytes_at asegs m (shad g) [z8].
Proof.
  intros m a n g HA H1 H2 H8 H0. destruct (HA (g + 7 - a) ltac:(lia)) as (b & HB & HOK).
  replace (a + (g + 7 - a)) with (g + 7) in HB, HOK by lia.
  assert (ES : shad (g + 7) = shad g).
  { unfold shad. f_equal. pose proof (Z.div_mod g 8 ltac:(lia)) as D. rewrite H8 in D.
    replace (g + 7) with (g / 8 * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
  rewrite ES in HB.
  assert (EB : b = z8).
  { destruct HOK as [E|(E1 & E2)].
    - apply bv_eq. rewrite E. reflexivity.
    - exfalso. replace ((g + 7) mod 8) with 7 in E2; [lia|]. pose proof (Z.div_mod g 8 ltac:(lia)) as D. rewrite H8 in D.
      replace (g + 7) with (7 + g / 8 * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite <- EB. exact HB.
Qed.

Lemma acc_granule0_ro : forall (m : mem) a n g, acc asegs m a n -> a <= g -> g + 8 <= a + n -> g mod 8 = 0 -> 0 <= g ->
  ro_cells asegs m (shad g) [C1 z8].
Proof.
  intros m a n g HA H1 H2 H8 H0. pose proof (acc_granule0 m a n g HA H1 H2 H8 H0) as HB.
  unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. split; [split; [reflexivity | exact I] | exact HB].
Qed.
