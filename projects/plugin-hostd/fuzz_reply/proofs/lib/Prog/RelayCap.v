From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c
  relay_finish_b_c RelayRep HarnessRep drain_b_c relay_remove_b_c printf_facts_c snprintf_c relay_instance_gone_b_c.
Import ListNotations.
Local Open Scope Z_scope.

(* Bounds on g_capout after the relay's sends (the *_cap models of the *_b_c statements): every growth round of
   fuzz_send asks (no + n) * 2 with no + n at most the g_nout the run ends at, so the final capacity is at most the
   larger of the first one and twice the final g_nout. A dead run (live = false) keeps the capacity. *)

(* ---- Arithmetic helpers. ---- *)

Lemma rc_step : forall c0 c1 c2 n1 m n2,
  c1 <= Z.max c0 (2 * n1) -> c2 <= Z.max c1 (2 * m) -> n1 <= n2 -> m <= n2 -> c2 <= Z.max c0 (2 * n2).
Proof.
  intros c0 c1 c2 n1 m n2 H1 H2 H3 H4.
  pose proof (Z.max_spec c0 (2 * n1)). pose proof (Z.max_spec c1 (2 * m)). pose proof (Z.max_spec c0 (2 * n2)).
  lia.
Qed.

Lemma rc_mono : forall x c n m, x <= Z.max c (2 * n) -> n <= m -> x <= Z.max c (2 * m).
Proof.
  intros x c n m H1 H2. pose proof (Z.max_spec c (2 * n)). pose proof (Z.max_spec c (2 * m)). lia.
Qed.

Lemma rc_if_t : forall {X : Type} (z : Z) (a b : X), z = 0 -> (if z =? 0 then a else b) = a.
Proof. intros X z a b ->. reflexivity. Qed.

Lemma rc_if_f : forall {X : Type} (z : Z) (a b : X), z <> 0 -> (if z =? 0 then a else b) = b.
Proof. intros X z a b H. destruct (Z.eqb_spec z 0) as [E|E]; [contradiction | reflexivity]. Qed.

Lemma rc_nth_ext : forall {X : Type} (l l' : list X) (d d' : X),
  length l = length l' -> (forall n, (n < length l)%nat -> nth n l d = nth n l' d') -> l = l'.
Proof.
  intros X l. induction l as [|x l IH]; intros [|x' l'] d d' HL HN; cbn [length] in HL; try (exfalso; lia).
  - reflexivity.
  - injection HL as HL. f_equal.
    + exact (HN 0%nat ltac:(cbn [length]; lia)).
    + apply (IH l' d d' HL). intros n Hn. exact (HN (S n) ltac:(cbn [length]; lia)).
Qed.

Lemma rc_Forall_lens : forall (l : list (list Z)), Forall (fun xl => 0 <= xl) (map (fun x => Z.of_nat (length x)) l).
Proof. induction l as [|x l IH]; [constructor|]. cbn [map]. constructor; [cbv beta; lia | exact IH]. Qed.

Lemma rc_Forall_key_lens : forall ks, Forall (fun xl => 0 <= xl) (key_lens ks).
Proof.
  induction ks as [|k ks IH]; [constructor|]. unfold key_lens in *. cbn [map].
  constructor; [cbv beta; lia | exact IH].
Qed.

(* The bytes a run of gesture_ends on keys of lengths xls appends. *)
Lemma rc_xls_nonneg : forall xls, Forall (fun xl => 0 <= xl) xls -> 0 <= fold_right (fun xl acc => xl + 5 + acc) 0 xls.
Proof.
  induction xls as [|xl r IH]; intros HF; cbn [fold_right]; [lia|].
  apply Forall_cons_iff in HF as [H0 HR]. cbv beta in H0. specialize (IH HR). lia.
Qed.

Lemma keys_total_lens : forall ks, keys_total ks = fold_right (fun xl acc => xl + 5 + acc) 0 (key_lens ks).
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  change (keys_total (k :: ks)) with (Z.of_nat (length (key_text k)) + 5 + keys_total ks).
  rewrite IH. reflexivity.
Qed.

Lemma rc_length_bzs : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.

Lemma keys_total_texts : forall ks,
  keys_total ks = fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun x => Z.of_nat (length x)) (keys_texts ks)).
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  change (keys_total (k :: ks)) with (Z.of_nat (length (key_text k)) + 5 + keys_total ks).
  change (keys_texts (k :: ks)) with (bzs (key_text k) :: keys_texts ks).
  cbn [map fold_right]. rewrite IH, rc_length_bzs. reflexivity.
Qed.

Lemma keys_total_nonneg : forall ks, 0 <= keys_total ks.
Proof. intros ks. rewrite keys_total_lens. apply rc_xls_nonneg, rc_Forall_key_lens. Qed.

Lemma entries_total_nonneg : forall es, 0 <= entries_total es.
Proof.
  induction es as [|e es IH]; [change (entries_total []) with 0; lia|].
  change (entries_total (e :: es)) with (keys_total (re_keys e) + entries_total es).
  pose proof (keys_total_nonneg (re_keys e)). lia.
Qed.

Lemma with_nul_nil_len : Z.of_nat (length (with_nul [])) = 0.
Proof. reflexivity. Qed.

Lemma with_nul_cons_len : forall l ls,
  Z.of_nat (length (with_nul (l :: ls))) = Z.of_nat (length l) + 1 + Z.of_nat (length (with_nul ls)).
Proof. intros l ls. unfold with_nul. cbn [map concat]. rewrite !length_app. cbn [length]. lia. Qed.

(* ---- send_line (send_line_b_c). ---- *)

Lemma sl_run_cap_le : forall f mx no cap rem j o,
  fst (snd (sl_run f mx no cap rem j o)) <= Z.max cap (2 * (no + rem)).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o; [cbn [sl_run fst snd]; apply Z.le_max_l|].
  cbn [sl_run]. cbv zeta.
  destruct (rem <=? 0); [cbn [fst snd]; apply Z.le_max_l|].
  assert (Hn : (if negb (mx =? 0) && (mx <? rem) then mx else rem) <= rem).
  { destruct (negb (mx =? 0) && (mx <? rem)) eqn:E; cbv iota; [|lia].
    apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. lia. }
  revert Hn. generalize (if negb (mx =? 0) && (mx <? rem) then mx else rem). intros n Hn.
  destruct (cap <? no + n); cbn [fst snd].
  - specialize (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j)).
    pose proof (Z.max_spec ((no + n) * 2) (2 * (no + n + (rem - n)))).
    pose proof (Z.max_spec cap (2 * (no + rem))). lia.
  - specialize (IH mx (no + n) cap (rem - n) j o).
    pose proof (Z.max_spec cap (2 * (no + n + (rem - n)))).
    pose proof (Z.max_spec cap (2 * (no + rem))). lia.
Qed.

Lemma send_line_cap_le : forall live mx NO CAP LEN,
  send_line_cap live mx NO CAP LEN <= Z.max CAP (2 * (NO + LEN)).
Proof.
  intros [|] mx NO CAP LEN.
  - exact (sl_run_cap_le (Z.to_nat LEN) mx NO CAP LEN 0%nat adr0).
  - exact (Z.le_max_l CAP (2 * (NO + LEN))).
Qed.

Lemma send_line_cap_dead : forall mx NO CAP LEN, send_line_cap false mx NO CAP LEN = CAP.
Proof. reflexivity. Qed.

(* ---- gesture_end (gesture_end_b_c). ---- *)

Lemma gesture_end_cap_le : forall live mx NO CAP XL,
  gesture_end_cap live mx NO CAP XL <= Z.max CAP (2 * (NO + XL + 5)).
Proof.
  intros live mx NO CAP XL. unfold gesture_end_cap.
  apply (rc_step CAP (send_line_cap live mx NO CAP XL) _ (NO + XL) (NO + XL + 5));
    [apply send_line_cap_le | apply send_line_cap_le | lia | lia].
Qed.

Lemma gesture_end_cap_dead : forall mx NO CAP XL, gesture_end_cap false mx NO CAP XL = CAP.
Proof. reflexivity. Qed.

(* ---- gestures_end (gestures_end_b_c). ---- *)

Lemma keys_end_run_cap_le : forall live mx xks no cap j o,
  Forall (fun xk => 0 <= fst xk) xks ->
  fst (snd (keys_end_run live mx no cap xks j o)) <=
  Z.max cap (2 * (no + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst xks))).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o HF.
  - cbn [keys_end_run fst snd map fold_right]. apply Z.le_max_l.
  - apply Forall_cons_iff in HF as [H0 HR]. cbv beta in H0. cbn [fst] in H0.
    pose proof (rc_xls_nonneg (map fst r) (proj2 (Forall_map fst (fun xl => 0 <= xl) r) HR)) as T0.
    cbn [keys_end_run]. cbv zeta. cbn [fst snd map fold_right].
    apply (rc_step cap (gesture_end_cap live mx no cap xl) _ (no + xl + 5)
             (no + xl + 5 + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst r)));
      [apply gesture_end_cap_le | apply IH; exact HR | lia | lia].
Qed.

Lemma keys_end_run_dead : forall mx xks no cap j o, fst (snd (keys_end_run false mx no cap xks j o)) = cap.
Proof.
  intros mx xks. induction xks as [|[xl ka] r IH]; intros no cap j o; [reflexivity|].
  cbn [keys_end_run]. cbv zeta. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

Lemma gestures_end_cap_le_xls : forall live mx NO CAP xls, Forall (fun xl => 0 <= xl) xls ->
  gestures_end_cap live mx NO CAP xls <= Z.max CAP (2 * (NO + fold_right (fun xl acc => xl + 5 + acc) 0 xls)).
Proof.
  intros live mx NO CAP xls HF. unfold gestures_end_cap.
  pose proof (keys_end_run_cap_le live mx (map (fun xl => (xl, adr0)) xls) NO CAP 0%nat adr0) as K.
  rewrite map_map in K. cbn [fst] in K. rewrite map_id in K. apply K.
  apply Forall_map. exact HF.
Qed.

Lemma gestures_end_cap_le : forall live mx NO CAP ks,
  gestures_end_cap live mx NO CAP (key_lens ks) <= Z.max CAP (2 * (NO + keys_total ks)).
Proof.
  intros live mx NO CAP ks. rewrite keys_total_lens. apply gestures_end_cap_le_xls. apply rc_Forall_key_lens.
Qed.

Lemma gestures_end_cap_dead : forall mx NO CAP xls, gestures_end_cap false mx NO CAP xls = CAP.
Proof. intros mx NO CAP xls. unfold gestures_end_cap. apply keys_end_run_dead. Qed.

(* ---- relay_finish (relay_finish_b_c). ---- *)

Lemma entries_end_run_cap_le : forall nm live mx es no cap j o,
  fst (snd (entries_end_run nm live mx no cap es j o)) <= Z.max cap (2 * (no + entries_total es)).
Proof.
  intros nm live mx es. induction es as [|e es IH]; intros no cap j o.
  - cbn [entries_end_run fst snd]. apply Z.le_max_l.
  - cbn [entries_end_run]. cbv zeta. cbn [fst snd].
    change (entries_total (e :: es)) with (keys_total (re_keys e) + entries_total es).
    pose proof (keys_total_nonneg (re_keys e)). pose proof (entries_total_nonneg es).
    apply (rc_step cap (gestures_end_cap live mx no cap (key_lens (re_keys e))) _ (no + keys_total (re_keys e))
             (no + keys_total (re_keys e) + entries_total es));
      [apply gestures_end_cap_le | apply IH | lia | lia].
Qed.

Lemma entries_end_run_dead : forall nm mx es no cap j o, fst (snd (entries_end_run nm false mx no cap es j o)) = cap.
Proof.
  intros nm mx es. induction es as [|e es IH]; intros no cap j o; [reflexivity|].
  cbn [entries_end_run]. cbv zeta. cbn [fst snd]. rewrite IH. apply gestures_end_cap_dead.
Qed.

Lemma relay_finish_cap_le : forall live mx NO CAP es,
  relay_finish_cap live mx NO CAP es <= Z.max CAP (2 * (NO + entries_total es)).
Proof. intros live mx NO CAP es. exact (entries_end_run_cap_le (fun _ => adr0) live mx es NO CAP 0%nat adr0). Qed.

Lemma relay_finish_cap_dead : forall mx NO CAP es, relay_finish_cap false mx NO CAP es = CAP.
Proof. intros mx NO CAP es. exact (entries_end_run_dead (fun _ => adr0) mx es NO CAP 0%nat adr0). Qed.

(* ---- drain (drain_b_c). ---- *)

Lemma lines_run_cap_le : forall live mx ls no cap H ka j o ha ks,
  fst (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks)))) <=
  Z.max cap (2 * (no + Z.of_nat (length (with_nul ls)))).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks.
  - cbn [lines_run snd fst]. apply Z.le_max_l.
  - cbn [lines_run]. cbv zeta. cbn [snd fst]. rewrite with_nul_cons_len.
    apply (rc_step cap (send_line_cap live mx no cap (Z.of_nat (length l) + 1)) _ (no + (Z.of_nat (length l) + 1))
             (no + (Z.of_nat (length l) + 1) + Z.of_nat (length (with_nul ls))));
      [apply send_line_cap_le | apply IH | lia | lia].
Qed.

Lemma lines_run_dead : forall mx ls no cap H ka j o ha ks,
  fst (fst (snd (fst (lines_run false mx no cap H ka ls j o ha ks)))) = cap.
Proof.
  intros mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks; [reflexivity|].
  cbn [lines_run]. cbv zeta. cbn [snd fst]. rewrite IH. reflexivity.
Qed.

(* Over drain's rounds g_nout only grows, and g_capout stays within the larger of its start and twice the final
   g_nout. *)
Lemma drain_run_cap_le : forall f live mx s j a,
  ds_no s <= ds_no (fst (snd (drain_run f live mx s j a))) /\
  ds_ocap (fst (snd (drain_run f live mx s j a))) <=
    Z.max (ds_ocap s) (2 * ds_no (fst (snd (drain_run f live mx s j a)))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a.
  - cbn [drain_run snd fst]. split; [lia | apply Z.le_max_l].
  - cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
    + cbn [snd fst].
      match goal with |- context [drain_run f live mx ?s1 ?j1 ?a1] => destruct (IH s1 j1 a1) as [I1 I2] end.
      cbn [ds_no ds_ocap] in I1, I2. split; [exact I1 | exact I2].
    + destruct (ds_pend s) as [|r0 rs].
      { cbn [snd fst ds_no ds_ocap]. split; [lia | apply Z.le_max_l]. }
      match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end.
      { cbn [snd fst ds_no ds_ocap]. split; [lia | apply Z.le_max_l]. }
      match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
      match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
        pose proof (lines_run_cap_le live mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LC;
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
          as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
      cbn [snd fst] in LC |- *.
      match goal with |- context [drain_run f live mx ?s2 ?j4 ?a2] => destruct (IH s2 j4 a2) as [I1 I2] end.
      cbn [ds_no ds_ocap] in I1, I2.
      split; [lia|].
      exact (rc_step _ _ _ _ _ _ LC I2 I1 (Z.le_refl _)).
Qed.

Lemma drain_run_dead : forall f mx s j a, ds_ocap (fst (snd (drain_run f false mx s j a))) = ds_ocap s.
Proof.
  intros f mx. induction f as [|f IH]; intros s j a; [reflexivity|].
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
  - cbn [snd fst]. rewrite IH. reflexivity.
  - destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
    match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end; [reflexivity|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
      pose proof (lines_run_dead mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LC;
      destruct (lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [snd fst] in LC |- *. rewrite IH. cbn [ds_ocap]. exact LC.
Qed.

(* drain's g_capout against the g_nout it ends at (ds_no fin, the model's total sent: NO plus every byte sent). *)
Lemma drain_ocap_le : forall live mx NO CAP e h,
  NO <= ds_no (drain_fin live mx NO CAP e h) /\
  ds_ocap (drain_fin live mx NO CAP e h) <= Z.max CAP (2 * ds_no (drain_fin live mx NO CAP e h)).
Proof.
  intros live mx NO CAP e h.
  exact (drain_run_cap_le (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) 0%nat dadr0).
Qed.

(* The same with drain_contract's TOT, given g_nout's total (relay_remove_b_aux.rma_fin_no proves it). *)
Lemma drain_ocap_le_tot : forall live mx NO CAP e h,
  ds_no (drain_fin live mx NO CAP e h) =
    NO + Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) ->
  ds_ocap (drain_fin live mx NO CAP e h) <=
    Z.max CAP (2 * (NO + Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))))).
Proof.
  intros live mx NO CAP e h E. rewrite <- E. exact (proj2 (drain_ocap_le live mx NO CAP e h)).
Qed.

Lemma drain_ocap_dead : forall mx NO CAP e h, ds_ocap (drain_fin false mx NO CAP e h) = CAP.
Proof. intros mx NO CAP e h. unfold drain_fin, drain_go. rewrite drain_run_dead. reflexivity. Qed.

(* ---- relay_remove (relay_remove_b_c). ---- *)

Lemma after_drain_fin : forall lv mx NO CAP e h,
  re_eof e = 0 -> after_drain lv mx NO CAP e h = drain_fin lv mx NO CAP e h.
Proof. intros lv mx NO CAP e h E. unfold after_drain. rewrite E. reflexivity. Qed.

Lemma after_drain_init : forall lv mx NO CAP e h,
  re_eof e <> 0 -> after_drain lv mx NO CAP e h = drain_init NO CAP e h.
Proof. intros lv mx NO CAP e h E. unfold after_drain. rewrite (rc_if_f _ _ _ E). reflexivity. Qed.

Lemma after_drain_le : forall lv mx NO CAP e h,
  NO <= ds_no (after_drain lv mx NO CAP e h) /\
  ds_ocap (after_drain lv mx NO CAP e h) <= Z.max CAP (2 * ds_no (after_drain lv mx NO CAP e h)).
Proof.
  intros lv mx NO CAP e h. destruct (Z.eq_dec (re_eof e) 0) as [E|E].
  - rewrite (after_drain_fin lv mx NO CAP e h E). apply drain_ocap_le.
  - rewrite (after_drain_init lv mx NO CAP e h E). unfold drain_init. cbn [ds_no ds_ocap].
    split; [lia | apply Z.le_max_l].
Qed.

Lemma after_drain_dead : forall mx NO CAP e h, ds_ocap (after_drain false mx NO CAP e h) = CAP.
Proof.
  intros mx NO CAP e h. destruct (Z.eq_dec (re_eof e) 0) as [E|E].
  - rewrite (after_drain_fin false mx NO CAP e h E). apply drain_ocap_dead.
  - rewrite (after_drain_init false mx NO CAP e h E). reflexivity.
Qed.

(* relay_remove's g_capout against the model's g_nout after the drain and the held keys' ends. *)
Lemma remove_entry_cap_le_no : forall lv mx NO CAP e h,
  remove_entry_cap lv mx NO CAP e h <=
  Z.max CAP (2 * (ds_no (after_drain lv mx NO CAP e h) +
                  fold_right (fun xl acc => xl + 5 + acc) 0
                    (map (fun x => Z.of_nat (length x)) (ds_H (after_drain lv mx NO CAP e h))))).
Proof.
  intros lv mx NO CAP e h.
  pose proof (after_drain_le lv mx NO CAP e h) as [_ A].
  unfold remove_entry_cap. cbv zeta.
  revert A. generalize (after_drain lv mx NO CAP e h) as s. intros s A.
  pose proof (rc_xls_nonneg _ (rc_Forall_lens (ds_H s))) as X0.
  apply (rc_step CAP (ds_ocap s) _ (ds_no s)
           (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun x => Z.of_nat (length x)) (ds_H s))));
    [exact A | exact (gestures_end_cap_le_xls lv mx (ds_no s) (ds_ocap s) _ (rc_Forall_lens (ds_H s))) | lia | lia].
Qed.

(* relay_remove's g_capout against relay_remove_contract's TOT = |with_nul Ls| + keys_total (re_keys e'), given
   drain's g_nout total (rma_fin_no) and the keys e' holds (the contract's keys_texts (re_keys e') = ds_H fin when
   re_eof e = 0, re_keys e' = re_keys e otherwise). *)
Lemma remove_entry_cap_le : forall lv mx NO CAP e h ks,
  (re_eof e = 0 ->
     ds_no (drain_fin lv mx NO CAP e h) =
       NO + Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) /\
     keys_texts ks = ds_H (drain_fin lv mx NO CAP e h)) ->
  (re_eof e <> 0 -> keys_total ks = keys_total (re_keys e)) ->
  remove_entry_cap lv mx NO CAP e h <=
  Z.max CAP (2 * (NO + (Z.of_nat (length (with_nul (if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h))
                                                     else []))) + keys_total ks))).
Proof.
  intros lv mx NO CAP e h ks HE HN.
  apply (rc_mono _ _ _ _ (remove_entry_cap_le_no lv mx NO CAP e h)).
  destruct (Z.eq_dec (re_eof e) 0) as [E|E].
  - rewrite (rc_if_t _ _ _ E), (after_drain_fin lv mx NO CAP e h E).
    destruct (HE E) as [N K]. rewrite N, <- K, <- keys_total_texts. lia.
  - rewrite (rc_if_f _ _ _ E), (after_drain_init lv mx NO CAP e h E), with_nul_nil_len.
    unfold drain_init. cbn [ds_no ds_H]. rewrite <- keys_total_texts, (HN E). lia.
Qed.

Lemma remove_entry_cap_dead : forall mx NO CAP e h, remove_entry_cap false mx NO CAP e h = CAP.
Proof.
  intros mx NO CAP e h. unfold remove_entry_cap. cbv zeta.
  rewrite gestures_end_cap_dead. apply after_drain_dead.
Qed.

(* ---- relay_instance_gone (relay_instance_gone_b_c). ---- *)

(* The bytes gone_run sends for the sources ps when their drains leave the held keys kss: each source's segment. *)
Fixpoint gone_tot (pre : list Z) (ps : list (rentry * (hsrc * nat))) (kss : list (list (list Z))) : Z :=
  match ps, kss with
  | p :: r, ks :: kr => Z.of_nat (length (gone_segment pre (entry_lines (fst p) (snd p)) ks)) + gone_tot pre r kr
  | _, _ => 0
  end.

Lemma gone_tot_nonneg : forall pre ps kss, 0 <= gone_tot pre ps kss.
Proof.
  intros pre ps. induction ps as [|p ps IH]; intros [|ks kss]; cbn [gone_tot]; try lia.
  specialize (IH kss). lia.
Qed.

Lemma gone_tot_seq : forall pre (es : list rentry) (hs : list (hsrc * nat)) (kss : list (list (list Z))),
  length hs = length es -> length kss = length es ->
  Z.of_nat (length (concat (map (fun i => gone_segment pre (entry_lines (nth i es no_entry) (nth i hs no_hj))
                                                       (nth i kss []))
                                (seq 0 (length es))))) =
  gone_tot pre (combine es hs) kss.
Proof.
  intros pre es. induction es as [|e es IH]; intros hs kss Lh Lk; [reflexivity|].
  destruct hs as [|hj hs]; cbn [length] in Lh; [discriminate|]. injection Lh as Lh.
  destruct kss as [|ks kss]; cbn [length] in Lk; [discriminate|]. injection Lk as Lk.
  cbn [length seq map concat combine gone_tot nth fst snd].
  rewrite <- seq_shift, map_map. cbn [nth].
  rewrite length_app, Nat2Z.inj_add, (IH hs kss Lh Lk). reflexivity.
Qed.

Lemma concat_end5_len : forall (l : list (list Z)),
  Z.of_nat (length (concat (map (fun x => x ++ END5Z) l))) =
  fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun x => Z.of_nat (length x)) l).
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [map concat fold_right]. rewrite !length_app, !Nat2Z.inj_add. change (length END5Z) with 5%nat. lia.
Qed.

Lemma gone_segment_len : forall pre Ls ks,
  Z.of_nat (length (gone_segment pre Ls ks)) =
  Z.of_nat (length (with_nul Ls)) +
  fold_right (fun xl acc => xl + 5 + acc) 0 (map (fun x => Z.of_nat (length x)) (fst (gei pre ks))).
Proof. intros pre Ls ks. unfold gone_segment. rewrite length_app, Nat2Z.inj_add, concat_end5_len. reflexivity. Qed.

Lemma after_drain_no : forall lv mx no cap (e : rentry) (hj : hsrc * nat),
  (re_eof e = 0 -> ds_no (drain_fin lv mx no cap e (fst hj)) =
     no + Z.of_nat (length (with_nul (lines (hs_state (fst hj)) (bzs (pending_stream (fst hj))))))) ->
  ds_no (after_drain lv mx no cap e (fst hj)) = no + Z.of_nat (length (with_nul (entry_lines e hj))).
Proof.
  intros lv mx no cap e hj HD. unfold entry_lines.
  destruct (Z.eq_dec (re_eof e) 0) as [E|E].
  - rewrite (rc_if_t _ _ _ E), (after_drain_fin lv mx no cap e (fst hj) E). exact (HD E).
  - rewrite (rc_if_f _ _ _ E), (after_drain_init lv mx no cap e (fst hj) E), with_nul_nil_len.
    unfold drain_init. cbn [ds_no]. lia.
Qed.

(* The held keys' addresses follow the held keys: the key lists gone_run pairs have the same length. *)
Lemma rc_set_nth_map : forall {A B} (f : A -> B) n y l, map f (set_nth n y l) = set_nth n (f y) (map f l).
Proof.
  intros A B f n y l. revert n. induction l as [|x l IH]; intros [|n]; cbn [set_nth map]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma rc_set_nth_len : forall {A} n (y : A) l, length (set_nth n y l) = length l.
Proof.
  intros A n y l. revert n. induction l as [|x l IH]; intros [|n]; cbn [set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.

Lemma rc_last_map : forall {A B} (f : A -> B) l d, f (last l d) = last (map f l) (f d).
Proof.
  intros A B f l d. induction l as [|x l IH]; [reflexivity|]. destruct l as [|y l]; [reflexivity|].
  change (last (x :: y :: l) d) with (last (y :: l) d).
  change (last (map f (x :: y :: l)) (f d)) with (last (map f (y :: l)) (f d)). exact IH.
Qed.

Lemma rc_firstn_map : forall {A B} (f : A -> B) k l, map f (firstn k l) = firstn k (map f l).
Proof. intros A B f k. induction k as [|k IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma rc_swap_map : forall {A B} (f : A -> B) d n l, map f (swap_remove d n l) = swap_remove (f d) n (map f l).
Proof.
  intros A B f d n l. unfold swap_remove. rewrite rc_firstn_map, rc_set_nth_map, rc_last_map, length_map. reflexivity.
Qed.

Lemma rc_swap_len : forall {A} (d : A) n l, length (swap_remove d n l) = (length l - 1)%nat.
Proof. intros A d n l. unfold swap_remove. rewrite length_firstn, rc_set_nth_len. lia. Qed.

Lemma rc_geia_loop : forall f pre n (Hk : list (list Z * adrF)),
  map fst (fst (geia_loop f pre n Hk)) = fst (gei_loop f pre n (map fst Hk)) /\
  map fst (snd (geia_loop f pre n Hk)) = snd (gei_loop f pre n (map fst Hk)).
Proof.
  induction f as [|f IH]; intros pre n Hk; cbn [geia_loop gei_loop]; [split; reflexivity|].
  rewrite length_map.
  destruct (Nat.ltb n (length Hk)); [|split; reflexivity].
  replace (nth n (map fst Hk) []) with (fst (nth n Hk ([], adr0))) by (symmetry; exact (map_nth fst Hk ([], adr0) n)).
  destruct (has_prefix pre (fst (nth n Hk ([], adr0)))).
  - replace (swap_remove [] n (map fst Hk)) with (map fst (swap_remove ([], adr0) n Hk))
      by (rewrite rc_swap_map; reflexivity).
    destruct (IH pre n (swap_remove ([], adr0) n Hk)) as [I1 I2].
    destruct (geia_loop f pre n (swap_remove ([], adr0) n Hk)) as [E1 H1].
    destruct (gei_loop f pre n (map fst (swap_remove ([], adr0) n Hk))) as [E2 H2].
    cbn [fst snd map] in I1, I2 |- *. rewrite I1, I2. split; reflexivity.
  - apply IH.
Qed.

Lemma rc_fst_combine : forall {A B} (l : list A) (l' : list B), length l = length l' -> map fst (combine l l') = l.
Proof.
  intros A B l. induction l as [|x l IH]; intros [|y l'] L; cbn in L |- *; try reflexivity; try discriminate.
  injection L as L. rewrite (IH l' L). reflexivity.
Qed.

Lemma rc_geia : forall pre H (ks : list adrF), length ks = length H ->
  map fst (fst (geia pre (combine H ks))) = fst (gei pre H).
Proof.
  intros pre H ks L. unfold geia, gei. rewrite length_combine, L, Nat.min_id.
  rewrite (proj1 (rc_geia_loop _ _ _ _)), rc_fst_combine by lia. reflexivity.
Qed.

Lemma rc_seen_len : forall H ka l j ha ks, length ks = length H ->
  length (snd (snd (seen_tr H ka l j ha ks))) = length (seen_arr H l).
Proof.
  intros H ka l j ha ks L. unfold seen_tr, seen_arr.
  destruct (gesture l) as [[k x]|]; [destruct k; destruct (index_of x H) |]; cbn [fst snd];
    rewrite ?length_app, ?rc_swap_len; cbn [length]; lia.
Qed.

Lemma rc_seen_ka : forall H ka l j ha ks j' ha' ks',
  snd (fst (seen_tr H ka l j ha ks)) = snd (fst (seen_tr H ka l j' ha' ks')).
Proof.
  intros. unfold seen_tr. destruct (gesture l) as [[k x]|]; [destruct k; destruct (index_of x H) |]; reflexivity.
Qed.

Lemma rc_lines_len : forall live mx ls no cap H ka j o ha ks, length ks = length H ->
  length (snd (snd (lines_run live mx no cap H ka ls j o ha ks))) =
  length (snd (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks))))).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks L; [exact L|].
  cbn [lines_run]. cbv zeta. cbn [fst snd]. apply IH. apply rc_seen_len. exact L.
Qed.

Lemma rc_lines_state : forall live mx ls no cap H ka j o ha ks j' o' ha' ks',
  snd (fst (lines_run live mx no cap H ka ls j o ha ks)) = snd (fst (lines_run live mx no cap H ka ls j' o' ha' ks')).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks j' o' ha' ks'; [reflexivity|].
  cbn [lines_run]. cbv zeta. cbn [fst snd].
  rewrite (rc_seen_ka H ka l _ ha ks (j' + nretF (send_line_tr live mx no cap (Z.of_nat (length l) + 1) j' o'))%nat
             ha' ks').
  apply IH.
Qed.

Lemma rc_pushes_cap : forall ls n cap j v rs j' v' rs',
  snd (fst (pushes_run n cap ls j v rs)) = snd (fst (pushes_run n cap ls j' v' rs')).
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs j' v' rs'; [reflexivity|].
  cbn [pushes_run]. cbv zeta. cbn [fst snd]. apply IH.
Qed.

Lemma rc_grow_cap : forall c u j b j' b', fst (snd (grow_tr c u j b)) = fst (snd (grow_tr c u j' b')).
Proof. intros. unfold grow_tr. destruct (c - u <? 4096); reflexivity. Qed.

(* drain's model state does not depend on the addresses. *)
Lemma rc_drain_state : forall f live mx s j a j' a',
  fst (snd (drain_run f live mx s j a)) = fst (snd (drain_run f live mx s j' a')).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a j' a'; [reflexivity|].
  cbn [drain_run]. cbv zeta.
  rewrite (rc_grow_cap (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a) j' (da_buf a')).
  destruct (ds_eintr s); [cbn [fst snd]; apply IH|].
  destruct (ds_pend s) as [|r0 rs]; [reflexivity|].
  match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [reflexivity|].
  match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
  match goal with |- ?L = ?R =>
    match L with context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
    match R with context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3' ?o' ?ha' ?ks'] =>
      pose proof (rc_lines_state live mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks j3' o' ha' ks') as LS;
      destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc1 H1] ka1]] [[o1 ha1] ks1]];
      destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3' o' ha' ks')
        as [[tl' [[oc2 H2] ka2]] [[o2 ha2] ks2]]
    end end end.
  cbn [fst snd] in LS. injection LS as -> -> ->.
  match goal with |- ?L = ?R =>
    match L with context [pushes_run ?n ?c ?ls ?jp ?v ?rs] =>
    match R with context [pushes_run n c ls ?jp' ?v' ?rs'] =>
      rewrite (rc_pushes_cap ls n c jp v rs jp' v' rs') end end end.
  cbn [fst snd]. apply IH.
Qed.

Lemma rc_drain_len : forall f live mx s j a, length (da_keys a) = length (ds_H s) ->
  length (da_keys (snd (snd (drain_run f live mx s j a)))) = length (ds_H (fst (snd (drain_run f live mx s j a)))).
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a L; [exact L|].
  cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
  - cbn [snd fst]. apply IH. exact L.
  - destruct (ds_pend s) as [|r0 rs]; [exact L|].
    match goal with |- context [Z.min ?x ?y <=? 0] => destruct (Z.min x y <=? 0) end; [exact L|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
    match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
      pose proof (rc_lines_len live mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks L) as LL;
      destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
        as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
    cbn [snd fst] in LL |- *. apply IH. exact LL.
Qed.

Lemma rc_after_drain_len : forall lv mx no cap e h nm o j,
  length (da_keys (after_drain_adr lv mx no cap e h j (drain_start nm o e h))) =
  length (ds_H (after_drain lv mx no cap e h)).
Proof.
  intros lv mx no cap e h nm o j. unfold after_drain_adr, after_drain.
  assert (L0 : length (da_keys (drain_start nm o e h)) = length (ds_H (drain_init no cap e h)))
    by (unfold drain_start, drain_init, keys_texts; cbn [da_keys ds_H]; rewrite !length_map; reflexivity).
  destruct (re_eof e =? 0); [|exact L0].
  unfold drain_adr, drain_fin, drain_go.
  rewrite (rc_drain_state _ lv mx (drain_init no cap e h) 0%nat dadr0 j (drain_start nm o e h)).
  apply rc_drain_len. exact L0.
Qed.

Lemma gone_run_len : forall lv mx pre ps no cap nm j o,
  length (snd (fst (gone_run lv mx no cap pre ps nm j o))) = length ps.
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o; [reflexivity|].
  cbn [gone_run]. cbv zeta.
  match goal with |- context [gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
    pose proof (IH n c nm j1 o1) as IHr; destruct (gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
  cbn [fst snd length] in IHr |- *. rewrite IHr. reflexivity.
Qed.

(* gone_run's g_capout against its sends, given each drained source's g_nout total (rma_fin_no). *)
Lemma gone_run_cap_le : forall lv mx pre (ps : list (rentry * (hsrc * nat))) no cap nm j o,
  Forall (fun p => re_eof (fst p) = 0 -> forall no cap,
            ds_no (drain_fin lv mx no cap (fst p) (fst (snd p))) =
            no + Z.of_nat (length (with_nul (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p)))))))) ps ->
  snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) <=
  Z.max cap (2 * (no + gone_tot pre ps (map ds_H (snd (fst (gone_run lv mx no cap pre ps nm j o)))))).
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o HF.
  - cbn [gone_run fst snd]. apply Z.le_max_l.
  - apply Forall_cons_iff in HF as [H0 HR]. cbn [fst snd] in H0.
    pose proof (after_drain_no lv mx no cap e hj (fun E => H0 E no cap)) as NO1.
    pose proof (after_drain_le lv mx no cap e (fst hj)) as [_ A1].
    pose proof (rc_after_drain_len lv mx no cap e (fst hj) nm o j) as LK.
    cbn [gone_run]. cbv zeta.
    revert NO1 A1 LK.
    generalize (after_drain_adr lv mx no cap e (fst hj) j (drain_start nm o e (fst hj))) as a.
    generalize (after_drain lv mx no cap e (fst hj)) as s. intros s a NO1 A1 LK.
    pose proof (rc_geia pre (ds_H s) (da_keys a) LK) as KG.
    assert (MX : map fst (map (fun x => (Z.of_nat (length (fst x)), snd x)) (fst (geia pre (combine (ds_H s) (da_keys a))))) =
                 map (fun x => Z.of_nat (length x)) (fst (gei pre (ds_H s)))).
    { rewrite map_map, <- KG, map_map. reflexivity. }
    match goal with |- context [keys_end_run lv mx (ds_no s) (ds_ocap s) ?xks ?j1 ?o1] =>
      pose proof (keys_end_run_cap_le lv mx xks (ds_no s) (ds_ocap s) j1 o1) as KB end.
    rewrite MX in KB. rewrite MX.
    specialize (KB ltac:(apply Forall_map, Forall_forall; intros x _; cbn [fst]; lia)).
    pose proof (rc_xls_nonneg _ (rc_Forall_lens (fst (gei pre (ds_H s))))) as X0.
    match goal with |- context [gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
      pose proof (IH n c nm j1 o1 HR) as IHr; destruct (gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
    cbn [fst snd map gone_tot] in IHr |- *.
    rewrite gone_segment_len.
    pose proof (gone_tot_nonneg pre r (map ds_H ss)) as R0.
    revert X0 KB IHr. generalize (map (fun x => Z.of_nat (length x)) (fst (gei pre (ds_H s)))) as xls.
    intros xls X0 KB IHr.
    match type of KB with ?c1 <= _ =>
      apply (rc_mono c' cap (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 xls + gone_tot pre r (map ds_H ss)));
      [apply (rc_step cap c1 c' (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 xls)
                (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 xls + gone_tot pre r (map ds_H ss))) | lia]
    end.
    + apply (rc_step cap (ds_ocap s) _ (ds_no s) (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 xls));
        [exact A1 | exact KB | lia | lia].
    + exact IHr.
    + lia.
    + lia.
Qed.

(* relay_instance_gone's g_capout against relay_instance_gone_contract's TOT, given each drained source's g_nout
   total (rma_fin_no) and the contract's kss (nth i kss [] = ds_H (nth i ss _)). *)
Lemma gone_cap_le : forall lv mx NO CAP pre (es : list rentry) (hs : list (hsrc * nat)) (kss : list (list (list Z))),
  length hs = length es -> length kss = length es ->
  Forall (fun p => re_eof (fst p) = 0 -> forall no cap,
            ds_no (drain_fin lv mx no cap (fst p) (fst (snd p))) =
            no + Z.of_nat (length (with_nul (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))))))
         (combine es hs) ->
  (forall i, (i < length es)%nat ->
     nth i kss [] = ds_H (nth i (gone_states lv mx NO CAP pre es hs)
                              (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))))) ->
  gone_cap lv mx NO CAP pre es hs <=
  Z.max CAP (2 * (NO + Z.of_nat (length (concat (map (fun i => gone_segment pre (entry_lines (nth i es no_entry)
                                                                                  (nth i hs no_hj)) (nth i kss []))
                                                      (seq 0 (length es))))))).
Proof.
  intros lv mx NO CAP pre es hs kss Lh Lk HF HK.
  rewrite (gone_tot_seq pre es hs kss Lh Lk).
  assert (LS : length (gone_states lv mx NO CAP pre es hs) = length es).
  { unfold gone_states. rewrite gone_run_len, length_combine, Lh. apply Nat.min_id. }
  assert (KE : kss = map ds_H (gone_states lv mx NO CAP pre es hs)).
  { apply (rc_nth_ext kss _ [] []).
    - rewrite length_map, LS. exact Lk.
    - intros i Hi. rewrite Lk in Hi. rewrite (HK i Hi).
      rewrite (nth_indep (map ds_H (gone_states lv mx NO CAP pre es hs)) []
                 (ds_H (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj)))))
        by (rewrite length_map, LS; exact Hi).
      rewrite map_nth. reflexivity. }
  rewrite KE. unfold gone_cap, gone_states.
  exact (gone_run_cap_le lv mx pre (combine es hs) NO CAP (fun _ => adr0) 0%nat adr0 HF).
Qed.

Lemma gone_run_dead : forall mx pre ps no cap nm j o, snd (fst (fst (gone_run false mx no cap pre ps nm j o))) = cap.
Proof.
  intros mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o; [reflexivity|].
  cbn [gone_run]. cbv zeta.
  match goal with |- context [gone_run false mx ?n ?c pre r nm ?j1 ?o1] =>
    pose proof (IH n c nm j1 o1) as IHr; destruct (gone_run false mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
  cbn [fst snd] in IHr |- *. rewrite IHr, keys_end_run_dead. apply after_drain_dead.
Qed.

Lemma gone_cap_dead : forall mx NO CAP pre es hs, gone_cap false mx NO CAP pre es hs = CAP.
Proof. intros mx NO CAP pre es hs. unfold gone_cap. apply gone_run_dead. Qed.
