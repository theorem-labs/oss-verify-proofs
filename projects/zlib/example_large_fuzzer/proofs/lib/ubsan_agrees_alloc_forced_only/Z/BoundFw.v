(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees DeflateLz FillWinModel RefDeflSafeLW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fwT (s : deflate_state) : Z := wrap64 (cs_total_in (ds_strm s) - cs_next_in (ds_strm s)).

Lemma wrap64_sub_wrap64_l : forall a b, wrap64 (wrap64 a - b) = wrap64 (a - b).
Proof. intros a b. rewrite !wrap64_mod. apply Zminus_mod_idemp_l. Qed.

Lemma fwT_read_buf : forall s dst n, fwT (fst (read_buf s dst n)) = fwT s.
Proof.
  intros s dst n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct dst; dsred; (destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]); unfold fwT, cs_emit; dsred;
    rewrite wrap64_sub_wrap64_l; f_equal; lia.
Qed.

Lemma fwT_insert : forall n s str, fwT (fill_window_insert n s str) = fwT s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[fwT update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold fwT; dsred; reflexivity|].
  rewrite IH. unfold fwT; dsred; reflexivity.
Qed.

Lemma fwT_slide : forall s ws more, fwT (fw_slide s ws more) = fwT s.
Proof. intros s ws more. unfold fw_slide, slide_hash. destruct (_ <? _); unfold fwT; dsred; reflexivity. Qed.

Lemma fwT_body : forall s ws, fwT (fst (fill_window_body s ws)) = fwT s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  set (s1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s ws (fw_more s) else s).
  set (m1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ws) else fw_more s).
  assert (E1 : fwT s1 = fwT s) by (subst s1; destruct (_ <=? _); [apply fwT_slide | reflexivity]).
  replace (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [exact E1|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (fwT_read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as E2'. rewrite E2 in E2'. cbn [fst] in E2'.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - rewrite fwT_insert. rewrite <- E1, <- E2'. unfold fwT; dsred; reflexivity.
  - rewrite <- E1, <- E2'. unfold fwT; dsred; reflexivity.
Qed.

Lemma fwT_loop : forall n s ws, fwT (fill_window_loop n s ws) = fwT s.
Proof.
  induction n as [|n IH]; intros s ws; [reflexivity|].
  rewrite fill_window_loop_step. destruct (fill_window_body s ws) as [s1 b] eqn:E.
  pose proof (fwT_body s ws) as E'. rewrite E in E'. cbn [fst] in E'.
  destruct b; [exact E'|]. destruct (_ && _); [rewrite IH; exact E' | exact E'].
Qed.

Lemma fwT_high : forall s, fwT (fill_window_high s) = fwT s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [|reflexivity]. destruct (_ <? _); [unfold fwT; dsred; reflexivity|].
  destruct (_ <? _); [unfold fwT; dsred; reflexivity | reflexivity].
Qed.

Lemma fwT_fill_window : forall s, fwT (fill_window s) = fwT s.
Proof. intros s. unfold fill_window. rewrite fwT_high, fwT_loop. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fwB (s : deflate_state) := (ds_strstart s, ds_block_start s, ds_w_size s).
Definition nbP (s : deflate_state) : Prop := ds_block_start s < 0 -> ds_w_size s - MIN_LOOKAHEAD <= ds_strstart s.

Lemma nbP_fwB : forall s s', fwB s' = fwB s -> nbP s -> nbP s'.
Proof. intros s s' E H. unfold fwB in E. injection E as E1 E2 E3. unfold nbP in *. rewrite E1, E2, E3. exact H. Qed.

Lemma fwB_read_buf : forall s off n, fwB (fst (read_buf s (RB_window off) n)) = fwB s.
Proof.
  intros s off n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; unfold fwB; dsred; reflexivity.
Qed.

Lemma fwB_insert : forall n s str, fwB (fill_window_insert n s str) = fwB s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[fwB update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold fwB; dsred; reflexivity|].
  rewrite IH. unfold fwB; dsred; reflexivity.
Qed.

Lemma nbP_body : forall s, nbP s -> nbP (fst (fill_window_body s (ds_w_size s))).
Proof.
  intros s H. rewrite fill_window_body_eq.
  set (s1 := if ds_w_size s + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s (ds_w_size s) (fw_more s) else s).
  set (m1 := if ds_w_size s + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ds_w_size s) else fw_more s).
  assert (P1 : nbP s1).
  { subst s1. destruct (Z.leb_spec (ds_w_size s + (ds_w_size s - MIN_LOOKAHEAD)) (ds_strstart s)); [| exact H].
    unfold fw_slide, slide_hash. destruct (_ <? _); unfold nbP; dsred; intros _; lia. }
  replace (if ds_w_size s + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s
           then (fw_slide s (ds_w_size s) (fw_more s), wrap32 (fw_more s + ds_w_size s)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [exact P1|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (fwB_read_buf s1 (ds_strstart s1 + ds_lookahead s1) m1) as E2'. rewrite E2 in E2'. cbn [fst] in E2'.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - eapply nbP_fwB; [| exact P1]. rewrite fwB_insert. rewrite <- E2'. unfold fwB; dsred; reflexivity.
  - eapply nbP_fwB; [| exact P1]. rewrite <- E2'. unfold fwB; dsred; reflexivity.
Qed.

Lemma w_size_body : forall s ws, ds_w_size (fst (fill_window_body s ws)) = ds_w_size s.
Proof.
  intros s ws. pose proof (fwG_body s ws) as E. unfold fwG in E.
  injection E as E _ _ _ _ _ _. (* [comment removed for export] *) exact E.
Qed.

Lemma nbP_loop : forall n s, nbP s -> nbP (fill_window_loop n s (ds_w_size s)).
Proof.
  induction n as [|n IH]; intros s H; [exact H|].
  rewrite fill_window_loop_step. pose proof (nbP_body s H) as B. pose proof (w_size_body s (ds_w_size s)) as W.
  destruct (fill_window_body s (ds_w_size s)) as [s1 b] eqn:E. cbn [fst] in B, W.
  destruct b; [exact B|]. destruct (_ && _); [| exact B]. rewrite <- W. apply IH. exact B.
Qed.

Lemma nbP_high : forall s, nbP s -> nbP (fill_window_high s).
Proof.
  intros s H. unfold fill_window_high.
  destruct (_ <? _); [|exact H]. destruct (_ <? _); [unfold nbP in *; dsred; exact H|].
  destruct (_ <? _); [unfold nbP in *; dsred; exact H | exact H].
Qed.

Lemma nbP_fill_window : forall s, nbP s -> nbP (fill_window s).
Proof. intros s H. unfold fill_window. apply nbP_high. apply nbP_loop. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CF (s : deflate_state) := (ds_level s, ds_strategy s, ds_wrap s, ds_status s, fwT s).

Lemma CF_fields : forall s s', CF s' = CF s ->
  ds_level s' = ds_level s /\ ds_strategy s' = ds_strategy s /\ ds_wrap s' = ds_wrap s /\ ds_status s' = ds_status s /\ fwT s' = fwT s.
Proof. intros s s' E. unfold CF in E. injection E as E1 E2 E3 E4 E5. auto. Qed.

(* [comment removed for export] *)
Definition CF4 (s : deflate_state) := (ds_level s, ds_strategy s, ds_wrap s, ds_status s).
Lemma CF_split : forall s s', CF4 s' = CF4 s -> fwT s' = fwT s -> CF s' = CF s.
Proof. intros s s' E4 ET. unfold CF4 in E4. injection E4 as E1 E2 E3 E4. unfold CF. rewrite E1, E2, E3, E4, ET. reflexivity. Qed.

Lemma CF4_read_buf : forall s dst n, CF4 (fst (read_buf s dst n)) = CF4 s.
Proof.
  intros s dst n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct dst; dsred; (destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]); unfold CF4; dsred; reflexivity.
Qed.

Lemma CF4_insert : forall n s str, CF4 (fill_window_insert n s str) = CF4 s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[CF4 update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold CF4; dsred; reflexivity|].
  rewrite IH. unfold CF4; dsred; reflexivity.
Qed.

Lemma CF4_slide : forall s ws more, CF4 (fw_slide s ws more) = CF4 s.
Proof. intros s ws more. unfold fw_slide, slide_hash. destruct (_ <? _); unfold CF4; dsred; reflexivity. Qed.

Lemma CF4_body : forall s ws, CF4 (fst (fill_window_body s ws)) = CF4 s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  set (s1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s ws (fw_more s) else s).
  set (m1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ws) else fw_more s).
  assert (E1 : CF4 s1 = CF4 s) by (subst s1; destruct (_ <=? _); [apply CF4_slide | reflexivity]).
  replace (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [exact E1|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (CF4_read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as E2'. rewrite E2 in E2'. cbn [fst] in E2'.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - rewrite CF4_insert. rewrite <- E1, <- E2'. unfold CF4; dsred; reflexivity.
  - rewrite <- E1, <- E2'. unfold CF4; dsred; reflexivity.
Qed.

Lemma CF4_loop : forall n s ws, CF4 (fill_window_loop n s ws) = CF4 s.
Proof.
  induction n as [|n IH]; intros s ws; [reflexivity|].
  rewrite fill_window_loop_step. destruct (fill_window_body s ws) as [s1 b] eqn:E.
  pose proof (CF4_body s ws) as E'. rewrite E in E'. cbn [fst] in E'.
  destruct b; [exact E'|]. destruct (_ && _); [rewrite IH; exact E' | exact E'].
Qed.

Lemma CF4_high : forall s, CF4 (fill_window_high s) = CF4 s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [|reflexivity]. destruct (_ <? _); [unfold CF4; dsred; reflexivity|].
  destruct (_ <? _); [unfold CF4; dsred; reflexivity | reflexivity].
Qed.

Lemma CF_fill_window : forall s, CF (fill_window s) = CF s.
Proof.
  intros s. apply CF_split; [| apply fwT_fill_window]. unfold fill_window. rewrite CF4_high, CF4_loop. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GZ (s : deflate_state) : Z := ds_gzhead s.
Definition INS (s : deflate_state) : Z := ds_insert s.

Lemma GZ_read_buf : forall s dst n, GZ (fst (read_buf s dst n)) = GZ s.
Proof.
  intros s dst n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct dst; dsred; (destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]); unfold GZ; dsred; reflexivity.
Qed.
Lemma INS_read_buf : forall s dst n, INS (fst (read_buf s dst n)) = INS s.
Proof.
  intros s dst n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct dst; dsred; (destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]); unfold INS; dsred; reflexivity.
Qed.

Lemma GZ_insert : forall n s str, GZ (fill_window_insert n s str) = GZ s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[GZ update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold GZ; dsred; reflexivity|].
  rewrite IH. unfold GZ; dsred; reflexivity.
Qed.
Lemma INS_insert0 : forall n s str, INS s = 0 -> fill_window_insert n s str = s.
Proof.
  intros n s str H. destruct n as [|n]; [reflexivity|].
  cbn -[update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  unfold INS in H. rewrite H. reflexivity.
Qed.

Lemma GZ_slide : forall s ws more, GZ (fw_slide s ws more) = GZ s.
Proof. intros s ws more. unfold fw_slide, slide_hash. destruct (_ <? _); unfold GZ; dsred; reflexivity. Qed.
(* [comment removed for export] *)
Lemma INS_slide0 : forall s ws more, INS s = 0 -> ws <= ds_strstart s -> INS (fw_slide s ws more) = 0.
Proof.
  intros s ws more H Hs. unfold INS in *. unfold fw_slide, slide_hash.
  destruct (_ <? _) eqn:E; dsred; [| exact H].
  dsred in E. rewrite H in E. apply Z.ltb_lt in E. lia.
Qed.

Lemma GZINS_body : forall s ws, GZ (fst (fill_window_body s ws)) = GZ s
  /\ (INS s = 0 -> MIN_LOOKAHEAD <= ds_w_size s -> INS (fst (fill_window_body s ws)) = 0).
Proof.
  intros s ws. rewrite fill_window_body_eq.
  set (s1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s ws (fw_more s) else s).
  set (m1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ws) else fw_more s).
  assert (E1 : GZ s1 = GZ s /\ (INS s = 0 -> MIN_LOOKAHEAD <= ds_w_size s -> INS s1 = 0)).
  { subst s1. destruct (Z.leb_spec (ws + (ds_w_size s - MIN_LOOKAHEAD)) (ds_strstart s)) as [L|L].
    - split; [apply GZ_slide | intros H Hw; apply INS_slide0; [exact H | lia]].
    - split; [reflexivity | intros H _; exact H]. }
  destruct E1 as [G1 I1].
  replace (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [split; [exact G1 | exact I1]|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (GZ_read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as G2. rewrite E2 in G2. cbn [fst] in G2.
  pose proof (INS_read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as I2. rewrite E2 in I2. cbn [fst] in I2.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - split.
    + rewrite GZ_insert. rewrite <- G1, <- G2. unfold GZ; dsred; reflexivity.
    + intros H Hw. rewrite INS_insert0; [unfold INS; dsred; fold (INS s2); rewrite I2; exact (I1 H Hw)|].
      unfold INS; dsred. fold (INS s2). rewrite I2. exact (I1 H Hw).
  - split; [rewrite <- G1, <- G2; unfold GZ; dsred; reflexivity|].
    intros H Hw. unfold INS; dsred. fold (INS s2). rewrite I2. exact (I1 H Hw).
Qed.

Lemma GZINS_loop : forall n s, GZ (fill_window_loop n s (ds_w_size s)) = GZ s
  /\ (INS s = 0 -> MIN_LOOKAHEAD <= ds_w_size s -> INS (fill_window_loop n s (ds_w_size s)) = 0).
Proof.
  induction n as [|n IH]; intros s; [split; [reflexivity | intros H _; exact H]|].
  rewrite fill_window_loop_step. destruct (GZINS_body s (ds_w_size s)) as [G I]. pose proof (w_size_body s (ds_w_size s)) as W.
  destruct (fill_window_body s (ds_w_size s)) as [s1 b] eqn:E. cbn [fst] in G, I, W.
  destruct b; [split; assumption|]. destruct (_ && _); [| split; assumption].
  replace (fill_window_loop n s1 (ds_w_size s)) with (fill_window_loop n s1 (ds_w_size s1)) by (rewrite W; reflexivity).
  destruct (IH s1) as [G' I']. split; [rewrite G'; exact G|].
  intros H Hw. apply I'; [exact (I H Hw) | rewrite W; exact Hw].
Qed.

Lemma GZINS_high : forall s, GZ (fill_window_high s) = GZ s /\ INS (fill_window_high s) = INS s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [|split; reflexivity]. destruct (_ <? _); [unfold GZ, INS; dsred; split; reflexivity|].
  destruct (_ <? _); [unfold GZ, INS; dsred; split; reflexivity | split; reflexivity].
Qed.

Lemma GZINS_fill_window : forall s, GZ (fill_window s) = GZ s /\ (INS s = 0 -> MIN_LOOKAHEAD <= ds_w_size s -> INS (fill_window s) = 0).
Proof.
  intros s. unfold fill_window. cbv zeta. destruct (GZINS_high (fill_window_loop 263%nat s (ds_w_size s))) as [G I].
  destruct (GZINS_loop 263%nat s) as [G' I'].
  split; [rewrite G; exact G' | intros H Hw; rewrite I; exact (I' H Hw)].
Qed.
