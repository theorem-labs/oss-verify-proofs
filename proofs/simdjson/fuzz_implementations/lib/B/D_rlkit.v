(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs D_kit D_auxv D_libiface D_clx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma firstn_app_skipn' : forall {X} (l : list X) n k, (n <= length l)%nat ->
  firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof.
  intros X l n. revert l. induction n as [|n IH]; intros l k Hn; [reflexivity|].
  destruct l as [|x l]; [cbn in Hn; lia|]. cbn. f_equal. apply IH. cbn in Hn. lia.
Qed.

Lemma filter_idem : forall {X} (f : X -> bool) (l : list X), List.filter f (List.filter f l) = List.filter f l.
Proof.
  intros X f l. induction l as [|x l IH]; [reflexivity|]. cbn. destruct (f x) eqn:E; cbn; [rewrite E, IH; reflexivity| exact IH].
Qed.

Lemma fd_insert_twice : forall F k e1 e2, fd_insert (fd_insert F k e1) k e2 = fd_insert F k e2.
Proof.
  intros F k e1 e2. unfold fd_insert. cbn. f_equal.
  replace (negb (bv_eqb k k)) with false by (unfold bv_eqb; rewrite Z.eqb_refl; reflexivity). cbn. apply filter_idem.
Qed.

Lemma fd_lookup_insert_same : forall F k e, fd_lookup (fd_insert F k e) k = Some e.
Proof. intros F k e. unfold fd_insert. cbn. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma wr_at_sub : forall m a n a' n', wr_at bsegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma stk_wr : forall m lo hi a n, stk bsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at bsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

Section Checked.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Lemma stage_static : forall i, 0 <= i < 65536 -> client_static (g_read_stage + i).
Proof. intros i Hi. apply client_static_intro. unfold g_read_stage. lia. Qed.

Lemma checked_dst_stage : forall Σ m sp n, ART RT Σ m -> stk bsegs m g_read_stage (g_read_stage + 65536) ->
  0 <= n <= 65536 -> checked_dst RT Σ m sp g_read_stage n.
Proof using AF.
  intros Σ m sp n HA ST Hn. split; [| split].
  - intros Hp. split.
    + apply (af_acc_static RT AF Σ m _ _ HA); [unfold g_read_stage; lia|]. intros i Hi. split; [apply stage_static; lia| unfold g_read_stage; lia].
    + right; right; right. unfold g_read_stage, SEGTOP_A. lia.
  - intros i Hi. right; left. apply stage_static. lia.
  - apply (stk_wr m g_read_stage (g_read_stage + 65536)); [exact ST| lia| lia| lia].
Qed.

Lemma checked_src_stage : forall Σ m sp lo n, ART RT Σ m -> 0 <= n <= 65536 -> SEGTOP_A <= lo ->
  checked_src RT Σ m sp lo g_read_stage n.
Proof using AF.
  intros Σ m sp lo n HA Hn Hlo. split.
  - intros Hp. split.
    + apply (af_acc_static RT AF Σ m _ _ HA); [unfold g_read_stage; lia|]. intros i Hi. split; [apply stage_static; lia| unfold g_read_stage; lia].
    + right; right; right. unfold g_read_stage, SEGTOP_A. lia.
  - left. unfold g_read_stage, SEGTOP_A in *. lia.
Qed.

Lemma checked_dst_live : forall Σ m sp p k d n, ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= d -> d + n <= p + k -> 0 <= n ->
  checked_dst RT Σ m sp d n.
Proof using AF.
  intros Σ m sp p k d n HA Hin H1 H2 Hn. destruct (af_acc_live RT AF Σ m p k HA Hin) as [WR AC]. split; [| split].
  - intros Hp. split; [apply (acc_sub bsegs m p k d n AC); lia|]. left. exists p, k. split; [exact Hin| lia].
  - intros i Hi. right; right; left. exists p, k. split; [exact Hin| lia].
  - apply (wr_at_sub m p k d n WR); lia.
Qed.

Lemma checked_src_live : forall Σ m sp lo p k s n, ART RT Σ m -> In (p, k) (rt_live RT Σ) -> p <= s -> s + n <= p + k ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> checked_src RT Σ m sp lo s n.
Proof using AF.
  intros Σ m sp lo p k s n HA Hin H1 H2 Hlo. destruct (af_acc_live RT AF Σ m p k HA Hin) as [WR AC].
  pose proof (af_live_range RT AF Σ m p k HA Hin) as (R1 & R2 & R3). split.
  - intros Hp. split; [apply (acc_sub bsegs m p k s n AC); lia|]. left. exists p, k. split; [exact Hin| lia].
  - left. lia.
Qed.

Lemma checked_src_stack : forall Σ m sp lo s n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN + 64 <= s -> s + n <= USTACK_TOP - 16 ->
  bv_unsigned sp <= s -> checked_src RT Σ m sp lo s n.
Proof using AF.
  intros Σ m sp lo s n HA H1 H2 H3. split.
  - intros Hp. split; [apply (af_acc_stack RT AF Σ m s n HA); unfold USTACK_TOP in *; lia|]. right; right; left. lia.
  - right. exact H3.
Qed.

Lemma agree_stack_pres : forall live frames sp m m', rt_pres live frames sp m m' ->
  agree_on (fun x => sp <= x < USTACK_TOP) m m'.
Proof. intros live frames sp m m' H. apply (agree_of_pres _ _ _ _ _ _ H). intros x Hx. left. exact Hx. Qed.

Lemma agree_stack_pres_ex : forall live frames sp d n m m', rt_pres_ex live frames sp d n m m' -> d + n <= sp ->
  agree_on (fun x => sp <= x < USTACK_TOP) m m'.
Proof.
  intros live frames sp d n m m' H Hd. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ H). intros x Hx. split; [left; exact Hx| lia].
Qed.

Lemma agree_stack_pres_fp : forall live frames sp W m m', rt_pres_fp live frames sp W m m' ->
  (forall x, sp <= x < USTACK_TOP -> outside W x) -> agree_on (fun x => sp <= x < USTACK_TOP) m m'.
Proof.
  intros live frames sp W m m' H HW. apply (agree_of_pres_fp _ _ _ _ _ _ _ H). intros x Hx. split; [left; exact Hx| apply HW, Hx].
Qed.

Lemma agree_stack_munch : forall W sp m m', munch W m m' -> (forall x, sp <= x < USTACK_TOP -> outside W x) ->
  agree_on (fun x => sp <= x < USTACK_TOP) m m'.
Proof. intros W sp m m' H HW. apply (agree_of_munch _ _ _ _ H). exact HW. Qed.

End Checked.

Section Transport.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable XENV : mem -> Prop.
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Hypothesis AF : art_facts RT.

Lemma argv_agree : forall m m' ap, argv_rep argvb m ap -> agree_on (fun x => ap <= x < USTACK_TOP) m m' -> wmono bsegs m m' ->
  argv_rep argvb m' ap.
Proof.
  intros m m' ap (ptrs & ARR & L & STR & SLKS) AG WM. exists ptrs. split; [| split; [exact L| split]].
  - apply (u64arr_agree bsegs m m' _ _ ARR); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    pose proof (u64arr_bound bsegs m ap ptrs ARR). rewrite L in *. split; [lia|].
    destruct (nth_error argvb 0) as [s0|] eqn:E0; [| apply nth_error_None in E0; lia].
    destruct (nth_error ptrs 0) as [p|] eqn:Ep; [| apply nth_error_None in Ep; lia].
    destruct (STR 0%nat s0 p E0 Ep) as (_ & P1 & P2). unfold USTACK_TOP in *. lia.
  - intros i s p Hs Hp. destruct (STR i s p Hs Hp) as (B & P1 & P2). split; [|split; assumption].
    apply (bytes_at_agree bsegs m m' _ _ B). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    rewrite length_app in Hx. cbn in Hx. pose proof (u64arr_bound bsegs m ap ptrs ARR). unfold USTACK_TOP in *. lia.
  - intros i s p Hs Hp. destruct (STR i s p Hs Hp) as (B & P1 & P2). destruct (SLKS i s p Hs Hp) as (sl & SL & SLM & SLB).
    exists sl. split; [| split; assumption].
    apply (bytes_at_agree bsegs m m' _ _ SL). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    pose proof (u64arr_bound bsegs m ap ptrs ARR). unfold USTACK_TOP in *. lia.
Qed.

Lemma main_frame_agree : forall m m' usp c0 c1 c2 c3 c4 c5 c6 c7, main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> agree_on auxc m m' -> wmono bsegs m m' -> main_frame m' usp c0 c1 c2 c3 c4 c5 c6 c7.
Proof.
  intros m m' usp c0 c1 c2 c3 c4 c5 c6 c7 ((junk & FR) & AUX) AG AGC WM.
  pose proof AUX as (av & x16 & x11 & rnd & _ & _ & HB). split; [exists junk|].
  - apply (rw_cells_agree bsegs m m' _ _ FR); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
  - apply (el_auxv_agree usp m m' AUX AGC). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. lia.
Qed.

Lemma MAINCTX_agree : forall Σ Σ' so so' usp ap c0 c1 c2 c3 c4 c5 c6 c7 m m',
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ so usp ap c0 c1 c2 c3 c4 c5 c6 c7 m ->
  ART RT Σ' m' -> mem_inv bsegs m' -> wmono bsegs m m' -> stk bsegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 80) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> CLX OUT_rep ERR_rep XENV LIB so' m' ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> agree_on auxc m m' ->
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ' so' usp ap c0 c1 c2 c3 c4 c5 c6 c7 m'.
Proof.
  intros Σ Σ' so so' usp ap c0 c1 c2 c3 c4 c5 c6 c7 m m'
    (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) ART1 MI1 WM ST1 ESP CLX1 AG AGC.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (argv_agree m m' ap ARGV0); [eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in *; lia| exact WM]|].
  split; [exact (main_frame_agree m m' usp _ _ _ _ _ _ _ _ FR0 AG AGC WM)|].
  rewrite ESP. split; [exact ST1|]. tauto.
Qed.

Lemma main_frame_agree_nw : forall m m' usp c0 c1 c2 c3 c4 c5 c6 c7, main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7 ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> agree_on auxc m m' -> main_frame m' usp c0 c1 c2 c3 c4 c5 c6 c7.
Proof.
  intros m m' usp c0 c1 c2 c3 c4 c5 c6 c7 ((junk & FR) & AUX) AG AGC.
  pose proof AUX as (av & x16 & x11 & rnd & _ & _ & HB). split; [exists junk|].
  - apply (rw_cells_agree_nw bsegs m m' _ _ FR). eapply agree_sub; [exact AG|]. intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
  - apply (el_auxv_agree usp m m' AUX AGC). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. lia.
Qed.

Lemma argv_agree_nw : forall m m' ap, argv_rep argvb m ap -> agree_on (fun x => ap <= x < USTACK_TOP) m m' -> argv_rep argvb m' ap.
Proof.
  intros m m' ap (ptrs & ARR & L & STR & SLKS) AG. exists ptrs. split; [| split; [exact L| split]].
  - apply (u64arr_agree_nw bsegs m m' _ _ ARR). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    pose proof (u64arr_bound bsegs m ap ptrs ARR). rewrite L in *. split; [lia|].
    destruct (nth_error argvb 0) as [s0|] eqn:E0; [| apply nth_error_None in E0; lia].
    destruct (nth_error ptrs 0) as [p|] eqn:Ep; [| apply nth_error_None in Ep; lia].
    destruct (STR 0%nat s0 p E0 Ep) as (_ & P1 & P2). unfold USTACK_TOP in *. lia.
  - intros i s p Hs Hp. destruct (STR i s p Hs Hp) as (B & P1 & P2). split; [|split; assumption].
    apply (bytes_at_agree bsegs m m' _ _ B). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    rewrite length_app in Hx. cbn in Hx. pose proof (u64arr_bound bsegs m ap ptrs ARR). unfold USTACK_TOP in *. lia.
  - intros i s p Hs Hp. destruct (STR i s p Hs Hp) as (B & P1 & P2). destruct (SLKS i s p Hs Hp) as (sl & SL & SLM & SLB).
    exists sl. split; [| split; assumption].
    apply (bytes_at_agree bsegs m m' _ _ SL). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    pose proof (u64arr_bound bsegs m ap ptrs ARR). unfold USTACK_TOP in *. lia.
Qed.

Lemma MAINCTX_agree_nw : forall Σ Σ' so so' usp ap c0 c1 c2 c3 c4 c5 c6 c7 m m',
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ so usp ap c0 c1 c2 c3 c4 c5 c6 c7 m ->
  ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (rt_sp0 RT Σ - STACK_WIN) (usp - 80) ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> CLX OUT_rep ERR_rep XENV LIB so' m' ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> agree_on auxc m m' ->
  MAINCTX RT OUT_rep ERR_rep XENV LIB argvb Σ' so' usp ap c0 c1 c2 c3 c4 c5 c6 c7 m'.
Proof.
  intros Σ Σ' so so' usp ap c0 c1 c2 c3 c4 c5 c6 c7 m m'
    (ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) ART1 MI1 ST1 ESP CLX1 AG AGC.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|].
  split; [apply (argv_agree_nw m m' ap ARGV0); eapply agree_sub; [exact AG|]; intros x Hx; cbv beta in *; lia|].
  split; [exact (main_frame_agree_nw m m' usp _ _ _ _ _ _ _ _ FR0 AG AGC)|].
  rewrite ESP. split; [exact ST1|]. tauto.
Qed.

Lemma path_agree : forall m m' usp path s, bytes_at bsegs m path s -> usp - 80 <= path -> path + Z.of_nat (length s) <= USTACK_TOP ->
  agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m' -> bytes_at bsegs m' path s.
Proof.
  intros m m' usp path s B H1 H2 AG. apply (bytes_at_agree bsegs m m' _ _ B). eapply agree_sub; [exact AG|].
  intros x Hx. cbv beta in *. lia.
Qed.

End Transport.
