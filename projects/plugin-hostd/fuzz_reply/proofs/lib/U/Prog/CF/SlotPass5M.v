(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names, addresses and numbers changed; 655 of its 764 lines of code are new or changed and 1120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_instance_gone_b_seg.v, with its module paths and module names changed; 188 of its 239 lines of code are new or changed and 713 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass5A.v, with its module paths and module names changed; 957 of its 1013 lines of code are new or changed and 183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5Check.v, with its module paths changed; 192 of its 256 lines of code are new or changed and 949 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF ListTr RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c relay_remove_b_c SlotInv SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_instance_gone_b_c RelayCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import check_no_loss_c check_shape_ends_c SlotPass2Check SlotPass4C SlotPass5Run relay_remove_b_aux SlotPass5Check relay_instance_gone_b_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma g5m_gesture_begin : forall l x, gesture l = Some (GBegin, x) ->
  Z.of_nat (length x) + 5 <= Z.of_nat (length l) + 1.
Proof.
  intros l x G. unfold gesture in G.
  destruct (list_eqb (firstn 13 l) K_GESTURE && Z.eqb (nth 13 l 0) SPACE && Nat.ltb 13 (length l)); [|discriminate].
  destruct (last_space_from 0 l) as [j|]; [|discriminate].
  destruct (Nat.ltb 13 j); [|discriminate].
  destruct (list_eqb (skipn (S j) l) W_BEGIN) eqn:EB.
  - injection G as EX. subst x. unfold list_eqb in EB.
    destruct (list_eq_dec Z.eq_dec (skipn (S j) l) W_BEGIN) as [Es|]; [|discriminate].
    pose proof (f_equal (@length Z) Es) as LE. rewrite length_skipn in LE. cbn [W_BEGIN length] in LE.
    rewrite length_firstn. lia.
  - destruct (list_eqb (skipn (S j) l) W_END); discriminate.
Qed.

Lemma g5m_w_one : forall x, g5_w [x] = Z.of_nat (length x) + 5.
Proof. intros x. unfold g5_w. cbn [map concat]. rewrite app_nil_r, length_app, Nat2Z.inj_add. reflexivity. Qed.

Lemma g5m_seen_w : forall H l, g5_w (seen_arr H l) <= g5_w H + Z.of_nat (length l) + 1.
Proof.
  intros H l. unfold seen_arr. destruct (gesture l) as [[k x]|] eqn:EG; [destruct k|].
  - destruct (index_of x H); [lia|]. rewrite g5_w_app, g5m_w_one. pose proof (g5m_gesture_begin l x EG). lia.
  - destruct (index_of x H) as [n|] eqn:EI; [|lia].
    destruct (index_of_some x H n EI) as (a & b & -> & <-).
    rewrite (g5_w_perm _ _ (swap_remove_perm [] a x b)).
    change (x :: swap_remove [] (length a) (a ++ x :: b)) with ([x] ++ swap_remove [] (length a) (a ++ x :: b)).
    rewrite g5_w_app, g5m_w_one. lia.
  - lia.
Qed.

Lemma g5m_lines_w : forall live mx ls no cap H ka j o ha ks,
  g5_w (snd (fst (snd (fst (lines_run live mx no cap H ka ls j o ha ks))))) <=
  g5_w H + Z.of_nat (length (with_nul ls)).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks.
  - cbn [lines_run snd fst]. rewrite with_nul_nil_len. lia.
  - cbn [lines_run]. cbv zeta. cbn [snd fst]. rewrite with_nul_cons_len.
    match goal with |- context [lines_run live mx ?n ?c (seen_arr H l) ?k ls ?j1 ?o1 ?h1 ?s1] =>
      pose proof (IH n c (seen_arr H l) k j1 o1 h1 s1) as IHr end.
    pose proof (g5m_seen_w H l). lia.
Qed.

Lemma g5m_drain_w : forall f live mx s j a,
  g5_w (ds_H (fst (snd (drain_run f live mx s j a)))) - ds_no (fst (snd (drain_run f live mx s j a))) <=
  g5_w (ds_H s) - ds_no s.
Proof.
  intros f live mx. induction f as [|f IH]; intros s j a.
  - cbn [drain_run snd fst]. lia.
  - cbn [drain_run]. cbv zeta. destruct (ds_eintr s).
    + cbn [snd fst].
      match goal with |- context [drain_run f live mx ?s1 ?j1 ?a1] => pose proof (IH s1 j1 a1) as I1 end.
      cbn [ds_H ds_no] in I1. lia.
    + destruct (ds_pend s) as [|r0 rs].
      { cbn [snd fst ds_H ds_no]. lia. }
      match goal with |- context [Z.min ?a ?b <=? 0] => destruct (Z.min a b <=? 0) end.
      { cbn [snd fst ds_H ds_no]. lia. }
      match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
      match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 ?o ?ha ?ks] =>
        pose proof (g5m_lines_w live mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 o ha ks) as LW;
        destruct (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 o ha ks)
          as [[tl [[oc' H'] ka']] [[o' ha'] ks']] end.
      cbn [snd fst] in LW |- *.
      match goal with |- context [drain_run f live mx ?s2 ?j4 ?a2] => pose proof (IH s2 j4 a2) as I1 end.
      cbn [ds_H ds_no] in I1. lia.
Qed.

Lemma g5m_w_keys : forall K, g5_w (keys_texts K) = keys_total K.
Proof. intros K. unfold g5_w. rewrite concat_end5_len, <- keys_total_texts. reflexivity. Qed.

Lemma g5m_fin_w : forall lv mx NO CAP e h,
  g5_w (ds_H (drain_fin lv mx NO CAP e h)) - ds_no (drain_fin lv mx NO CAP e h) <= keys_total (re_keys e) - NO.
Proof.
  intros lv mx NO CAP e h. unfold drain_fin, drain_go.
  pose proof (g5m_drain_w (S (S (length (pending_stream h)))) lv mx (drain_init NO CAP e h) 0 dadr0) as W.
  change (ds_H (drain_init NO CAP e h)) with (keys_texts (re_keys e)) in W.
  change (ds_no (drain_init NO CAP e h)) with NO in W.
  rewrite g5m_w_keys in W. exact W.
Qed.

Lemma g5m_seg_w : forall pre Ls ks K, g5_w ks <= keys_total K + Z.of_nat (length (with_nul Ls)) ->
  Z.of_nat (length (gone_segment pre Ls ks)) <= keys_total K + 2 * Z.of_nat (length (with_nul Ls)).
Proof.
  intros pre Ls ks K HW. unfold gone_segment. rewrite length_app, Nat2Z.inj_add.
  change (Z.of_nat (length (concat (map (fun x => x ++ END5Z) (fst (gei pre ks)))))) with (g5_w (fst (gei pre ks))).
  pose proof (gei_loop_ok (length ks) pre 0 ks ltac:(lia) ltac:(intros i Hi; exfalso; lia)) as G.
  unfold gei. destruct (gei_loop (length ks) pre 0 ks) as [E0 H0]. destruct G as (PE & _).
  cbn [fst]. pose proof (g5_w_perm _ _ PE) as W1. rewrite g5_w_app in W1. pose proof (g5_w_nonneg H0). lia.
Qed.

Lemma g5m_gs_after : forall lv mx pre (ps : list (rentry * (hsrc * nat))) no cap nm j o i d,
  (i < length ps)%nat ->
  exists no' cap', nth i (snd (fst (gone_run lv mx no cap pre ps nm j o))) d =
    after_drain lv mx no' cap' (fst (nth i ps (no_entry, no_hj))) (fst (snd (nth i ps (no_entry, no_hj)))).
Proof.
  intros lv mx pre ps. induction ps as [|[e hj] r IH]; intros no cap nm j o i d Hi; [cbn [length] in Hi; lia|].
  cbn [gone_run]. cbv zeta.
  match goal with |- context [gone_run lv mx ?n ?c pre r nm ?j1 ?o1] =>
    pose proof (IH n c nm j1 o1) as IHr; destruct (gone_run lv mx n c pre r nm j1 o1) as [[[t c'] ss] [o2 das]] end.
  cbn [fst snd] in IHr |- *. destruct i as [|i]; cbn [nth fst snd].
  - exists no, cap. reflexivity.
  - cbn [length] in Hi. exact (IHr i d ltac:(lia)).
Qed.

Section G5M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.

Lemma g5m_pair_seg : forall L A mem t pre (e : rentry) (hj : hsrc * nat) (ks : list (list Z)),
  entry_ok Bm L A mem e -> pair_ok Bm L A mem t e hj ->
  g5_w ks <= keys_total (re_keys e) + Z.of_nat (length (with_nul (entry_lines e hj))) ->
  Z.of_nat (length (gone_segment pre (entry_lines e hj) ks)) <= 2 * pair_cost e hj.
Proof.
  intros L A mem t pre e [h i] ks EOK HP HW.
  pose proof (g5m_seg_w pre (entry_lines e (h, i)) ks (re_keys e) HW) as S.
  unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP. destruct HP as (SRC & _ & _ & SKU & _).
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hov & _).
  destruct EOK as (_ & _ & _ & _ & _ & _ & HUl & _).
  pose proof (keys_total_nonneg (re_keys e)) as KN.
  assert (SU : 0 <= (if re_skip e =? 0 then re_used e else 0)) by (destruct (re_skip e =? 0); lia).
  unfold pair_cost. cbn [fst]. unfold entry_lines in S |- *. cbn [fst] in S |- *.
  destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
  - destruct (SKU E0) as [Hsk HU]. pose proof (reads_bound e h Hsk HU Hov HUl) as RB. lia.
  - rewrite with_nul_nil_len in S. lia.
Qed.

Lemma g5m_gone_cap : forall L A mem t lv mx CAP pre (es : list rentry) (hj : list (hsrc * nat)) k,
  Forall (entry_ok Bm L A mem) es -> Forall2 (pair_ok Bm L A mem t) es hj ->
  slot_cost es hj <= k -> k < INPUT_MAX -> 0 <= CAP <= TBBYTES ->
  gone_cap lv mx 0 CAP pre es hj <= NMAX.
Proof.
  intros L A mem t lv mx CAP pre es hj k HF PA Hc Hk HCAP.
  assert (Lh : length hj = length es) by (symmetry; exact (Forall2_length PA)).
  assert (HD : Forall (fun p => re_eof (fst p) = 0 -> forall no cap,
            ds_no (drain_fin lv mx no cap (fst p) (fst (snd p))) =
            no + Z.of_nat (length (with_nul (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))))))
         (combine es hj)).
  { apply Forall_forall. intros [e p] Hp. cbn [fst snd]. apply (g5_fin_no Bm L A mem t).
    - rewrite Forall_forall in HF. apply HF. exact (in_combine_l _ _ _ _ Hp).
    - exact (g5_forall2_in _ _ _ _ _ PA Hp). }
  assert (CB : gone_cap lv mx 0 CAP pre es hj <=
      Z.max CAP (2 * (0 + gone_tot pre (combine es hj) (map ds_H (gone_states lv mx 0 CAP pre es hj))))).
  { unfold gone_cap, gone_states. exact (gone_run_cap_le lv mx pre (combine es hj) 0 CAP (fun _ => adr0) 0%nat adr0 HD). }
  assert (LS : length (gone_states lv mx 0 CAP pre es hj) = length es).
  { unfold gone_states. rewrite gone_run_len, length_combine, Lh. apply Nat.min_id. }
  assert (T2 : gone_tot pre (combine es hj) (map ds_H (gone_states lv mx 0 CAP pre es hj)) <= 2 * slot_cost es hj).
  { unfold slot_cost. apply g5_tot_le. apply (g5_forall2_of_nth _ _ _ (no_entry, no_hj) []).
    - rewrite length_combine, length_map, LS, Lh. apply Nat.min_id.
    - intros i Hi. rewrite length_combine, Lh, Nat.min_id in Hi. rewrite combine_nth by (symmetry; exact Lh).
      cbn [fst snd].
      assert (EOK : entry_ok Bm L A mem (nth i es no_entry))
        by (rewrite Forall_forall in HF; apply HF; apply nth_In; exact Hi).
      pose proof (g5_forall2_nth _ _ _ no_entry no_hj PA i Hi) as PK.
      apply (g5m_pair_seg L A mem t pre _ _ _ EOK PK).
      rewrite (nth_indep _ [] (ds_H (drain_init 0 CAP (nth i es no_entry) (fst (nth i hj no_hj)))))
        by (rewrite length_map, LS; exact Hi).
      rewrite map_nth. unfold gone_states.
      destruct (g5m_gs_after lv mx pre (combine es hj) 0 CAP (fun _ => adr0) 0%nat adr0 i
        (drain_init 0 CAP (nth i es no_entry) (fst (nth i hj no_hj))) ltac:(rewrite length_combine; lia))
        as (no' & cap' & EQ).
      rewrite EQ, combine_nth by (symmetry; exact Lh). cbn [fst snd].
      unfold entry_lines. destruct (Z.eqb_spec (re_eof (nth i es no_entry)) 0) as [E0|E0].
      + rewrite (after_drain_fin lv mx no' cap' _ _ E0).
        pose proof (g5m_fin_w lv mx no' cap' (nth i es no_entry) (fst (nth i hj no_hj))) as W.
        pose proof (g5_fin_no Bm L A mem t lv mx (nth i es no_entry) (nth i hj no_hj) EOK PK E0 no' cap') as NO.
        lia.
      + rewrite (after_drain_init lv mx no' cap' _ _ E0).
        change (ds_H (drain_init no' cap' (nth i es no_entry) (fst (nth i hj no_hj))))
          with (keys_texts (re_keys (nth i es no_entry))).
        rewrite g5m_w_keys, with_nul_nil_len. lia. }
  pose proof (gone_tot_nonneg pre (combine es hj) (map ds_H (gone_states lv mx 0 CAP pre es hj))).
  unfold INPUT_MAX, TBBYTES, NMAX in *. lia.
Qed.

Lemma g5m_d3_facts : forall L A mem t G OUT (es : list rentry) (hj : list (hsrc * nat)) k,
  Forall (entry_ok Bm L A mem) es -> Forall2 (pair_ok Bm L A mem t) es hj ->
  slot_cost es hj <= k -> k < INPUT_MAX -> 0 <= t < OPS_MAX ->
  Forall (fun p => gone_src_ok Bm L A mem G OUT es (fst p) (snd p)) (combine es hj) ->
  Forall (fun p => re_eof (fst p) = 0 ->
            0 <= re_cap (fst p) /\ 0 <= ent_ka (fst p) /\
            J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p))) /\
            0 <= hs_off (fst (snd p)) /\
            re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26 /\
            (hl_cap (hs_expected (fst (snd p))) = 0 \/
             exists k, 0 <= k /\ hl_cap (hs_expected (fst (snd p))) = 8 * 2 ^ k) /\
            hl_n (hs_expected (fst (snd p))) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 25 /\
            Z.of_nat (length (re_U (fst p))) <= re_used (fst p)) (combine es hj).
Proof.
  intros L A mem t G OUT es hj k HF PA Hc Hk Ht GS. apply Forall_forall. intros [e [h jj]] Hp E0. cbn [fst snd] in *.
  pose proof (g5_forall2_in _ _ _ _ _ PA Hp) as HP. unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP.
  destruct HP as (SRC & HJ & FD & SKU & SS & NDH & HE0 & PN & PC & PS & EC & HC).
  assert (EOK : entry_ok Bm L A mem e) by (rewrite Forall_forall in HF; exact (HF e (in_combine_l _ _ _ _ Hp))).
  rewrite Forall_forall in GS. pose proof (GS (e, (h, jj)) Hp) as GO. unfold gone_src_ok in GO. cbv zeta in GO.
  cbn [fst snd] in GO. destruct (GO E0) as (_ & _ & _ & _ & _ & _ & _ & NH).
  destruct EOK as (_ & SK & _ & _ & _ & CAPC & UL & UB & UNZ & _ & _ & HHP & _).
  destruct (SKU E0) as [Hsk HU].
  pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & OFF & _).
  split; [destruct CAPC as [X|[X|X]]; rewrite X; lia|].
  split.
  { unfold ent_ka. destruct (Z.eqb_spec (re_hp e) 0); [lia|].
    destruct HHP as [(H0 & _)|(_ & _ & _ & K8 & _)]; [contradiction|lia]. }
  split.
  { unfold J1, hs_state. cbn [ls_k ls_w]. rewrite Hsk. split; [reflexivity|]. split.
    - intros F0. apply HU. destruct SK as [S|S]; [exact S|]. rewrite <- Hsk, S in F0. discriminate.
    - split; [|apply g5_nozero; exact UNZ].
      unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000. lia. }
  split; [destruct OFF as [(_ & ->)|(r & rs & _ & O1 & _)]; lia|].
  split; [exact NH|].
  split.
  { destruct EC as [E1|(k0 & Hk0 & E1)]; [left; exact E1|right; exists k0; split; [lia|exact E1]]. }
  split.
  { unfold hl_n. rewrite HE0. cbn [length Z.of_nat]. unfold WRITE_MAX, OPS_MAX in *. lia. }
  lia.
Qed.

Lemma g5m_hp_kh : forall L A mem (es : list rentry) (hj : list (hsrc * nat)),
  Forall (entry_ok Bm L A mem) es ->
  Forall (fun p => re_eof (fst p) = 0 -> re_hp (fst p) <> 0 -> re_kh (fst p) <> 0) (combine es hj).
Proof.
  intros L A mem es hj HF. apply Forall_forall. intros [e p] Hp _ Hh. cbn [fst] in *.
  rewrite Forall_forall in HF. pose proof (HF e (in_combine_l _ _ _ _ Hp)) as EOK.
  destruct EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHP & _).
  destruct HHP as [(H0 & _)|(_ & _ & _ & K8 & _)]; [contradiction|lia].
Qed.

Lemma g5m_tot0_drain : forall L A mem t (es : list rentry) (hj : list (hsrc * nat)),
  Forall (entry_ok Bm L A mem) es -> Forall2 (pair_ok Bm L A mem t) es hj ->
  Forall (fun p => re_eof (fst p) = 0 ->
            lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p)))) = [] ->
            forall (lv' : bool) (mx' NO' CAP' : Z) (j' : nat) (a : dadr),
              drain_go lv' mx' NO' CAP' (fst p) (fst (snd p)) j' a = drain_go false mx' NO' CAP' (fst p) (fst (snd p)) j' a)
    (combine es hj).
Proof.
  intros L A mem t es hj HF PA. apply Forall_forall. intros [e [h jj]] Hp E0 HL lv' mx' NO' CAP' j' a.
  cbn [fst snd] in *.
  pose proof (g5_forall2_in _ _ _ _ _ PA Hp) as HP. unfold pair_ok in HP. cbv zeta in HP. cbn [fst snd] in HP.
  destruct HP as (SRC & _ & _ & SKU & _).
  assert (EOK : entry_ok Bm L A mem e) by (rewrite Forall_forall in HF; exact (HF e (in_combine_l _ _ _ _ Hp))).
  destruct EOK as (_ & SK & _ & _ & _ & CAPC & UL & UB & UNZ & _).
  destruct (SKU E0) as [Hsk HU].
  pose proof SRC as (_ & _ & _ & _ & _ & LP & _ & OFF & _).
  pose proof LP as (_ & _ & _ & _ & _ & PFA).
  destruct (rig_dinit NO' CAP' e h SK Hsk HU ltac:(lia) UNZ ltac:(destruct CAPC as [X|[X|X]]; rewrite X; lia) OFF
    ltac:(eapply Forall_impl; [|exact PFA]; intros r (_ & _ & _ & _ & X); exact (X eq_refl))) as [I1 I2].
  exact (proj2 (rig_drain_model false mx' NO' CAP' e h I1 I2) HL lv' j' a).
Qed.

End G5M.
