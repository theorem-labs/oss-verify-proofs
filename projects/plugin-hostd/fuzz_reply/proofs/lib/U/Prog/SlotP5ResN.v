(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names, addresses and numbers changed; 655 of its 764 lines of code are new or changed and 1120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_instance_gone_b_seg.v, with its module paths and module names changed; 188 of its 239 lines of code are new or changed and 713 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/SlotPass5A.v, with its module paths and module names changed; 957 of its 1013 lines of code are new or changed and 183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5Check.v; 192 of its 256 lines of code are new or changed and 949 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5M.v, with its module paths changed; 854 of its 894 lines of code are new or changed and 216 lines of the source are left out. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import StatementKept SlotInv SlotSteps SlotRes
  SlotParse SlotCaps3 SlotRI3 RelayRunT RelayRunF RelayModel RelayKeys RelayRep HarnessRep ListRep CheckRep ListTr
  HarnessTr send_line_b_c gesture_end_b_c gestures_end_b_c drain_b_c relay_remove_b_c relay_instance_gone_b_c
  SlotRun3 SlotP5R3 SlotP5R3G SlotDrain3Aux SlotDrain3 SlotDrainWt3 SlotP5Res3 SlotRI3P SlotPeak3
  SlotP4Res3Aux SlotP4Res3P SlotNcWt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotPass4 relay_add_b_c.
From Stdlib Require Import ZArith List Bool Lia Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition p5c_res3_fullN (OK : astate -> Prop) (RM : pbound3 -> Z -> Prop) : Prop :=
  forall (E : sstart) (K K' : Z) (L : layout) (A : astate) (G OUT : Z) (es : list rentry) (hs : list (hsrc * nat))
         (lv : bool) (mx NO CAP : Z) (pre : list Z),
    let nm := known_at L A in
    let V := view_of G OUT es hs in
    let tr := relay_instance_gone_tr lv mx NO CAP pre es hs nm 0 (nm OUT) in
    RI3P OK E K V L A -> K <= K' ->
    length hs = length es -> (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
    Forall (fun p => re_eof (fst p) = 0 ->
              0 <= re_cap (fst p) /\ 0 <= ent_ka (fst p) /\
              J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p))) /\
              0 <= hs_off (fst (snd p)) /\
              re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26 /\
              (hl_cap (hs_expected (fst (snd p))) = 0 \/
               exists k, 0 <= k /\ hl_cap (hs_expected (fst (snd p))) = 8 * 2 ^ k) /\
              hl_n (hs_expected (fst (snd p))) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 25 /\
              Z.of_nat (length (re_U (fst p))) <= re_used (fst p)) (combine es hs) ->
    gone_cap lv mx NO CAP pre es hs <= NMAX ->
    Forall (fun p => re_eof (fst p) = 0 -> re_hp (fst p) <> 0 -> re_kh (fst p) <> 0) (combine es hs) ->
    List.NoDup (map fst (blocks L A)) ->
    (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
    0 <= NO <= CAP ->
    In (G, relay_add_b_c.SRC_TABLE) (blocks L A) ->
    (CAP = 0 \/ In (OUT, CAP) (blocks L A)) ->
    Forall (SlotPass4.p4_ent_blk L A) es ->
    Forall (fun p => SlotPass4.p4_src_blk L A (fst p)) hs ->
    exists bnd, rt_ok (pack3P OK RM) A bnd /\
      (forall qs, length qs = nretF tr -> roomF (pack3P OK RM) qs bnd tr) /\
      forall L' A' qs, length qs = nretF tr -> rt_ok (pack3P OK RM) A' (runF (pack3P OK RM) qs bnd tr) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c + gone_dl lv mx NO CAP pre es hs nm 0 (nm OUT) c <= nc_cnt V' L' A' c) ->
        ncs V L A + gone_db lv mx NO CAP pre es hs nm 0 (nm OUT) <= ncs V' L' A' ->
        ncs V' L' A' <= rv_wt V' ->
        rv_wt V' <= rv_wt V + gone_wd (combine es hs) (gone_states lv mx NO CAP pre es hs) +
                    DATA_PER * (cdat (ss_pl E) K' - cdat (ss_pl E) K) ->
        rv_pend V' = gone_pend es hs ->
        (forall c, 0 <= c < 49 -> ek_c V' c = ek_c V c + bcnt c (gone_ek (combine es hs))) ->
        ek_b V' = ek_b V + zsum (fun n => n) (gone_ek (combine es hs)) ->
        Forall (fun n => 0 <= n) (rv_ek V') ->
        List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> In (ptr_addr L p) (rv_nc V) ->
           ~ In (ptr_addr L p) (gone_tch OUT CAP es hs) -> In (ptr_addr L' p) (rv_nc V')) ->
        (gone_cap lv mx NO CAP pre es hs <> 0 ->
           In (ptr_addr L' (resolveF qs (gone_out lv mx NO CAP pre es hs nm 0 (nm OUT)))) (rv_nc V')) ->
        (forall i, (i < length es)%nat -> re_eof (nth i es no_entry) = 0 ->
           let s := nth i (gone_states lv mx NO CAP pre es hs)
                      (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))) in
           let a := nth i (gone_adrs lv mx NO CAP pre es hs nm 0 (nm OUT)) dadr0 in
           (ds_cap s <> 0 -> In (ptr_addr L' (resolveF qs (da_buf a))) (rv_nc V')) /\
           (ds_ka s <> 0 -> In (ptr_addr L' (resolveF qs (da_hp a))) (rv_nc V')) /\
           (ds_ecap s <> 0 -> In (ptr_addr L' (resolveF qs (da_ev a))) (rv_nc V'))) ->
        RI3P OK E K' V' L' A'.

Lemma ncN_ent L A e : List.NoDup (map fst (blocks L A)) -> SlotPass4.p4_ent_blk L A e ->
  zsum (nc_sz L A) (entry_nc e) <= re_cap e + ent_ka e.
Proof.
  intros HN (HB & HP & _). unfold entry_nc, ent_ka. rewrite zsum_app.
  assert (X1 : zsum (nc_sz L A) (if re_cap e =? 0 then [] else [re_buf e]) <= re_cap e).
  { destruct (Z.eqb_spec (re_cap e) 0) as [E0|E0]; [rewrite zsum_nil; lia|].
    destruct HB as [X|X]; [lia|]. rewrite zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN X). lia. }
  assert (X2 : zsum (nc_sz L A) (if re_hp e =? 0 then [] else [re_hp e]) <=
               (if re_hp e =? 0 then 0 else re_kh e)).
  { destruct (Z.eqb_spec (re_hp e) 0) as [E0|E0]; [rewrite zsum_nil; lia|].
    destruct HP as [X|X]; [lia|]. rewrite zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN X). lia. }
  lia.
Qed.

Lemma ncN_arr L A l : List.NoDup (map fst (blocks L A)) -> SlotPass4.p4_list_blk L A l ->
  zsum (nc_sz L A) (arr_nc l) <= 16 * hl_cap l.
Proof.
  intros HN (HC & _). unfold arr_nc.
  destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; [rewrite zsum_nil; lia|].
  destruct HC as [X|X]; [lia|]. rewrite zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN X). lia.
Qed.

Lemma ncN_src L A h : List.NoDup (map fst (blocks L A)) -> SlotPass4.p4_src_blk L A h ->
  zsum (nc_sz L A) (src_nc h) <=
    16 * hl_cap (hs_pending h) + 6000 + 16 * hl_cap (hs_expected h) + 16 * hl_cap (hs_held h).
Proof.
  intros HN (HP & HPa & HE & HH & _). unfold src_nc.
  rewrite !zsum_app, zsum_cons, zsum_nil, (nw_sz_at L A _ _ HN HPa).
  pose proof (ncN_arr L A (hs_pending h) HN HP). pose proof (ncN_arr L A (hs_expected h) HN HE).
  pose proof (ncN_arr L A (hs_held h) HN HH). lia.
Qed.

Lemma ncsN L A G OUT CAP es hs : List.NoDup (map fst (blocks L A)) ->
  In (G, relay_add_b_c.SRC_TABLE) (blocks L A) ->
  (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) -> (CAP = 0 \/ In (OUT, CAP) (blocks L A)) ->
  Forall (SlotPass4.p4_ent_blk L A) es -> Forall (fun p => SlotPass4.p4_src_blk L A (fst p)) hs ->
  ncs (view_of G OUT es hs) L A <= relay_add_b_c.SRC_TABLE + CAP +
    zsum (fun e => re_cap e + ent_ka e) es +
    zsum (fun p => 16 * hl_cap (hs_pending (fst p)) + 6000 + 16 * hl_cap (hs_expected (fst p)) +
                   16 * hl_cap (hs_held (fst p))) hs.
Proof.
  intros HN HG HO0 HO HE HS. unfold ncs, view_of. cbn [rv_nc].
  rewrite !zsum_cons, zsum_app, (nw_sz_at L A _ _ HN HG).
  assert (XO : nc_sz L A OUT <= CAP).
  { destruct HO as [E0|X]; [rewrite (nw_sz_none L A OUT (HO0 E0)); lia|].
    rewrite (nw_sz_at L A _ _ HN X). lia. }
  rewrite !nw_zsum_concat.
  pose proof (nw_zsum_le (fun e => zsum (nc_sz L A) (entry_nc e)) (fun e => re_cap e + ent_ka e) es
    (fun e He => ncN_ent L A e HN (proj1 (Forall_forall _ _) HE e He))) as X1.
  pose proof (nw_zsum_le (fun p => zsum (nc_sz L A) (src_nc (fst p)))
    (fun p => 16 * hl_cap (hs_pending (fst p)) + 6000 + 16 * hl_cap (hs_expected (fst p)) +
              16 * hl_cap (hs_held (fst p))) hs
    (fun p Hp => ncN_src L A (fst p) HN (proj1 (Forall_forall _ _) HS p Hp))) as X2.
  lia.
Qed.

Lemma seen_stepsN mxs x0 x1 x3 H ka l j ha ks : 0 <= ka -> zlen l <= 6000 ->
  (Z.of_nat (length H) + 1) * 8 <= NMAX -> (Z.of_nat (length H) + 1) * 8 <= nth 2 mxs 0 ->
  exists u, steps mxs j [x0; x1; (ka, ha); x3] (fst (fst (seen_tr H ka l j ha ks)))
      [x0; x1; (snd (fst (seen_tr H ka l j ha ks)), fst (snd (seen_tr H ka l j ha ks))); x3] u /\
    (forall c, bcnt c u <= bcnt c (ek1 l)) /\ zsum (fun n => n) u <= zsum (fun n => n) (ek1 l) /\
    0 <= snd (fst (seen_tr H ka l j ha ks)) /\ (length (seen_arr H l) <= length H + 1)%nat.
Proof.
  intros Hk Hl HH HM. pose proof NMAX_v as EN. unfold seen_tr, seen_arr, ek1.
  destruct (gesture l) as [[[|] x]|] eqn:Eg.
  - destruct (index_of x H) as [i|] eqn:Ei; cbn [fst snd]; cbv zeta.
    + exists []. split; [apply sp_nil|]. split; [intros c; change (bcnt c []) with 0; apply bcnt_nonneg|].
      split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|lia].
    + destruct (gesture_begin l x Eg) as [Ex _]. exists [Z.of_nat (length x) + 1]. split.
      * apply sp_grow2; [lia|lia|]. apply sp_copy; [lia|]. apply sp_nil.
      * split; [intros c; lia|]. split; [lia|]. split; [lia|]. rewrite length_app. cbn [length]. lia.
  - destruct (index_of x H) as [i|] eqn:Ei; cbn [fst snd].
    + exists []. split; [apply sp_free; [lia|apply sp_nil]|]. split; [intros c; unfold bcnt, zsum; cbn [fold_right]; lia|].
      split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|]. unfold swap_remove.
      pose proof (firstn_len_le (length H - 1) (set_nth i (last H []) H)). lia.
    + exists []. split; [apply sp_nil|]. split; [intros c; unfold bcnt, zsum; cbn [fold_right]; lia|].
      split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|lia].
  - exists []. cbn [fst snd]. split; [apply sp_nil|]. split; [intros c; unfold bcnt, zsum; cbn [fold_right]; lia|].
    split; [unfold zsum; cbn [fold_right]; lia|]. split; [exact Hk|lia].
Qed.

Lemma lines_stepsN lv mx mxs x1 x3 : forall ls no cap H ka j o ha ks,
  0 <= cap -> 0 <= ka -> (zlen H + zlen ls + 1) * 8 <= nth 2 mxs 0 -> (zlen H + zlen ls + 1) * 8 <= NMAX ->
  Forall (fun l => zlen l <= 6000) ls -> nth 0 mxs 0 <= NMAX ->
  fst (fst (snd (fst (lines_run lv mx no cap H ka ls j o ha ks)))) <= nth 0 mxs 0 ->
  exists u, steps mxs j [(cap, o); x1; (ka, ha); x3] (fst (fst (lines_run lv mx no cap H ka ls j o ha ks)))
      [(fst (fst (snd (fst (lines_run lv mx no cap H ka ls j o ha ks)))),
        fst (fst (snd (lines_run lv mx no cap H ka ls j o ha ks)))); x1;
       (snd (snd (fst (lines_run lv mx no cap H ka ls j o ha ks))),
        snd (fst (snd (lines_run lv mx no cap H ka ls j o ha ks)))); x3] u /\
    (forall c, bcnt c u <= bcnt c (ekl ls)) /\ zsum (fun n => n) u <= zsum (fun n => n) (ekl ls) /\
    0 <= snd (snd (fst (lines_run lv mx no cap H ka ls j o ha ks))) /\
    zlen (snd (fst (snd (fst (lines_run lv mx no cap H ka ls j o ha ks))))) <= zlen H + zlen ls.
Proof.
  induction ls as [|l r IH]; intros no cap H ka j o ha ks Hc Hk HK MK HF MN HO.
  - exists []. cbn [lines_run fst snd]. split; [apply sp_nil|].
    split; [intros c; unfold bcnt, ekl, zsum; cbn [map concat fold_right]; lia|].
    split; [unfold ekl, zsum; cbn [map concat fold_right]; lia|]. split; [exact Hk|]. unfold zlen. cbn [length]. lia.
  - apply Forall_cons_iff in HF as [Hl HF]. revert HO. cbn [lines_run fst snd]. cbv zeta. intros HO.
    set (len := Z.of_nat (length l) + 1) in *.
    set (t1 := send_line_tr lv mx no cap len j o) in *.
    set (sn := seen_tr H ka l (j + nretF t1) ha ks) in *.
    set (p := lines_run lv mx (no + len) (send_line_cap lv mx no cap len) (seen_arr H l) (snd (fst sn)) r
                (j + nretF t1 + nretF (fst (fst sn))) (send_line_out lv mx no cap len j o) (fst (snd sn))
                (snd (snd sn))) in *.
    pose proof (send_mono lv mx no cap len Hc) as MS.
    assert (MO : send_line_cap lv mx no cap len <= fst (fst (snd (fst p)))) by (unfold p; apply lines_mono; lia).
    pose proof (send_steps mxs [x1; (ka, ha); x3] lv mx no cap len j o Hc ltac:(lia) MN) as S1.
    assert (HHs1 : (Z.of_nat (length H) + 1) * 8 <= NMAX)
      by (unfold zlen in *; cbn [length] in MK; lia).
    assert (HHs2 : (Z.of_nat (length H) + 1) * 8 <= nth 2 mxs 0)
      by (unfold zlen in *; cbn [length] in HK; lia).
    destruct (seen_stepsN mxs (send_line_cap lv mx no cap len, send_line_out lv mx no cap len j o) x1 x3 H ka l
      (j + nretF t1) ha ks Hk Hl HHs1 HHs2) as (u1 & S2 & B1 & Z1 & K1 & L1).
    fold sn in S2, B1, Z1, K1.
    assert (HK' : (zlen (seen_arr H l) + zlen r + 1) * 8 <= nth 2 mxs 0)
      by (unfold zlen in *; cbn [length] in HK |- *; lia).
    assert (MK' : (zlen (seen_arr H l) + zlen r + 1) * 8 <= NMAX)
      by (unfold zlen in *; cbn [length] in MK |- *; lia).
    destruct (IH (no + len) (send_line_cap lv mx no cap len) (seen_arr H l) (snd (fst sn))
      (j + nretF t1 + nretF (fst (fst sn)))%nat (send_line_out lv mx no cap len j o) (fst (snd sn)) (snd (snd sn))
      ltac:(lia) K1 HK' MK' HF MN HO) as (u2 & S3 & B2 & Z2 & K2 & L2).
    exists (u1 ++ u2). split.
    + change (u1 ++ u2) with ([] ++ u1 ++ u2). eapply steps_app; [exact S1|]. eapply steps_app; [exact S2|]. exact S3.
    + change (ekl (l :: r)) with (ek1 l ++ ekl r).
      split; [intros c; rewrite !bcnt_app; specialize (B1 c); specialize (B2 c); lia|].
      split; [rewrite !zsum_app; lia|]. split; [exact K2|]. fold p in L2. unfold zlen in *. cbn [length]. lia.
Qed.

Lemma push_tra_stepsN mxs x0 x1 x2 v n cap len j : d3pow cap -> n < 2 ^ 25 -> 0 <= len <= 6000 ->
  16 * push_cap n cap <= nth 3 mxs 0 ->
  steps mxs j [x0; x1; x2; (16 * cap, v)] (list_push_tra v n cap len)
    [x0; x1; x2; (16 * push_cap n cap, if n =? cap then Ret j else v)] [len + 1].
Proof.
  intros Hp Hn Hl HM. pose proof P29 as E29. pose proof NMAX_v as EN.
  unfold list_push_tra. unfold push_cap in HM |- *.
  destruct (Z.eqb_spec n cap) as [Ec|Ec].
  - destruct (Z.eqb_spec cap 0) as [Ez|Ez].
    + subst n. subst cap. cbn [app].
      refine (sp_grow3 mxs j x0 x1 x2 [] (16 * 0) v 128 [RMalloc (len + 1)] _ [len + 1] _ _ _); [lia|lia|].
      change (16 * 8) with 128. apply sp_copy; [lia|apply sp_nil].
    + subst n. destruct Hp as [Hp|(k & Hk & Ek)]; [contradiction|].
      pose proof (Z.pow_nonneg 2 k ltac:(lia)) as P0.
      destruct (pow8_grow k Hk ltac:(lia)) as [G _]. cbn [app].
      replace (RRealloc (16 * cap) (32 * cap) v) with
        (if 16 * cap =? 0 then RMalloc (32 * cap) else RRealloc (16 * cap) (32 * cap) v)
        by (rewrite (proj2 (Z.eqb_neq (16 * cap) 0)) by lia; reflexivity).
      replace (16 * (cap * 2)) with (32 * cap) in HM |- * by lia.
      apply sp_grow3; [lia|lia|]. apply sp_copy; [lia|apply sp_nil].
  - cbn [app]. apply sp_copy; [lia|apply sp_nil].
Qed.

Lemma pcap_geN ls : forall n cap, 0 <= cap -> cap <= pcap n cap ls.
Proof.
  induction ls as [|l r IH]; intros n cap Hc.
  - unfold pcap. cbn [pushes_run fst snd]. lia.
  - unfold pcap. cbn [pushes_run fst snd]. cbv zeta. rewrite pushes_cap_c.
    assert (P : cap <= push_cap n cap)
      by (unfold push_cap; destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0); lia|lia]).
    pose proof (IH (n + 1) (push_cap n cap) ltac:(lia)). lia.
Qed.

Lemma pushes_stepsN mxs x0 x1 x2 ls : forall n cap j v rs,
  d3pow cap -> n + zlen ls < 2 ^ 25 -> Forall (fun l => zlen l <= 6000) ls ->
  16 * pcap n cap ls <= nth 3 mxs 0 ->
  steps mxs j [x0; x1; x2; (16 * cap, v)] (fst (fst (pushes_run n cap ls j v rs)))
    [x0; x1; x2; (16 * snd (fst (pushes_run n cap ls j v rs)), fst (snd (pushes_run n cap ls j v rs)))] (rcl ls) /\
  d3pow (snd (fst (pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l r IH]; intros n cap j v rs Hp Hn HF HM.
  - cbn [pushes_run fst snd]. split; [apply sp_nil|exact Hp].
  - apply Forall_cons_iff in HF as [Hl HF]. cbn [pushes_run fst snd]. cbv zeta.
    assert (Hr : n + 1 + zlen r < 2 ^ 25) by (unfold zlen in *; cbn [length] in Hn; lia).
    assert (Hc0 : 0 <= cap) by (destruct Hp as [->|(k & Hk & ->)]; [lia|pose proof (Z.pow_nonneg 2 k ltac:(lia)); lia]).
    assert (Ec : pcap n cap (l :: r) = pcap (n + 1) (push_cap n cap) r).
    { unfold pcap. cbn [pushes_run fst snd]. cbv zeta. rewrite pushes_cap_c. reflexivity. }
    assert (Hpc0 : 0 <= push_cap n cap)
      by (unfold push_cap; destruct (Z.eqb_spec n cap); [destruct (Z.eqb_spec cap 0); lia|lia]).
    pose proof (pcap_geN r (n + 1) (push_cap n cap) Hpc0) as G1.
    assert (HM1 : 16 * push_cap n cap <= nth 3 mxs 0) by (rewrite Ec in HM; lia).
    assert (Hn1 : n < 2 ^ 25) by (unfold zlen in *; cbn [length] in Hn; lia).
    pose proof (push_tra_stepsN mxs x0 x1 x2 v n cap (Z.of_nat (length l)) j Hp Hn1
      ltac:(unfold zlen in Hl; lia) HM1) as T.
    assert (Hp' : d3pow (push_cap n cap))
      by (apply (push_cap_pow n cap (zlen (l :: r))); [exact Hp|exact Hn|unfold zlen; cbn [length]; lia]).
    assert (HM' : 16 * pcap (n + 1) (push_cap n cap) r <= nth 3 mxs 0) by (rewrite Ec in HM; exact HM).
    destruct (IH (n + 1) (push_cap n cap) (j + nretF (list_push_tra v n cap (Z.of_nat (length l))))%nat
      (if n =? cap then Ret j else v)
      (rs ++ [Ret (Nat.pred (j + nretF (list_push_tra v n cap (Z.of_nat (length l)))))]) Hp' Hr HF HM') as [S2 P2].
    split; [|exact P2].
    change (rcl (l :: r)) with ([Z.of_nat (length l) + 1] ++ rcl r).
    eapply steps_app; [exact T|exact S2].
Qed.

Lemma drain_ecap_monoN lv mx : forall f s j a, 0 <= ds_ecap s ->
  ds_ecap s <= ds_ecap (fst (snd (drain_run f lv mx s j a))).
Proof.
  induction f as [|f IH]; intros s j a He; [cbn; lia|]. cbn [drain_run]. cbv zeta.
  destruct (ds_eintr s).
  - cbn [fst snd].
    match goal with |- _ <= ds_ecap (fst (snd (drain_run f lv mx ?s1 ?j1 ?a1))) => exact (IH s1 j1 a1 He) end.
  - destruct (ds_pend s) as [|r0 rs]; [cbn [fst snd ds_ecap]; lia|].
    match goal with |- context [if Z.min ?x ?y <=? 0 then _ else _] => destruct (Z.min x y <=? 0) end;
      [cbn [fst snd ds_ecap]; lia|].
    match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end. cbv beta iota.
    match goal with |- context [snd (fst (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11))] =>
      destruct (snd (fst (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11))) as [[oc' H'] ka'] end.
    cbv beta iota.
    match goal with |- context [snd (lines_run ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11)] =>
      destruct (snd (lines_run a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)) as [[o' ha'] ks'] end.
    cbv beta iota. cbn [fst snd].
    match goal with |- _ <= ds_ecap (fst (snd (drain_run f lv mx ?s2 ?j2 ?a2))) =>
      assert (E2 : ds_ecap s <= ds_ecap s2) end.
    { cbn [ds_ecap]. rewrite pushes_cap_c. apply pcap_geN. exact He. }
    match goal with |- _ <= ds_ecap (fst (snd (drain_run f lv mx ?s2 ?j2 ?a2))) =>
      exact (Z.le_trans _ _ _ E2 (IH s2 j2 a2 ltac:(lia))) end.
Qed.

Lemma drain_stepsN lv mx mxs : forall f s j a,
  d3I s -> 32768 <= nth 1 mxs 0 ->
  (zlen (ds_H s) + zlen (d3str s) + 1) * 8 <= nth 2 mxs 0 ->
  (zlen (ds_H s) + zlen (d3str s) + 1) * 8 <= NMAX -> nth 0 mxs 0 <= NMAX ->
  16 * ds_ecap (fst (snd (drain_run f lv mx s j a))) <= nth 3 mxs 0 ->
  ds_ocap (fst (snd (drain_run f lv mx s j a))) <= nth 0 mxs 0 ->
  exists u cs, steps mxs j (d3sig s a) (fst (drain_run f lv mx s j a))
      (d3sig (fst (snd (drain_run f lv mx s j a))) (snd (snd (drain_run f lv mx s j a)))) u /\
    d3str s = cs ++ d3str (fst (snd (drain_run f lv mx s j a))) /\ chg u (lines (ds_ref s) cs).
Proof.
  induction f as [|f IH]; intros s j a HD M1 MK MKN MN.
  - intros _ _. exists [], []. cbn [drain_run fst snd]. split; [apply sp_nil|]. split; [reflexivity|].
    rewrite lines_nil. exact chg_nil.
  - pose proof HD as (HJ & Hc & Hka & Hoc & Hoff & Hp & Hen & HH).
    assert (Hu : 0 <= Z.of_nat (length (ds_u s)) <= 6000)
      by (destruct HJ as (_ & _ & L & _); pose proof (LL_le _ L); lia).
    destruct (grow_steps mxs (ds_ocap s, da_out a) (ds_ka s, da_hp a) (16 * ds_ecap s, da_ev a) (ds_cap s)
      (Z.of_nat (length (ds_u s))) j (da_buf a) Hc Hu M1) as [G1 G2].
    cbn [drain_run]. cbv zeta.
    set (g := grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)) in *.
    destruct (ds_eintr s) eqn:Ee.
    + cbn [fst snd]. intros ME HF.
      match type of HF with ds_ocap (fst (snd (drain_run f lv mx ?s1 ?j1 ?a1))) <= _ =>
        assert (HD1 : d3I s1) by (unfold d3I, d3str in *; cbn [ds_u ds_skip ds_ref ds_cap ds_ka ds_ocap ds_off ds_ecap
          ds_en ds_H ds_pend]; tauto);
        assert (MK1 : (zlen (ds_H s1) + zlen (d3str s1) + 1) * 8 <= nth 2 mxs 0)
          by (unfold d3str in *; cbn [ds_H ds_pend ds_off]; exact MK);
        assert (MKN1 : (zlen (ds_H s1) + zlen (d3str s1) + 1) * 8 <= NMAX)
          by (unfold d3str in *; cbn [ds_H ds_pend ds_off]; exact MKN);
        destruct (IH s1 j1 a1 HD1 M1 MK1 MKN1 MN ME HF) as (u & cs & S1 & S2 & S3) end.
      exists u, cs. split; [|split; [exact S2|exact S3]].
      change u with ([] ++ u). eapply steps_app; [exact G1|exact S1].
    + destruct (ds_pend s) as [|r0 rs] eqn:Ep.
      * cbn [fst snd]. intros ME HF. exists [], []. split; [exact G1|].
        split; [unfold d3str; rewrite Ep; reflexivity|]. rewrite lines_nil. exact chg_nil.
      * set (n := Z.min (Z.of_nat (length r0) - ds_off s) (fst (snd g) - Z.of_nat (length (ds_u s)))) in *.
        destruct (Z.leb_spec n 0) as [En|En].
        -- cbn [fst snd]. intros ME HF. exists [], []. split; [exact G1|].
           split; [unfold d3str; rewrite Ep; reflexivity|]. rewrite lines_nil. exact chg_nil.
        -- assert (Hn1 : n <= Z.of_nat (length r0) - ds_off s) by apply Z.le_min_l.
           set (d := firstn (Z.to_nat n) (skipn (Z.to_nat (ds_off s)) r0)) in *.
           destruct (chunk (ds_u s) (ds_skip s) d) as [[u' sk'] rl] eqn:Ech. cbv beta iota.
           pose proof (chunk_ok (ds_u s) (ds_skip s) (ds_ref s) d HJ) as CK. rewrite Ech in CK. cbv beta iota in CK.
           destruct CK as [Erl HJ2]. subst rl.
           set (ls := lines (ds_ref s) d) in *.
           set (pu := pushes_run (ds_en s) (ds_ecap s) ls (j + nretF (fst g)) (da_ev a) (da_erecs a)) in *.
           match goal with |- context [lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls ?j3 (da_out a) (da_hp a) (da_keys a)] =>
             set (j3' := j3) in * end.
           set (sl := lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a)) in *.
           destruct (snd (fst sl)) as [[oc' H'] ka'] eqn:E1. cbv beta iota.
           destruct (snd sl) as [[o' ha'] ks'] eqn:E2. cbv beta iota.
           cbn [fst snd]. intros ME HF.
           match type of HF with ds_ocap (fst (snd (drain_run f lv mx ?s2 ?j4 ?a2))) <= _ =>
             set (s2' := s2) in *; set (a2' := a2) in *; set (j4' := j4) in * end.
           assert (SE : d3str s = d ++ d3str s2')
             by (unfold d; apply (round_str s s2' r0 rs n Ep Hoff En Hn1); reflexivity).
           assert (Ld : zlen (d3str s) = zlen d + zlen (d3str s2'))
             by (rewrite SE; unfold zlen; rewrite length_app; lia).
           pose proof (lines_count d (ds_ref s)) as LC. fold ls in LC.
           assert (LF : Forall (fun l => zlen l <= 6000) ls) by exact (lines_J1 _ _ _ d HJ).
           assert (HE0 : 0 <= ds_ecap s)
             by (destruct Hp as [E0|(k0 & Hk0 & E0)]; rewrite E0;
                 [lia|pose proof (Z.pow_nonneg 2 k0 ltac:(lia)); lia]).
           assert (EC2 : ds_ecap s2' = pcap (ds_en s) (ds_ecap s) ls)
             by (unfold s2'; cbn [ds_ecap]; unfold pu; apply pushes_cap_c).
           assert (HE2 : 0 <= ds_ecap s2')
             by (rewrite EC2; pose proof (pcap_geN ls (ds_en s) (ds_ecap s) HE0); lia).
           assert (HPC : 16 * pcap (ds_en s) (ds_ecap s) ls <= nth 3 mxs 0).
           { rewrite <- EC2. pose proof (drain_ecap_monoN lv mx f s2' j4' a2' HE2). lia. }
           destruct (pushes_stepsN mxs (ds_ocap s, da_out a) (fst (snd g), snd (snd g)) (ds_ka s, da_hp a) ls
             (ds_en s) (ds_ecap s) (j + nretF (fst g)) (da_ev a) (da_erecs a) Hp
             ltac:(unfold zlen in *; lia) LF ltac:(exact HPC)) as [P1 P2].
           fold pu in P1, P2.
           pose proof (lines_mono lv mx ls (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3' (da_out a) (da_hp a)
             (da_keys a) Hoc) as M.
           change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a))
             with sl in M.
           rewrite E1 in M. cbn [fst] in M.
           assert (Hfin : oc' <= nth 0 mxs 0).
           { eapply Z.le_trans; [|exact HF].
             exact (drain_ocap_mono lv mx f s2' j4' a2' ltac:(unfold s2'; cbn [ds_ocap]; lia)). }
           assert (HKl : (zlen (ds_H s) + zlen ls + 1) * 8 <= nth 2 mxs 0) by (unfold zlen in *; lia).
           assert (HKlN : (zlen (ds_H s) + zlen ls + 1) * 8 <= NMAX) by (unfold zlen in *; lia).
           destruct (lines_stepsN lv mx mxs (fst (snd g), snd (snd g)) (16 * snd (fst pu), fst (snd pu)) ls
             (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3' (da_out a) (da_hp a) (da_keys a) Hoc Hka
             HKl HKlN LF MN
             ltac:(change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a)
                     (da_keys a)) with sl; rewrite E1; exact Hfin))
             as (uk & L1 & B1 & Z1 & K1 & HL1).
           change (lines_run lv mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) ls j3' (da_out a) (da_hp a) (da_keys a))
             with sl in L1, B1, Z1, K1, HL1.
           rewrite E1, E2 in L1. rewrite E1 in K1, HL1. cbn [fst snd] in L1, K1, HL1.
           assert (HD2 : d3I s2').
           { unfold d3I.
             split; [exact HJ2|]. split; [exact G2|]. split; [exact K1|]. split; [change (0 <= oc'); lia|].
             split; [change (0 <= if ds_off s + n =? Z.of_nat (length r0) then 0 else ds_off s + n);
                     destruct (ds_off s + n =? Z.of_nat (length r0)); lia|].
             split; [exact P2|].
             split; [change (ds_en s + Z.of_nat (length ls) + zlen (d3str s2') < 2 ^ 25); unfold zlen in *; lia|].
             change (zlen H' + zlen (d3str s2') < 2 ^ 26). unfold zlen in *. lia. }
           assert (MK2 : (zlen (ds_H s2') + zlen (d3str s2') + 1) * 8 <= nth 2 mxs 0).
           { change (ds_H s2') with H'. unfold zlen in *. lia. }
           assert (MKN2 : (zlen (ds_H s2') + zlen (d3str s2') + 1) * 8 <= NMAX).
           { change (ds_H s2') with H'. unfold zlen in *. lia. }
           destruct (IH s2' j4' a2' HD2 M1 MK2 MKN2 MN ME HF) as (u2 & cs & S1 & S2 & S3).
           exists (rcl ls ++ uk ++ u2), (d ++ cs). split; [|split].
           ++ change (rcl ls ++ uk ++ u2) with ([] ++ rcl ls ++ [] ++ uk ++ u2).
              eapply steps_app; [exact G1|]. eapply steps_app; [exact P1|].
              eapply steps_app; [apply td_steps; lia|]. eapply steps_app; [exact L1|]. exact S1.
           ++ rewrite SE, S2, app_assoc. reflexivity.
           ++ rewrite lines_app. fold ls. rewrite app_assoc. apply chg_app; [|exact S3].
              split; [intros c; rewrite bcnt_app; specialize (B1 c); lia|]. rewrite zsum_app. lia.
Qed.

Definition kmN (e : rentry) (h : hsrc) : Z :=
  Z.max (ent_ka e) ((zlen (keys_texts (re_keys e)) + zlen (bzs (pending_stream h)) + 1) * 8).

Definition slackN (lv : bool) (mx NO CAP : Z) (e : rentry) (h : hsrc) : Z :=
  (ds_ocap (drain_fin lv mx NO CAP e h) - CAP) + (Z.max (re_cap e) 32768 - re_cap e) +
  (kmN e h - ent_ka e) + (16 * ds_ecap (drain_fin lv mx NO CAP e h) - 16 * hl_cap (hs_expected h)).

Lemma drain_peakN (e : rentry) (h : hsrc) (lv : bool) (mx NO CAP : Z) (j : nat) (a : dadr) :
  0 <= re_cap e -> 0 <= ent_ka e -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  re_nheld e + Z.of_nat (length (pending_stream h)) < 2 ^ 26 ->
  (hl_cap (hs_expected h) = 0 \/ exists k, 0 <= k /\ hl_cap (hs_expected h) = 8 * 2 ^ k) ->
  hl_n (hs_expected h) + Z.of_nat (length (pending_stream h)) < 2 ^ 25 ->
  0 <= mx -> 0 <= CAP -> ds_ocap (drain_fin lv mx NO CAP e h) <= NMAX ->
  (forall Bd, slackN lv mx NO CAP e h + NMAX + credb h <= Bd ->
     tr_peak (drain_tr lv mx NO CAP e h j a) Bd) /\
  tr_db (drain_tr lv mx NO CAP e h j a) <= slackN lv mx NO CAP e h + credb h.
Proof.
  intros Hcap Hka HJ Hoff Hnh Hpow Hen Hmx Hc HN.
  unfold slackN, kmN, drain_fin, drain_tr, drain_go in *.
  set (f := S (S (length (pending_stream h)))) in *.
  set (s0 := drain_init NO CAP e h) in *.
  rewrite (drain_st lv mx f s0 0 dadr0 j a) in HN |- *.
  set (sF := fst (snd (drain_run f lv mx s0 j a))) in *.
  set (aF := snd (snd (drain_run f lv mx s0 j a))) in *.
  set (td := fst (drain_run f lv mx s0 j a)) in *.
  assert (HL0 : zlen (d3str s0) = Z.of_nat (length (pending_stream h)))
    by (unfold s0; rewrite d3str_init; unfold zlen, bzs; rewrite length_map; reflexivity).
  assert (HD0 : d3I s0).
  { unfold d3I. rewrite HL0. unfold s0, drain_init.
    cbn [ds_u ds_skip ds_ref ds_cap ds_ka ds_ocap ds_off ds_ecap ds_en ds_H].
    split; [exact HJ|]. split; [exact Hcap|]. split; [exact Hka|]. split; [lia|]. split; [exact Hoff|].
    split; [exact Hpow|]. split; [exact Hen|].
    unfold zlen, keys_texts, re_nheld in *. rewrite length_map. exact Hnh. }
  pose proof P29 as E29. pose proof P26 as E26. pose proof NMAX_v as EN.
  assert (Hc0 : 0 <= hl_cap (hs_expected h)).
  { destruct Hpow as [->|(k & Hk & ->)]; [lia|]. pose proof (Z.pow_nonneg 2 k ltac:(lia)). lia. }
  assert (HmF : CAP <= ds_ocap sF)
    by exact (drain_ocap_mono lv mx f s0 j a ltac:(unfold s0, drain_init; cbn [ds_ocap]; lia)).
  assert (HeF : hl_cap (hs_expected h) <= ds_ecap sF)
    by exact (drain_ecap_monoN lv mx f s0 j a ltac:(unfold s0, drain_init; cbn [ds_ecap]; lia)).
  set (KM := Z.max (ent_ka e) ((zlen (keys_texts (re_keys e)) + zlen (bzs (pending_stream h)) + 1) * 8)) in *.
  set (mxs := [ds_ocap sF; Z.max (re_cap e) 32768; KM; 16 * ds_ecap sF]).
  assert (EH0 : zlen (ds_H s0) = zlen (keys_texts (re_keys e))) by reflexivity.
  assert (ES0 : d3str s0 = bzs (pending_stream h)) by (unfold s0; apply d3str_init).
  assert (HKm : (zlen (ds_H s0) + zlen (d3str s0) + 1) * 8 <= nth 2 mxs 0)
    by (unfold mxs; cbn [nth]; rewrite EH0, ES0; unfold KM; apply Z.le_max_r).
  assert (HKn : (zlen (ds_H s0) + zlen (d3str s0) + 1) * 8 <= NMAX).
  { rewrite EH0, HL0. unfold zlen, keys_texts, re_nheld in *. rewrite length_map. lia. }
  destruct (drain_stepsN lv mx mxs f s0 j a HD0 ltac:(unfold mxs; cbn [nth]; lia) HKm HKn
    ltac:(unfold mxs; cbn [nth]; exact HN) ltac:(unfold mxs; cbn [nth]; apply Z.le_refl)
    ltac:(unfold mxs; cbn [nth]; apply Z.le_refl)) as (u & cs & ST & SE & SC).
  change (fst (snd (drain_run f lv mx s0 j a))) with sF in ST, SE.
  change (snd (snd (drain_run f lv mx s0 j a))) with aF in ST.
  change (fst (drain_run f lv mx s0 j a)) with td in ST.
  set (g0 := [(CAP, da_out a); (re_cap e, da_buf a); (ent_ka e, da_hp a);
              (16 * hl_cap (hs_expected h), da_ev a)]).
  change (d3sig s0 a) with g0 in ST.
  assert (HKl : ent_ka e <= KM) by (unfold KM; apply Z.le_max_l).
  assert (HB0 : bnd g0 mxs).
  { unfold bnd, g0, mxs. constructor; [cbv beta; cbn [fst]; lia|]. constructor; [cbv beta; cbn [fst]; lia|].
    constructor; [cbv beta; cbn [fst]; lia|]. constructor; [cbv beta; cbn [fst]; lia|]. constructor. }
  assert (HJw : ls_k (hs_state h) = false -> zlen (ls_w (hs_state h)) <= 6000 /\ nozero (ls_w (hs_state h))).
  { destruct HJ as (Hk & Hw & Hl & Hz). intros E. rewrite <- Hw by (rewrite Hk; exact E).
    split; [unfold zlen; apply LL_le; exact Hl|exact Hz]. }
  assert (ENEW : lines (hs_state h) (bzs (pending_stream h)) =
                 lines (hs_state h) cs ++ lines (feed (hs_state h) cs) (d3str sF)).
  { rewrite <- lines_app, <- SE. rewrite ES0. reflexivity. }
  assert (LFN : Forall (fun l => zlen l <= 6000) (lines (hs_state h) (bzs (pending_stream h))))
    by (apply lines_len6; intros E; exact (proj1 (HJw E))).
  destruct (new_cred h HJw) as [_ CR2].
  rewrite ENEW in LFN, CR2.
  destruct (chg_new (lines (hs_state h) cs) (lines (feed (hs_state h) cs) (d3str sF)) LFN) as [_ CN2].
  destruct SC as [_ SC2].
  assert (Er : ds_ref s0 = hs_state h) by reflexivity. rewrite Er in SC2.
  pose proof (ekl_line _ LFN) as (_ & _ & _ & EK).
  pose proof (zsum_id_nonneg _ EK) as EK0.
  assert (UZ : zsum (fun n => n) u <= credb h) by lia.
  assert (Emx : zsum (fun m => m) mxs = ds_ocap sF + Z.max (re_cap e) 32768 + KM + 16 * ds_ecap sF)
    by (unfold mxs, zsum; cbn [fold_right]; lia).
  assert (Ebkb : bkb g0 = CAP + re_cap e + ent_ka e + 16 * hl_cap (hs_expected h))
    by (unfold bkb, g0, zsum; cbn [fold_right fst]; lia).
  split.
  - intros Bd HBd. apply (steps_peak mxs j g0 td (d3sig sF aF) u ST HB0). rewrite Emx, Ebkb. lia.
  - pose proof (bnd_nonneg _ _ HB0) as HG0.
    destruct (steps_eff _ _ _ _ _ _ ST HG0) as (_ & _ & DB).
    pose proof (bnd_bkb _ _ (steps_bnd _ _ _ _ _ _ ST HB0)) as BK.
    rewrite Emx in BK. rewrite Ebkb in DB. lia.
Qed.

Lemma ecapF_boundN (e : rentry) (h : hsrc) (lv : bool) (mx NO CAP : Z) :
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  16 * ds_ecap (drain_fin lv mx NO CAP e h) <=
    Z.max (16 * hl_cap (hs_expected h)) (NC_PER * hl_n (hs_expected h) + 128) +
    NC_PER * zlen (lines (hs_state h) (bzs (pending_stream h))).
Proof.
  intros HJ Hoff. unfold drain_fin, drain_go.
  set (f := S (S (length (pending_stream h)))).
  set (s0 := drain_init NO CAP e h).
  assert (HI : dwI s0)
    by (unfold dwI, s0, drain_init; cbn [ds_u ds_skip ds_ref ds_off]; split; [exact HJ|exact Hoff]).
  destruct (dw_run lv mx f s0 0 dadr0 HI) as (cs & SE & Erf & S1 & S2 & S4).
  set (sF := fst (snd (drain_run f lv mx s0 0 dadr0))) in *.
  assert (EP : d3str s0 = bzs (pending_stream h)) by (unfold s0; apply d3str_init).
  assert (ELs : lines (hs_state h) (bzs (pending_stream h)) =
                lines (hs_state h) cs ++ lines (feed (hs_state h) cs) (d3str sF))
    by (rewrite <- lines_app, <- SE, EP; reflexivity).
  assert (LE : zlen (lines (hs_state h) cs) <= zlen (lines (hs_state h) (bzs (pending_stream h))))
    by (rewrite ELs, dw_zlen_app; unfold zlen; lia).
  unfold dw4 in S4. unfold s0, drain_init in S4. cbn [ds_en ds_ecap ds_ref] in S4.
  unfold NC_PER in *. lia.
Qed.

Lemma lines_credN (h : hsrc) (u : list Z) (sk : bool) : J1 u sk (hs_state h) ->
  zlen (lines (hs_state h) (bzs (pending_stream h))) <= zsumZ (cred h) (zseq 0 49).
Proof.
  intros HJ.
  assert (HJw : ls_k (hs_state h) = false -> zlen (ls_w (hs_state h)) <= 6000 /\ nozero (ls_w (hs_state h))).
  { destruct HJ as (Hk & Hw & Hl & Hz). intros E. rewrite <- Hw by (rewrite Hk; exact E).
    split; [unfold zlen; apply LL_le; exact Hl|exact Hz]. }
  assert (LFN : Forall (fun l => zlen l <= 6000) (lines (hs_state h) (bzs (pending_stream h))))
    by (apply lines_len6; intros E; exact (proj1 (HJw E))).
  destruct (new_cred h HJw) as [CR _].
  destruct (dw_copies _ LFN) as [CP CN].
  rewrite <- (bcnt_sum _ CN) in CP.
  assert (E0 : 0 <= zlen (ekl (lines (hs_state h) (bzs (pending_stream h))))) by (unfold zlen; lia).
  assert (X : zsumZ (fun c => bcnt c (flat_map line_copies (lines (hs_state h) (bzs (pending_stream h)))))
                (zseq 0 49) <= zsumZ (cred h) (zseq 0 49))
    by (apply zsumZ_le; intros c _; exact (CR c)).
  lia.
Qed.

Definition ssN (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then
    32768
    + (kmN (fst p) (fst (snd p)) - ent_ka (fst p))
    + (Z.max (16 * hl_cap (hs_expected (fst (snd p)))) (NC_PER * hl_n (hs_expected (fst (snd p))) + 128)
       - 16 * hl_cap (hs_expected (fst (snd p))))
    + NC_PER * zlen (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p)))))
    + credb (fst (snd p))
  else 0.

Lemma ssN_nonneg p : 0 <= ssN p.
Proof.
  unfold ssN. destruct (re_eof (fst p) =? 0); [|lia].
  pose proof (credb_nonneg (fst (snd p))).
  pose proof (Z.le_max_l (16 * hl_cap (hs_expected (fst (snd p))))
                (NC_PER * hl_n (hs_expected (fst (snd p))) + 128)).
  pose proof (Z.le_max_l (ent_ka (fst p))
    ((zlen (keys_texts (re_keys (fst p))) + zlen (bzs (pending_stream (fst (snd p)))) + 1) * 8)).
  unfold kmN.
  assert (0 <= zlen (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))))
    by (unfold zlen; lia).
  unfold NC_PER in *. lia.
Qed.

Lemma slack_ssN lv mx no cap e h i :
  0 <= re_cap e -> 0 <= ent_ka e -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  re_eof e = 0 ->
  slackN lv mx no cap e h + credb h <= (ds_ocap (drain_fin lv mx no cap e h) - cap) + ssN (e, (h, i)).
Proof.
  intros Hcap Hka HJ Hoff Eeof. unfold slackN, ssN. cbn [fst snd].
  rewrite (proj2 (Z.eqb_eq (re_eof e) 0) Eeof).
  pose proof (ecapF_boundN e h lv mx no cap HJ Hoff) as EB.
  assert (Z0 : 0 <= zlen (keys_texts (re_keys e))) by (unfold zlen; lia).
  assert (Z1 : 0 <= zlen (bzs (pending_stream h))) by (unfold zlen; lia).
  unfold NC_PER in *. lia.
Qed.

Lemma gone_peak_compN ps : forall lv mx no cap pre nm j o,
  0 <= mx -> 0 <= cap ->
  Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) ps ->
  Forall (fun p => re_eof (fst p) = 0 ->
            0 <= re_cap (fst p) /\ 0 <= ent_ka (fst p) /\
            J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p))) /\
            0 <= hs_off (fst (snd p)) /\
            re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26 /\
            (hl_cap (hs_expected (fst (snd p))) = 0 \/
             exists k0, 0 <= k0 /\ hl_cap (hs_expected (fst (snd p))) = 8 * 2 ^ k0) /\
            hl_n (hs_expected (fst (snd p))) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 25 /\
            Z.of_nat (length (re_U (fst p))) <= re_used (fst p)) ps ->
  snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) <= NMAX ->
  tr_db (fst (fst (fst (gone_run lv mx no cap pre ps nm j o)))) <=
    (snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) - cap) + zsum ssN ps /\
  (forall Bd, (snd (fst (fst (gone_run lv mx no cap pre ps nm j o))) - cap) + zsum ssN ps + NMAX <= Bd ->
     tr_peak (fst (fst (fst (gone_run lv mx no cap pre ps nm j o)))) Bd).
Proof.
  induction ps as [|[e hj] ps IH]; intros lv mx no cap pre nm j o Hm Hc HD HF HN.
  - cbn [gone_run fst snd]. rewrite zsum_nil, tr_db_nil.
    split; [lia|intros Bd _; apply tr_peak_nil].
  - pose proof HD as HD0. apply Forall_cons_iff in HD as [Hd HD].
    pose proof HF as HF0. apply Forall_cons_iff in HF as [Hf HF]. cbn [fst snd] in Hd, Hf.
    pose proof (gone_mono ((e, hj) :: ps) lv mx no cap pre nm j o HD0 Hm Hc) as Mc.
    destruct (gone_run_cons lv mx no cap pre e hj ps nm j o)
      as (s & a0 & td & a & xks & k & g & Es & Ea0 & Etd & Ea & Ex & Ek & Eg & T1 & T2 & T3 & T4).
    rewrite T1, T2 in *.
    set (capF := snd (fst (fst g))) in *.
    assert (HX : Forall (fun x => 0 <= fst x) xks).
    { rewrite Ex. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (y & <- & _). cbn [fst]. lia. }
    assert (Hmo : cap <= ds_ocap s).
    { rewrite Es. unfold after_drain. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
      - exact (proj1 (Hd E0 lv mx no cap Hm Hc)).
      - cbn [drain_init ds_ocap]. lia. }
    assert (Hke : ds_ocap s <= fst (snd k)) by (rewrite Ek; apply ke_mono; lia).
    assert (Hgm : fst (snd k) <= capF) by (unfold capF; rewrite Eg; apply gone_mono; [exact HD|exact Hm|lia]).
    assert (HSS0 : 0 <= zsum ssN ps) by (apply zsum_nonneg; intros x _; apply ssN_nonneg).
    assert (DTD : tr_db td <= (ds_ocap s - cap) + ssN (e, hj) /\
                  (forall Bd, (ds_ocap s - cap) + ssN (e, hj) + NMAX <= Bd -> tr_peak td Bd)).
    { destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
      - destruct (Hf E0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _).
        assert (X8 : hl_cap (hs_expected (fst hj)) = 0 \/
                     exists k1, 0 <= k1 /\ hl_cap (hs_expected (fst hj)) = 8 * 2 ^ k1)
          by (destruct X6 as [Y|(k1 & Hk1 & Y)]; [left; exact Y|right; exists k1; split; [lia|exact Y]]).
        assert (Esf : s = drain_fin lv mx no cap e (fst hj))
          by (rewrite Es; unfold after_drain; rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
        assert (HNf : ds_ocap (drain_fin lv mx no cap e (fst hj)) <= NMAX) by (rewrite <- Esf; lia).
        destruct (drain_peakN e (fst hj) lv mx no cap j a0 X1 X2 X3 X4 X5 X8 X7 Hm Hc HNf) as [DP DB].
        pose proof (slack_ssN lv mx no cap e (fst hj) (snd hj) X1 X2 X3 X4 E0) as SL.
        rewrite <- Esf in SL.
        assert (Etd' : td = drain_tr lv mx no cap e (fst hj) j a0) by exact Etd.
        rewrite Etd'. replace (e, (fst hj, snd hj)) with (e, hj) in SL by (destruct hj; reflexivity).
        split; [lia|]. intros Bd HBd. apply DP. lia.
      - assert (Etd' : td = []) by exact Etd.
        assert (Eoc : ds_ocap s = cap)
          by (rewrite Es; unfold after_drain; rewrite (proj2 (Z.eqb_neq _ _) E0);
              cbn [drain_init ds_ocap]; reflexivity).
        assert (Ess : ssN (e, hj) = 0) by (unfold ssN; cbn [fst]; rewrite (proj2 (Z.eqb_neq _ _) E0); reflexivity).
        rewrite Etd', tr_db_nil, Ess, Eoc. split; [lia|intros Bd _; apply tr_peak_nil]. }
    destruct DTD as [DB1 DP1].
    destruct (p4p_ke_peak xks lv mx (ds_no s) (ds_ocap s) (j + nretF td)%nat (da_out a)
      (capF - ds_ocap s + zsum ssN ps + NMAX) Hm ltac:(lia) HX ltac:(rewrite <- Ek; lia)
      ltac:(rewrite <- Ek; lia)) as [KP KB].
    rewrite <- Ek in KP, KB.
    destruct (IH lv mx (ds_no s + fold_right (fun xl acc => xl + 5 + acc) 0 (map fst xks)) (fst (snd k)) pre nm
      (j + nretF td + nretF (fst k))%nat (snd (snd k)) Hm ltac:(lia) HD HF
      ltac:(rewrite <- Eg; unfold capF in *; lia)) as [GB GP].
    rewrite <- Eg in GB, GP. fold capF in GB, GP.
    rewrite zsum_cons. cbv beta.
    split.
    + rewrite !tr_db_app. lia.
    + intros Bd HBd. apply tr_peak_app; [apply DP1; lia|].
      apply tr_peak_app; [eapply tr_peak_mono; [|exact KP]; lia|].
      apply GP. lia.
Qed.

Lemma zsumN_add {X : Type} (f g : X -> Z) l : zsum (fun x => f x + g x) l = zsum f l + zsum g l.
Proof.
  induction l as [|x l IH]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons. cbv beta. lia.
Qed.

Lemma zsumN_mul {X : Type} (c : Z) (f : X -> Z) l : zsum (fun x => c * f x) l = c * zsum f l.
Proof.
  induction l as [|x l IH]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons. cbv beta. lia.
Qed.

Lemma zsumN_comb {X Y : Type} (F : X -> Z) (G : Y -> Z) (l1 : list X) (l2 : list Y) :
  length l2 = length l1 -> zsum (fun p => F (fst p) + G (snd p)) (combine l1 l2) = zsum F l1 + zsum G l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] HL; cbn [length] in HL; try discriminate.
  - cbn [combine]. rewrite !zsum_nil. lia.
  - cbn [combine]. rewrite !zsum_cons. cbv beta. cbn [fst snd]. rewrite (IH l2 ltac:(lia)). lia.
Qed.

Lemma zsumN_card {X : Type} (f : X -> Z) (c : Z) l : 0 <= c -> (forall x, In x l -> f x <= c) ->
  zsum f l <= c * Z.of_nat (length l).
Proof.
  intros Hc H. induction l as [|x l IH]; [rewrite zsum_nil; cbn [length]; lia|].
  rewrite zsum_cons. cbn [length]. pose proof (H x (or_introl eq_refl)).
  pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

Lemma zsumN_4 {X : Type} (f g h i : X -> Z) (c : Z) l :
  zsum (fun x => f x + g x + c * h x + i x) l = zsum f l + zsum g l + c * zsum h l + zsum i l.
Proof.
  induction l as [|x l IH]; [rewrite !zsum_nil; lia|]. rewrite !zsum_cons. cbv beta. lia.
Qed.

Definition wN (p : rentry * (hsrc * nat)) : Z :=
  (re_cap (fst p) + ent_ka (fst p)) +
  (16 * hl_cap (hs_pending (fst (snd p))) + 6000 + 16 * hl_cap (hs_expected (fst (snd p))) +
   16 * hl_cap (hs_held (fst (snd p)))).

Definition nwN (p : rentry * (hsrc * nat)) : Z := nw_ent (fst p) + nw_src (fst (snd p)).

Definition pnN (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then 8 * zlen (bzs (pending_stream (fst (snd p)))) + 32768 else 0.

Definition lnN (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0
  then zlen (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))) else 0.

Definition cnN (p : rentry * (hsrc * nat)) : Z :=
  if re_eof (fst p) =? 0 then credb (fst (snd p)) else 0.

Lemma gone_lines_credN ps :
  Forall (fun p => re_eof (fst p) = 0 ->
            J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p)))) ps ->
  zsum (fun p => if re_eof (fst p) =? 0
                 then zlen (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))) else 0) ps
  <= zsumZ (gone_cred ps) (zseq 0 49).
Proof.
  induction ps as [|[e hj] ps IH]; intros HJ.
  - rewrite zsum_nil. apply zsumZ_nonneg. intros c _. apply gone_cred_nonneg.
  - apply Forall_cons_iff in HJ as [Hj HJ]. cbn [fst snd] in Hj.
    rewrite zsum_cons, gone_cred_sum. cbv beta. cbn [fst snd].
    pose proof (IH HJ) as R.
    destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0].
    + pose proof (lines_credN (fst hj) (bzs (re_U e)) (re_skip e =? 1) (Hj E0)) as X. lia.
    + lia.
Qed.

Lemma gone_peakN pl k L A b al alb G OUT es hs lv mx NO CAP pre :
  RI3_ledger rv_wt pl k (view_of G OUT es hs) L A b al alb -> res_ok_pack3 A b ->
  length hs = length es -> (length es <= 4)%nat -> 0 <= mx -> 0 <= CAP ->
  Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) (combine es hs) ->
  Forall (fun p => re_eof (fst p) = 0 ->
            0 <= re_cap (fst p) /\ 0 <= ent_ka (fst p) /\
            J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p))) /\
            0 <= hs_off (fst (snd p)) /\
            re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 26 /\
            (hl_cap (hs_expected (fst (snd p))) = 0 \/
             exists k0, 0 <= k0 /\ hl_cap (hs_expected (fst (snd p))) = 8 * 2 ^ k0) /\
            hl_n (hs_expected (fst (snd p))) + Z.of_nat (length (pending_stream (fst (snd p)))) < 2 ^ 25 /\
            Z.of_nat (length (re_U (fst p))) <= re_used (fst p)) (combine es hs) ->
  gone_cap lv mx NO CAP pre es hs <= NMAX ->
  List.NoDup (map fst (blocks L A)) ->
  (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
  0 <= NO <= CAP ->
  In (G, relay_add_b_c.SRC_TABLE) (blocks L A) ->
  (CAP = 0 \/ In (OUT, CAP) (blocks L A)) ->
  Forall (SlotPass4.p4_ent_blk L A) es ->
  Forall (fun p => SlotPass4.p4_src_blk L A (fst p)) hs ->
  tr_peak (relay_instance_gone_tr lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
          (CF_MAX - p3_bytes b).
Proof.
  intros HL HR Hlen Hes Hmx Hc HD HF HN HNC HO0 HNO HGB HOB HPE HPS.
  pose proof HL as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  assert (HJF : Forall (fun p => re_eof (fst p) = 0 ->
                  J1 (bzs (re_U (fst p))) (re_skip (fst p) =? 1) (hs_state (fst (snd p)))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (_ & _ & Y & _). exact Y. }
  destruct (gone_peak_compN (combine es hs) lv mx NO CAP pre (known_at L A) 0 (known_at L A OUT) Hmx Hc HD HF
    ltac:(change (snd (fst (fst (gone_run lv mx NO CAP pre (combine es hs) (known_at L A) 0
            (known_at L A OUT))))) with
            (gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT));
          rewrite gone_capT_eq; exact HN)) as [_ GP].
  unfold relay_instance_gone_tr. eapply tr_peak_mono; [|apply GP; apply Z.le_refl].
  change (snd (fst (fst (gone_run lv mx NO CAP pre (combine es hs) (known_at L A) 0 (known_at L A OUT)))))
    with (gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT)).
  rewrite gone_capT_eq.
  pose proof (ncsN L A G OUT CAP es hs HNC HGB HO0 HOB HPE HPS) as NCS.
  assert (NCS2 : ncs (view_of G OUT es hs) L A <= relay_add_b_c.SRC_TABLE + CAP + zsum wN (combine es hs)).
  { assert (E : zsum wN (combine es hs) =
      zsum (fun e => re_cap e + ent_ka e) es +
      zsum (fun p => 16 * hl_cap (hs_pending (fst p)) + 6000 + 16 * hl_cap (hs_expected (fst p)) +
                     16 * hl_cap (hs_held (fst p))) hs)
      by exact (zsumN_comb (fun e => re_cap e + ent_ka e)
                 (fun p => 16 * hl_cap (hs_pending (fst p)) + 6000 + 16 * hl_cap (hs_expected (fst p)) +
                           16 * hl_cap (hs_held (fst p))) es hs Hlen).
    lia. }
  clear NCS.
  assert (PW : forall p, In p (combine es hs) -> wN p + ssN p <= nwN p + pnN p + 32 * lnN p + cnN p).
  { intros p Hp. unfold wN, nwN, pnN, lnN, cnN, ssN, kmN, nw_ent, nw_src, nw_list.
    pose proof (credb_nonneg (fst (snd p))) as CB.
    assert (LZ : 0 <= zlen (lines (hs_state (fst (snd p))) (bzs (pending_stream (fst (snd p))))))
      by (unfold zlen; lia).
    assert (EK : zlen (keys_texts (re_keys (fst p))) = re_nheld (fst p))
      by (unfold zlen, keys_texts, re_nheld; rewrite length_map; reflexivity).
    assert (EB : zlen (bzs (pending_stream (fst (snd p)))) = Z.of_nat (length (pending_stream (fst (snd p)))))
      by (unfold zlen, bzs; rewrite length_map; reflexivity).
    rewrite EK, EB.
    change (if re_hp (fst p) =? 0 then 0 else re_kh (fst p)) with (ent_ka (fst p)).
    pose proof (Z.le_max_l (re_cap (fst p)) (DATA_PER * re_used (fst p) + 8192)) as M1.
    pose proof (Z.le_max_l (16 * hl_cap (hs_pending (fst (snd p))))
      (NC_PER * hl_n (hs_pending (fst (snd p))) + 128)) as M2.
    pose proof (Z.le_max_l (16 * hl_cap (hs_held (fst (snd p))))
      (NC_PER * hl_n (hs_held (fst (snd p))) + 128)) as M3.
    pose proof (Z.max_spec (ent_ka (fst p)) (8 * re_nheld (fst p) + 8)) as M4.
    pose proof (Z.max_spec (ent_ka (fst p))
      ((re_nheld (fst p) + Z.of_nat (length (pending_stream (fst (snd p)))) + 1) * 8)) as M5.
    assert (PZ : 0 <= Z.of_nat (length (pending_stream (fst (snd p))))) by lia.
    unfold NC_PER, DATA_PER, op_add_c.PARTIAL_BYTES in *.
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [E0|E0]; lia. }
  assert (SUM : zsum (fun p => wN p + ssN p) (combine es hs) <=
                zsum (fun p => nwN p + pnN p + 32 * lnN p + cnN p) (combine es hs))
    by (apply nw_zsum_le; exact PW).
  pose proof (zsumN_add wN ssN (combine es hs)) as E1.
  pose proof (zsumN_4 nwN pnN lnN cnN 32 (combine es hs)) as E2.
  assert (E6 : zsum nwN (combine es hs) = zsum nw_ent es + zsum (fun q => nw_src (fst q)) hs)
    by exact (zsumN_comb nw_ent (fun q => nw_src (fst q)) es hs Hlen).
  assert (EW : rv_wt (view_of G OUT es hs) = nc_wt es hs) by reflexivity.
  assert (NWS : zsum nw_ent es + zsum (fun q => nw_src (fst q)) hs <=
                rv_wt (view_of G OUT es hs) - relay_add_b_c.SRC_TABLE - TBBYTES).
  { rewrite EW. unfold nc_wt. unfold NW_ENT0, NW_SRC0, op_add_c.PARTIAL_BYTES.
    assert (Z.of_nat (length es) <= 4) by lia. assert (Z.of_nat (length hs) <= 4) by (rewrite Hlen; lia). lia. }
  assert (E25 : 2 ^ 25 = 33554432) by reflexivity.
  assert (PEND : zsum pnN (combine es hs) <= 268468224 * Z.of_nat (length (combine es hs))).
  { apply zsumN_card; [lia|]. intros p Hp. unfold pnN.
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [E0|E0]; [|lia].
    destruct (proj1 (Forall_forall _ _) HF p Hp E0) as (_ & _ & _ & _ & _ & _ & Y & _).
    assert (HN0 : 0 <= hl_n (hs_expected (fst (snd p)))) by (unfold hl_n; lia).
    assert (EB : zlen (bzs (pending_stream (fst (snd p)))) = Z.of_nat (length (pending_stream (fst (snd p)))))
      by (unfold zlen, bzs; rewrite length_map; reflexivity).
    rewrite EB. lia. }
  assert (HCard : Z.of_nat (length (combine es hs)) <= 4)
    by (pose proof (combine_len_le es hs); lia).
  assert (LCR : zsum lnN (combine es hs) <= zsumZ (gone_cred (combine es hs)) (zseq 0 49))
    by exact (gone_lines_credN (combine es hs) HJF).
  assert (EP : rv_pend (view_of G OUT es hs) = pend_view hs) by reflexivity.
  assert (PRM : zsumZ (gone_cred (combine es hs)) (zseq 0 49) <= ALSUM_MAX - alsum al).
  { assert (X1 : zsumZ (gone_cred (combine es hs)) (zseq 0 49) <=
                 zsumZ (fun c => prom_c (pend_view hs) c) (zseq 0 49)).
    { apply zsumZ_le. intros c Hc1. cbv beta.
      pose proof (prom_gone es hs c Hlen) as PG.
      pose proof (prom_c_nonneg (gone_pend es hs) c). lia. }
    assert (X2 : zsumZ (fun c => znth c al + prom_c (pend_view hs) c) (zseq 0 49) <=
                 zsumZ (fun c => cons_c pl k c) (zseq 0 49)).
    { apply zsumZ_le. intros c Hc1. cbv beta. apply In_zseq in Hc1.
      pose proof (ledger3_credit _ _ _ _ _ _ _ _ _ c HL ltac:(lia)) as Y. rewrite EP in Y.
      pose proof (ek_c_nonneg (view_of G OUT es hs) c). lia. }
    pose proof (zsumZ_add (fun c => znth c al) (fun c => prom_c (pend_view hs) c) (zseq 0 49)) as E7.
    cbv beta in E7.
    pose proof (cons_sum pl k) as CS. unfold alsum. lia. }
  assert (CRB : zsum cnN (combine es hs) <= promb (pend_view hs)).
  { assert (ECN : zsum cnN (combine es hs) = gone_credb (combine es hs)) by reflexivity.
    pose proof (promb_gone es hs Hlen). pose proof (promb_nonneg (gone_pend es hs)). lia. }
  pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LB. rewrite EP in LB.
  pose proof (consb_le pl k) as CBL.
  pose proof (ek_b_nonneg (view_of G OUT es hs) C7) as EBN.
  pose proof (cdat_le pl k) as CDL.
  assert (NUM : PDRV_BYTES + relay_add_b_c.SRC_TABLE +
                (NC_FIX + 2 * BTEXT - relay_add_b_c.SRC_TABLE - TBBYTES) +
                268468224 * 4 + 32 * ALSUM_MAX + CONSB_MAX + 2 * NMAX <= CF_MAX)
    by (apply Z.leb_le; vm_compute; reflexivity).
  assert (CAP0 : 0 <= CAP) by lia.
  assert (HC4 : 268468224 * Z.of_nat (length (combine es hs)) <= 268468224 * 4) by lia.
  clear HD HF HJF GP PW HL HR C1 C2 C3 C4 C5 C7 C9 C11 C12 C13 HPE HPS HGB HOB HO0 HNC.
  assert (S1 : zsum wN (combine es hs) + zsum ssN (combine es hs) <=
               zsum nwN (combine es hs) + zsum pnN (combine es hs) +
               32 * zsum lnN (combine es hs) + zsum cnN (combine es hs)) by lia.
  assert (S2 : zsum nwN (combine es hs) <=
               rv_wt (view_of G OUT es hs) - relay_add_b_c.SRC_TABLE - TBBYTES) by lia.
  assert (S3 : 32 * zsum lnN (combine es hs) <= 32 * (ALSUM_MAX - alsum al)) by lia.
  assert (S4 : zsum cnN (combine es hs) <= CONSB_MAX - alb) by lia.
  assert (S5 : rv_wt (view_of G OUT es hs) <= NC_FIX + 32 * alsum al + 2 * cdat pl k) by exact C10.
  assert (S5' : 2 * cdat pl k <= 2 * BTEXT) by lia.
  assert (S6 : p3_bytes b <= PDRV_BYTES + relay_add_b_c.SRC_TABLE + CAP +
                             zsum wN (combine es hs) + alb) by lia.
  lia.
Qed.

Theorem p5c_res3_fullN_holds OK RM : RMH RM -> p5c_res3_fullN OK RM.
Proof.
  intros HRM E K K' L A G OUT es hs lv mx NO CAP pre. cbv zeta.
  intros ((b & al & alb & HR & HL) & HOK) Hk Hlen Hes Hmx Hc HF HN Hkh HB HO0 HNC HGB HOB HPE HPS.
  assert (HD : Forall (fun p => re_eof (fst p) = 0 -> drain3 (fst p) (fst (snd p))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
    exact (drain3_holds _ _ H1 H2 H3 H4 H5 H6 H7). }
  assert (HW : Forall (fun p => re_eof (fst p) = 0 -> drain_wt3 (fst p) (fst (snd p))) (combine es hs)).
  { eapply Forall_impl; [|exact HF]. intros p Hp E0. destruct (Hp E0) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exact (drain_wt3_holds _ _ H1 H2 H3 H4 H5 H6 H7 H8). }
  assert (HNT : gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT) <= NMAX)
    by (rewrite gone_capT_eq; exact HN).
  pose proof (gone_misT_call (ss_pl E) K L A b al alb G OUT es hs CAP HL HR Hlen Hes Hkh HB HO0) as HS.
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + exact (gone_room3 rv_wt (ss_pl E) K L A b al alb G OUT es hs lv mx NO CAP pre _ HL HD Hes Hmx Hc HNT HS qs Hq).
    + pose proof HL as (HCs & HMc & _).
      apply (RMrun_of_peak RM (ss_pl E) b _ (CF_MAX - p3_bytes b) HRM HCs HMc); [lia|].
      exact (gone_peakN (ss_pl E) K L A b al alb G OUT es hs lv mx NO CAP pre HL HR Hlen Hes Hmx Hc HD HF HN
               HB HO0 HNC HGB HOB HPE HPS).
  - intros L' A' qs Hq (HR' & HOK') V' HN' HC' HB' HW1' HW' HP' HEc HEb HEF HB2 HO HF12 HF13.
    split; [|exact HOK']. rewrite runF_pack3P in HR'.
    pose proof HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HW2 & _ & HMis & _).
    assert (Hstep : call_step3 rv_wt (ss_pl E) K' (view_of G OUT es hs) L A V' L' A' al alb
              (gone_dl lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
              (gone_db lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT)) (gone_da es hs) (gone_dab es hs)).
    { pose proof (cdat_mono (ss_pl E) K K' Hk). pose proof (consb_mono (ss_pl E) K K' Hk).
      pose proof (gone_wd_le (combine es hs) lv mx NO CAP pre (fun _ => adr0) 0 adr0 Hmx Hc HD HW) as WD.
      unfold gone_states in HW'.
      assert (DA : zsumZ (gone_da es hs) (zseq 0 49) =
                   zsumZ (gone_cred (combine es hs)) (zseq 0 49) - zlen (gone_ek (combine es hs))).
      { unfold gone_da.
        rewrite (zsumZ_ext _ (fun c => gone_cred (combine es hs) c + (-1) * bcnt c (gone_ek (combine es hs))))
          by (intros; lia).
        rewrite zsumZ_add, zsumZ_mul_l, (bcnt_sum _ (gone_ek_nonneg _)). lia. }
      split; [exact HN'|]. split; [exact HC'|]. split; [exact HB'|]. split; [exact HW1'|].
      split; [rewrite DA; unfold NC_PER, DATA_PER in *; lia|].
      split; [|split; [|exact HEF]].
      - intros c Hc'. rewrite (HEc c Hc'), HP'. pose proof (prom_gone es hs c Hlen) as PG.
        pose proof (ledger3_credit _ _ _ _ _ _ _ _ _ c HL Hc') as LC. cbn [view_of rv_pend] in LC.
        pose proof (cons_mono (ss_pl E) K K' c Hk). unfold gone_da. lia.
      - rewrite HEb, HP'. pose proof (promb_gone es hs Hlen). pose proof (ledger3_creditb _ _ _ _ _ _ _ _ _ HL) as LB.
        cbn [view_of rv_pend] in LB. unfold gone_dab. lia. }
    assert (H0 : misK (p3_mis b) (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs)))
                   (slot3 CAP (resolveF qs (known_at L A OUT)) ++ concat (map (gslots qs (known_at L A)) (combine es hs)) ++ [])
                   (p3_mis b))
      by (eapply misK_S; [|apply misK_init]; intros x Hx; rewrite app_nil_r; exact Hx).
    pose proof (gone_misK (p3_mis b) _ qs (combine es hs) lv mx NO CAP pre (known_at L A) 0 (known_at L A OUT) b [] Hc H0)
      as GM.
    cbv zeta in GM.
    assert (Hmis : mis_nc V' L' (p3_mis (runF pack3_form qs b
                     (relay_instance_gone_tr lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))))).
    { apply (mis_nc_post L A b L' A' _ (view_of G OUT es hs) V'
               (slot3 CAP (sptr_of L A OUT) ++ concat (map (gslots [] (known_at L A)) (combine es hs)))
               (slot3 (gone_capT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
                      (resolveF qs (gone_out lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))) ++
                gfin qs (combine es hs) (gone_ssT lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT))
                  (gone_adrs lv mx NO CAP pre es hs (known_at L A) 0 (known_at L A OUT)))
               HR HMis HR' HB2).
      - rewrite runF3. unfold relay_instance_gone_tr, gone_capT, gone_out, gone_ssT, gone_adrs.
        eapply misK_S; [|exact GM]. intros x Hx. rewrite app_nil_r in Hx. exact Hx.
      - intros p Hp. apply in_app_or in Hp as [Hp|Hp].
        + apply slot3_in in Hp as (Hp0 & <-). rewrite gone_capT_eq in Hp0. exact (HF12 Hp0).
        + destruct (gfin_in qs _ _ _ p Hp) as (i & Hi1 & Hi2 & Hi3 & Hi4 & Hi5).
          rewrite (combine_len es hs Hlen) in Hi1.
          rewrite (combine_nth es hs i no_entry no_hj (eq_sym Hlen)) in Hi4. cbn [fst] in Hi4.
          destruct (HF13 i Hi1 Hi4) as (F1 & F2 & F3).
          rewrite gone_ssT_eq in Hi2, Hi5.
          rewrite (nth_dflt _ i ds0 (drain_init NO CAP (nth i es no_entry) (fst (nth i hs no_hj))) Hi2) in Hi5.
          unfold dsl in Hi5. rewrite !in_app_iff in Hi5.
          destruct Hi5 as [Hp1|[Hp1|Hp1]]; apply slot3_in in Hp1 as (Hp0 & <-);
            first [exact (F1 Hp0) | exact (F2 Hp0) | exact (F3 Hp0)].
      - intros p n Hb Hv Hn. apply (HO p n Hb Hv). exact (gone_tch_cover L A OUT CAP es hs p n HB Hb Hn). }
    exact (gone_ri3 E K K' L A L' A' V' b al alb G OUT es hs lv mx NO CAP pre _ qs HL HD Hes Hmx Hc HNT HS HR' Hstep Hmis).
Qed.
