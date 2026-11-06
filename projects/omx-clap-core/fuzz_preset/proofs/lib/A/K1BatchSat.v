(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/K1BatchSat.v, with its module paths and numbers changed; 88 of its 321 lines of code are new or changed and 8 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30: BATCH-SAT (VERIFY rule 1), a check of the batch of premise texts the kit's cut changed
   (its PRH_Base.v blob ef7c8ca98529), as this tree states them (lib/A/PRH_*.v). A MEASUREMENT FILE: it proves no
   function.
   For each NEW or CHANGED premise text of the batch outside the slot precondition (its items 4a / 4b are not here), a
   satisfiability witness at the REAL instances - image A' (PRH_Img.prh_img_A, AD2l.TfibB, CfImgA.CfImg_A) and
   image B' (PRH_ImgB.prh_img_B, YD2l.TfibB, CfImgB.CfImg_B), the start state YG00.init_state, cp :=
   CfParams_preset - and a NEGATIVE CONTROL showing the premise is not trivially true there:
   (1) the wild-budget room premises `wild_room (as_universe B) SET k (st_depot S)` of the wild texts, in each
       text's own (SET, k): [] / prh_wk F (parse_noting, check_no_overread, check_reject_clean_starved,
       round_trip_text, check_round_trip), [] / length (prhtx_evs 0 0 ks) (the four tx texts), and the cursor set
       CW / 0 (pj_parse, parse_value, parse_items, parse_string), with CW of the form prh_cw_pj asks; and the
       budgets `wbudget SET k WS` of the budgeted posts;
   (2) the state-free inU clause of prhtx_trace (PRH_FnTx.v:199), for EVERY chain;
   (3) fuzz_free's `admits (as_universe B) (call_trace ..) S` (PRH_FnAlloc.v:334), at a fixed and a cursor trace;
   (4) the cnt <> fail guarded byte premises of tpj_string (PRH_FnPj.v:1256) and tfuzz_strdup (PRH_FnAlloc.v:518);
   (5) the count premises of tcheck_as_written_specX (PRH_FnCheck.v:857-858);
   (6) the outcome conjunct of tfuzz_malloc / tfuzz_strdup's posts (PRH_FnAlloc.v:300-307, :536-544): its run
       hypotheses are SATISFIABLE together at a real run position, so the conjunct is not vacuous. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YM05 YG00 YG01 YG0f YG0d YGcfNames YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild YGcfRoom YGcfFrees YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YCej YG0n YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Img CfImgA AD2l ACej CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRun PresetReqAt
  PresetLiveBounds PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes TxModel.
Import ListNotations.
Local Open Scope Z_scope.

(* ================================================================ image-free *)
Lemma wr_init : forall U set k, (length set + k <= u_wmax U)%nat -> YCbqGwild.wild_room U set k (st_depot init_state).
Proof. intros U set k H. apply YCbqGwild.wild_room_of_count. rewrite YCbqGwild.init_depot_nil. exact H. Qed.
(* CONTROL (1): a room premise with more slots than the universe leaves is FALSE at EVERY depot *)
Lemma wr_ctl : forall U set k d, (u_wmax U < k)%nat -> ~ YCbqGwild.wild_room U set k d.
Proof. intros U set k d H (b & _ & Hb). lia. Qed.
Lemma wb_nil : forall set k, YCbqGwild.wbudget set k [].
Proof. intros set k. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn [filter length]. lia. Qed.
Lemma wb_one : forall tr, YCbqGwild.wbudget [tr] 0 [tr].
Proof.
  intros tr. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn [filter].
  assert (E : mem_trace tr [tr] = true) by (apply mem_trace_In; left; reflexivity). rewrite E. cbn. lia.
Qed.
(* CONTROL (1, posts): a budget of 0 outside SET is FALSE for a store of one trace outside SET *)
Lemma wb_ctl : ~ YCbqGwild.wbudget [] 0 [[1]].
Proof. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia. Qed.

Lemma prh_wk_le : forall F, (prh_wk F <= 66)%nat.
Proof. intros F. destruct F; cbn; lia. Qed.

Lemma trace_cut : forall pc0 r w, r <> pc0 ->
  prh_trace pc0 r [w] = [pc0; r] ++ (if w =? pc0 then [] else [w]).
Proof.
  intros pc0 r w Hr. unfold prh_trace. cbn [flat_map].
  destruct (r =? pc0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  destruct (w =? pc0); reflexivity.
Qed.
Lemma inU_prefix : forall U p sfx, In p (u_wild U) -> (length (p ++ sfx) <= kUnwindMax)%nat -> inU U (p ++ sfx).
Proof. intros U p sfx Hp Hl. split; [exact Hl | right; exists p, sfx; split; [exact Hp | reflexivity]]. Qed.
Lemma inU_cursor : forall U pc0 r w, r <> pc0 -> In [pc0; r] (u_wild U) -> inU U (prh_trace pc0 r [w]).
Proof.
  intros U pc0 r w Hr Hp. rewrite (trace_cut pc0 r w Hr). apply inU_prefix; [exact Hp|].
  destruct (w =? pc0); cbn [app length]; unfold kUnwindMax; lia.
Qed.
(* (2) the realloc chain trace: [pc0; r] then any chain, cut at kUnwindMax *)
Lemma inU_chain : forall U pc0 r t s ch, r <> pc0 -> In [pc0; r] (u_wild U) ->
  inU U (unwind_of_chain pc0 ((t, r, s) :: ch)).
Proof.
  intros U pc0 r t s ch Hr Hp. unfold unwind_of_chain. cbn [flat_map].
  destruct (r =? pc0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  split; [apply firstn_le_length|]. right.
  exists [pc0; r], (firstn 28 (flat_map (fun r0 => match r0 with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch)).
  split; [exact Hp | unfold kUnwindMax; reflexivity].
Qed.

(* (6) the outcome conjunct's run hypotheses, at a real run position: the bytes {"a":1}, one harness call with all
   three P1 readings granted, the reader's own strtod, position 0 (check_no_overread's first copy, HMal (7 + 16)),
   at the start state's room. Image-independent: it holds at every CfImg / CfParams. *)
Definition isalloc (e : PresetReqAt.hev) : bool :=
  match e with PresetReqAt.HMal _ | PresetReqAt.HRe _ _ => true | _ => false end.
Definition cons_fromb sm x os (i k : nat) : bool :=
  forallb (fun j => match nth_error (PresetRun.hruns sm x os) (i + j) with
                    | Some e => if isalloc e then nth (i + j) (PresetRun.hcons sm x os) false else true
                    | None => true end) (seq 0 k).
Lemma cons_fromb_ok : forall sm x os i k, cons_fromb sm x os i k = true -> prh_cons_from sm x os i k.
Proof.
  unfold cons_fromb, prh_cons_from. intros sm x os i k H j e Hj He.
  rewrite forallb_forall in H. specialize (H j (proj2 (in_seq k 0 j) (conj (Nat.le_0_l j) Hj))).
  rewrite He in H. destruct e; cbn in H |- *; auto.
Qed.
Definition sm6 : list Z -> Z * Z := ReaderRes.jr_strtod.
Definition x6 : list Z := [123; 34; 97; 34; 58; 49; 125].
Definition os6 : list (option nat * option nat * option nat) := [(None, None, None)].
Section outcome. Context {ci : CfImg} {cp : CfParams}.
Theorem outcome_hyps_sat :
  PresetRoomPos.iface_room_pos sm6 x6 os6 0 [] [] init_state /\
  prh_run_at sm6 x6 os6 0 [PresetReqAt.HMal (7 + 16)] /\
  prh_cons_from sm6 x6 os6 0 (length [PresetReqAt.HMal (7 + 16)]).
Proof.
  split; [|split].
  - unfold PresetRoomPos.iface_room_pos. rewrite firstn_O. split; [|split; [|split; [|split; [|split]]]].
    + exists (PresetRoom.rs_live (YGcfRoom.room_of_cf init_state)). split.
      * apply Nat.leb_le. vm_compute. reflexivity.
      * cbn [app]. change (PresetReqAt.hlive []) with (@nil Z). apply Permutation_refl.
    + exact YGcfRoom.room_inv_cf_init.
    + exact YGcfRoom.quar_fifo_cf_init.
    + constructor.
    + reflexivity.
    (* Part 4's COUNT clause (A16, PresetRoomPos.v rp_count): at the start state, no secondary *)
    + exact (PresetRoomPos.rp_count_start init_state eq_refl).
  - vm_compute. reflexivity.
  - apply cons_fromb_ok. vm_compute. reflexivity.
Qed.
End outcome.
(* CONTROL (6): at check_no_overread's first READING (position 3, where the model may refuse) the consumer premise
   is FALSE, so the conjunct's hypotheses are not trivially true *)
Lemma outcome_ctl : ~ prh_cons_from sm6 x6 os6 3 1.
Proof.
  intro H. unfold prh_cons_from in H.
  let eo := eval vm_compute in (nth_error (PresetRun.hruns sm6 x6 os6) (3 + 0)) in
  match eo with Some ?e => specialize (H 0%nat e ltac:(lia) ltac:(vm_compute; reflexivity)) end.
  revert H. vm_compute. discriminate.
Qed.

(* (4) at the start state no harness byte is live *)
Lemma bb_init : blocks_bytes init_state = 0.
Proof. reflexivity. Qed.
Lemma head16 : @cf_head CfParamsPreset.CfParams_preset = 16.
Proof. reflexivity. Qed.
Theorem pjstring_bytes_sat : forall len, 0 <= len <= 2 ^ 33 ->
  blocks_bytes init_state + @PRH_FnPj.LIVE_pj_string CfParamsPreset.CfParams_preset len <= LIVE_MAX.
Proof. intros len H. rewrite bb_init. unfold PRH_FnPj.LIVE_pj_string, LIVE_MAX. rewrite head16. lia. Qed.
Theorem pjstring_bytes_ctl :
  ~ (blocks_bytes init_state + @PRH_FnPj.LIVE_pj_string CfParamsPreset.CfParams_preset (2 ^ 34) <= LIVE_MAX).
Proof. rewrite bb_init. unfold PRH_FnPj.LIVE_pj_string, LIVE_MAX. rewrite head16. lia. Qed.
Theorem strdup_bytes_sat : forall cs : list Z, (length cs <= 2 ^ 20)%nat ->
  blocks_bytes init_state + (Z.of_nat (length cs) + 1 + @cf_head CfParamsPreset.CfParams_preset) <= LIVE_MAX.
Proof. intros cs H. rewrite bb_init, head16. unfold LIVE_MAX. apply Nat2Z.inj_le in H. rewrite Nat2Z.inj_pow in H. lia. Qed.
Theorem strdup_bytes_ctl : forall cs : list Z, (length cs = 2 ^ 34)%nat ->
  ~ (blocks_bytes init_state + (Z.of_nat (length cs) + 1 + @cf_head CfParamsPreset.CfParams_preset) <= LIVE_MAX).
Proof. intros cs H. rewrite bb_init, head16, H. unfold LIVE_MAX. rewrite Nat2Z.inj_pow. cbn. lia. Qed.

(* ================================================================ image A' *)
Definition TA : asyms := AD2l.TfibB.
Lemma uA : as_universe TA = ACej.Tfib_universe.
Proof. reflexivity. Qed.
Lemma wmaxA : u_wmax (as_universe TA) = 3920%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma pcfA : pc_free_ra0 (as_code TA) = 0x53878.
Proof. vm_compute. reflexivity. Qed.

(* (1) the five SET = [] texts, at k = prh_wk F *)
Theorem room_wk_A : forall F, YCbqGwild.wild_room (as_universe TA) [] (prh_wk F) (st_depot init_state).
Proof. intros F. apply wr_init. rewrite wmaxA. pose proof (prh_wk_le F). cbn [length]. lia. Qed.
Theorem room_ctl_A : forall set d, ~ YCbqGwild.wild_room (as_universe TA) set 3921 d.
Proof. intros set d. apply wr_ctl. rewrite wmaxA. lia. Qed.
(* (1) the four tx texts, at k = length (prhtx_evs 0 0 ks), ks the texts' pieces (>= 0, total + 1 <= 2 ^ 28) *)
Theorem room_tx_A : forall ks, Forall (fun k => 0 <= k) ks -> TxModel.zsum ks + 1 <= 2 ^ 28 ->
  YCbqGwild.wild_room (as_universe TA) [] (length (PRH_FnTx.prhtx_evs 0 0 ks)) (st_depot init_state).
Proof.
  intros ks H1 H2. apply wr_init. rewrite wmaxA. pose proof (PRH_FnTx.prhtx_evs_le_30 ks H1 H2). cbn [length]. lia.
Qed.
(* (1) the cursor texts: CW = the two cursor frees' traces at the cursor's end word w = t0 + len *)
Definition CWA (w : Z) : list (list Z) := [prh_trace 0x53878 0x87e50 [w]; prh_trace 0x53878 0x87764 [w]].
Theorem room_cw_A : forall w, YCbqGwild.wild_room (as_universe TA) (CWA w) 0 (st_depot init_state).
Proof. intros w. apply wr_init. rewrite wmaxA. cbn [length CWA]. lia. Qed.
Lemma cw_arm_A : forall w F r, prh_cursor F -> In r (@prh_free_sites PRH_Img.prh_img_A F) ->
  In (prh_trace (pc_free_ra0 (as_code TA)) r [w]) (CWA w).
Proof.
  intros w F r [-> | ->] Hr; rewrite pcfA; vm_compute in Hr.
  - destruct Hr as [<- | []]. left. reflexivity.
  - destruct Hr as [<- | []]. right. left. reflexivity.
Qed.
(* prh_cw_pj AFTER ITS REPAIR (i) (PRH_Base.v blob d6679ece5a34: each cursor arm keeps only its FIRST
   disjunct): parse_items' trace at the cursor's end t0 + len, parse_string's at the SLOT WORD rdword reads at
   spZ regs - pi_frame F_pj_parse. The earlier A' witness (both cursors at the code word 0x85e6c, through the dropped
   second disjuncts) no longer meets the text, so A' takes B''s shape (the kit owner's measured replacement): CWA2 (t0 + len) w0,
   the witness stated for the value read, never a chosen one. CWA (t0 + len) above, the cursor's end for BOTH, is the
   CW the text rejects: cw_pj_A_ctl below. *)
Definition CWA2 (w1 w0 : Z) : list (list Z) := [prh_trace 0x53878 0x87764 [w1]; prh_trace 0x53878 0x87e50 [w0]].
Lemma rets_A : @pi_call_rets PRH_Img.prh_img_A F_pj_parse F_parse_value = [0x85e6c].
Proof. vm_compute. reflexivity. Qed.
Lemma sites_items_A : @prh_free_sites PRH_Img.prh_img_A F_parse_items = [0x87764].
Proof. vm_compute. reflexivity. Qed.
Lemma sites_string_A : @prh_free_sites PRH_Img.prh_img_A F_parse_string = [0x87e50].
Proof. vm_compute. reflexivity. Qed.
Section cwA. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {L : ptable asym} {PA : PAImg L}.
Theorem cw_pj_A : forall W mem regs t0 len w0,
  rdword (YG0n.aview pa_segs (YA0n.w_H W) mem) (spZ regs - @pi_frame PRH_Img.prh_img_A F_pj_parse) = Some w0 ->
  prh_cw_pj (PI := PRH_Img.prh_img_A) TA (CWA2 (t0 + len) w0) W mem regs t0 len.
Proof.
  intros W mem regs t0 len w0 Hrd. unfold prh_cw_pj. rewrite pcfA. split.
  - intros r Hr. rewrite sites_items_A in Hr. destruct Hr as [<- | []]. left. reflexivity.
  - intros r Hr. rewrite sites_string_A in Hr. destruct Hr as [<- | []].
    intros w0' Hrd'. rewrite Hrd in Hrd'. injection Hrd' as <-. right. left. reflexivity.
Qed.
(* CONTROL: arm 1 for both cursors (CWA (t0 + len)) FAILS the pin wherever the slot word read is another word *)
Theorem cw_pj_A_ctl : forall W mem regs t0 len w0,
  rdword (YG0n.aview pa_segs (YA0n.w_H W) mem) (spZ regs - @pi_frame PRH_Img.prh_img_A F_pj_parse) = Some w0 ->
  w0 <> t0 + len -> t0 + len <> 0x85e6c -> w0 <> 0x53878 -> t0 + len <> 0x53878 ->
  ~ prh_cw_pj (PI := PRH_Img.prh_img_A) TA (CWA (t0 + len)) W mem regs t0 len.
Proof.
  intros W mem regs t0 len w0 Hrd H1 H2 H3 H4 Hp. unfold prh_cw_pj in Hp. destruct Hp as [_ Hs]. rewrite pcfA in Hs.
  pose proof (Hs 0x87e50 ltac:(rewrite sites_string_A; left; reflexivity)) as H.
  specialize (H w0 Hrd). unfold CWA in H. rewrite !trace_cut in H by lia.
  rewrite (proj2 (Z.eqb_neq w0 0x53878) H3), (proj2 (Z.eqb_neq (t0 + len) 0x53878) H4) in H.
  destruct H as [E | [E | []]]; injection E; intros; lia.
Qed.
End cwA.
(* (2) prhtx_trace's clause: every chain from tx_put's realloc site is inU *)
Lemma txsite_A : @cf_pc_realloc_ra0 CfImgA.CfImg_A = 0x53c74 /\ @pi_ret_tx_realloc PRH_Img.prh_img_A = 0x84db0.
Proof. split; vm_compute; reflexivity. Qed.
Theorem tx_chain_inU_A : forall t ch,
  inU (as_universe TA) (unwind_of_chain (@cf_pc_realloc_ra0 CfImgA.CfImg_A)
    ((t, @pi_ret_tx_realloc PRH_Img.prh_img_A, t) :: ch)).
Proof.
  intros t ch. destruct txsite_A as [E1 E2]. rewrite E1, E2.
  apply inU_chain; [lia | vm_compute; repeat first [left; reflexivity | right]].
Qed.
(* CONTROL (2): the OLD `In _ (as_universe B)` (= the fixed list) is FALSE for a chain with one data word *)
Theorem tx_chain_old_ctl_A :
  ~ In (unwind_of_chain 0x53c74 ((0, 0x84db0, 0) :: [(0, 0x7fe1e7ff0017, 0)])) (u_fix (as_universe TA)).
Proof. intro H. apply mem_trace_In in H. vm_compute in H. discriminate H. Qed.
(* (3) fuzz_free's admits: a cursor free's trace at every word, and a fixed trace *)
Theorem admits_cursor_A : forall w, admits (as_universe TA) (prh_trace 0x53878 0x87e50 [w]) init_state.
Proof.
  intros w. split.
  - apply inU_cursor; [lia | vm_compute; repeat first [left; reflexivity | right]].
  - right. right. rewrite YCbqGwild.init_depot_nil, wmaxA. cbn. lia.
Qed.
Theorem admits_fixed_A : admits (as_universe TA) [0x53878] init_state.
Proof. apply admits_fix; [exact ACej.Tfib_universe_ok | apply mem_trace_In; vm_compute; reflexivity]. Qed.
(* CONTROL (3): a trace neither fixed nor under a wild prefix is NOT admitted *)
Theorem admits_ctl_A : ~ admits (as_universe TA) [0x53878; 1] init_state.
Proof.
  intros [[_ [Hf | (p & sfx & Hp & E)]] _].
  - apply mem_trace_In in Hf. vm_compute in Hf. discriminate Hf.
  - vm_compute in Hp. repeat (destruct Hp as [<- | Hp]; [cbn in E; congruence |]). destruct Hp.
Qed.
(* (5) tcheck_as_written's counts at the start state *)
Theorem counts_A :
  YGcfRoomLive.sec_cnt init_state
    <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 init_state <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ================================================================ image B' *)
Definition TB : asyms := YD2l.TfibB.
Lemma uB : as_universe TB = YCej.Tfib_universe.
Proof. reflexivity. Qed.
Lemma wmaxB : u_wmax (as_universe TB) = 3926%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma pcfB : pc_free_ra0 (as_code TB) = 0x53964.
Proof. vm_compute. reflexivity. Qed.
Theorem room_wk_B : forall F, YCbqGwild.wild_room (as_universe TB) [] (prh_wk F) (st_depot init_state).
Proof. intros F. apply wr_init. rewrite wmaxB. pose proof (prh_wk_le F). cbn [length]. lia. Qed.
Theorem room_ctl_B : forall set d, ~ YCbqGwild.wild_room (as_universe TB) set 3927 d.
Proof. intros set d. apply wr_ctl. rewrite wmaxB. lia. Qed.
Theorem room_tx_B : forall ks, Forall (fun k => 0 <= k) ks -> TxModel.zsum ks + 1 <= 2 ^ 28 ->
  YCbqGwild.wild_room (as_universe TB) [] (length (PRH_FnTx.prhtx_evs 0 0 ks)) (st_depot init_state).
Proof.
  intros ks H1 H2. apply wr_init. rewrite wmaxB. pose proof (PRH_FnTx.prhtx_evs_le_30 ks H1 H2). cbn [length]. lia.
Qed.
Definition CWB (w : Z) : list (list Z) := [prh_trace 0x53964 0x885e4 [w]; prh_trace 0x53964 0x87f34 [w]].
Theorem room_cw_B : forall w, YCbqGwild.wild_room (as_universe TB) (CWB w) 0 (st_depot init_state).
Proof. intros w. apply wr_init. rewrite wmaxB. cbn [length CWB]. lia. Qed.
Lemma cw_arm_B : forall w F r, prh_cursor F -> In r (@prh_free_sites PRH_ImgB.prh_img_B F) ->
  In (prh_trace (pc_free_ra0 (as_code TB)) r [w]) (CWB w).
Proof.
  intros w F r [-> | ->] Hr; rewrite pcfB; vm_compute in Hr.
  - destruct Hr as [<- | []]. left. reflexivity.
  - destruct Hr as [<- | []]. right. left. reflexivity.
Qed.
(* THE PINNED prh_cw_pj on B': parse_items at arm 1 (its trace 0x87f34 at the cursor's end t0 + len), parse_string at
   arm 2 (its trace 0x885e4 at w0, the SLOT WORD that rdword reads at spZ regs - pi_frame F_pj_parse; the witness is
   stated for the value read, never a chosen one). CWB (t0 + len) above, arm 1 for BOTH, is the CW the pin rejects. *)
Definition CWB2 (w1 w0 : Z) : list (list Z) := [prh_trace 0x53964 0x87f34 [w1]; prh_trace 0x53964 0x885e4 [w0]].
Lemma rets_B : @pi_call_rets PRH_ImgB.prh_img_B F_pj_parse F_parse_value = [0x8633c].
Proof. vm_compute. reflexivity. Qed.
Lemma sites_items_B : @prh_free_sites PRH_ImgB.prh_img_B F_parse_items = [0x87f34].
Proof. vm_compute. reflexivity. Qed.
Lemma sites_string_B : @prh_free_sites PRH_ImgB.prh_img_B F_parse_string = [0x885e4].
Proof. vm_compute. reflexivity. Qed.
Section cwB. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {L : ptable asym} {PA : PAImg L}.
Theorem cw_pj_B : forall W mem regs t0 len w0,
  rdword (YG0n.aview pa_segs (YA0n.w_H W) mem) (spZ regs - @pi_frame PRH_ImgB.prh_img_B F_pj_parse) = Some w0 ->
  prh_cw_pj (PI := PRH_ImgB.prh_img_B) TB (CWB2 (t0 + len) w0) W mem regs t0 len.
Proof.
  intros W mem regs t0 len w0 Hrd. unfold prh_cw_pj. rewrite pcfB. split.
  - intros r Hr. rewrite sites_items_B in Hr. destruct Hr as [<- | []]. left. reflexivity.
  - intros r Hr. rewrite sites_string_B in Hr. destruct Hr as [<- | []].
    intros w0' Hrd'. rewrite Hrd in Hrd'. injection Hrd' as <-. right. left. reflexivity.
Qed.
(* CONTROL: arm 1 for both cursors (CWB (t0 + len)) FAILS the pin wherever the slot word read is another word *)
Theorem cw_pj_B_ctl : forall W mem regs t0 len w0,
  rdword (YG0n.aview pa_segs (YA0n.w_H W) mem) (spZ regs - @pi_frame PRH_ImgB.prh_img_B F_pj_parse) = Some w0 ->
  w0 <> t0 + len -> t0 + len <> 0x8633c -> w0 <> 0x53964 -> t0 + len <> 0x53964 ->
  ~ prh_cw_pj (PI := PRH_ImgB.prh_img_B) TB (CWB (t0 + len)) W mem regs t0 len.
Proof.
  intros W mem regs t0 len w0 Hrd H1 H2 H3 H4 Hp. unfold prh_cw_pj in Hp. destruct Hp as [_ Hs]. rewrite pcfB in Hs.
  pose proof (Hs 0x885e4 ltac:(rewrite sites_string_B; left; reflexivity)) as H.
  specialize (H w0 Hrd). unfold CWB in H. rewrite !trace_cut in H by lia.
  rewrite (proj2 (Z.eqb_neq w0 0x53964) H3), (proj2 (Z.eqb_neq (t0 + len) 0x53964) H4) in H.
  destruct H as [E | [E | []]]; injection E; intros; lia.
Qed.
End cwB.
Lemma txsite_B : @cf_pc_realloc_ra0 CfImgB.CfImg_B = 0x53d60 /\ @pi_ret_tx_realloc PRH_ImgB.prh_img_B = 0x8529c.
Proof. split; vm_compute; reflexivity. Qed.
Theorem tx_chain_inU_B : forall t ch,
  inU (as_universe TB) (unwind_of_chain (@cf_pc_realloc_ra0 CfImgB.CfImg_B)
    ((t, @pi_ret_tx_realloc PRH_ImgB.prh_img_B, t) :: ch)).
Proof.
  intros t ch. destruct txsite_B as [E1 E2]. rewrite E1, E2.
  apply inU_chain; [lia | vm_compute; repeat first [left; reflexivity | right]].
Qed.
Theorem tx_chain_old_ctl_B :
  ~ In (unwind_of_chain 0x53d60 ((0, 0x8529c, 0) :: [(0, 0x7fe1e7ff0017, 0)])) (u_fix (as_universe TB)).
Proof. intro H. apply mem_trace_In in H. vm_compute in H. discriminate H. Qed.
Theorem admits_cursor_B : forall w, admits (as_universe TB) (prh_trace 0x53964 0x885e4 [w]) init_state.
Proof.
  intros w. split.
  - apply inU_cursor; [lia | vm_compute; repeat first [left; reflexivity | right]].
  - right. right. rewrite YCbqGwild.init_depot_nil, wmaxB. cbn. lia.
Qed.
Theorem admits_fixed_B : admits (as_universe TB) [0x53964] init_state.
Proof. apply admits_fix; [exact YCej.Tfib_universe_ok | apply mem_trace_In; vm_compute; reflexivity]. Qed.
Theorem admits_ctl_B : ~ admits (as_universe TB) [0x53964; 1] init_state.
Proof.
  intros [[_ [Hf | (p & sfx & Hp & E)]] _].
  - apply mem_trace_In in Hf. vm_compute in Hf. discriminate Hf.
  - vm_compute in Hp. repeat (destruct Hp as [<- | Hp]; [cbn in E; congruence |]). destruct Hp.
Qed.
Theorem counts_B :
  YGcfRoomLive.sec_cnt init_state
    <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  YGcfRoomLive.ccnt24 init_state <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ================================================================ option (b) of the unit owner's 00:31Z ruling:
   the cursor texts' parameter CW = YCbqGwild.cw_of Tfib_wild w1 w2 (nth 0 = parse_items' free, nth 1 =
   parse_string's), entry premise wild_room (as_universe B) CW 0 (st_depot S) and "every cursor free trace is in CW" *)
Theorem room_cwof_A : forall w1 w2,
  YCbqGwild.wild_room (as_universe TA) (YCbqGwild.cw_of (u_wild (as_universe TA)) w1 w2) 0 (st_depot init_state).
Proof. intros w1 w2. apply YCbqGwild.wild_room_cw_init. rewrite YCbqGwild.cw_of_length, wmaxA. lia. Qed.
Theorem cwof_cursor_A : forall w1 w2, w1 <> 0x53878 -> w2 <> 0x53878 ->
  In (prh_trace 0x53878 0x87764 [w1]) (YCbqGwild.cw_of (u_wild (as_universe TA)) w1 w2) /\
  In (prh_trace 0x53878 0x87e50 [w2]) (YCbqGwild.cw_of (u_wild (as_universe TA)) w1 w2).
Proof.
  intros w1 w2 H1 H2. rewrite !trace_cut by lia.
  rewrite (proj2 (Z.eqb_neq w1 0x53878) H1), (proj2 (Z.eqb_neq w2 0x53878) H2).
  split; [left | right; left]; reflexivity.
Qed.
(* CONTROL: the membership premise is not trivially true - a cursor trace at another word is NOT in CW *)
Theorem cwof_ctl_A : ~ In (prh_trace 0x53878 0x87764 [1]) (YCbqGwild.cw_of (u_wild (as_universe TA)) 2 2).
Proof. vm_compute. intros [H | [H | []]]; discriminate H. Qed.
Theorem room_cwof_B : forall w1 w2,
  YCbqGwild.wild_room (as_universe TB) (YCbqGwild.cw_of (u_wild (as_universe TB)) w1 w2) 0 (st_depot init_state).
Proof. intros w1 w2. apply YCbqGwild.wild_room_cw_init. rewrite YCbqGwild.cw_of_length, wmaxB. lia. Qed.
Theorem cwof_cursor_B : forall w1 w2, w1 <> 0x53964 -> w2 <> 0x53964 ->
  In (prh_trace 0x53964 0x87f34 [w1]) (YCbqGwild.cw_of (u_wild (as_universe TB)) w1 w2) /\
  In (prh_trace 0x53964 0x885e4 [w2]) (YCbqGwild.cw_of (u_wild (as_universe TB)) w1 w2).
Proof.
  intros w1 w2 H1 H2. rewrite !trace_cut by lia.
  rewrite (proj2 (Z.eqb_neq w1 0x53964) H1), (proj2 (Z.eqb_neq w2 0x53964) H2).
  split; [left | right; left]; reflexivity.
Qed.
Theorem cwof_ctl_B : ~ In (prh_trace 0x53964 0x87f34 [1]) (YCbqGwild.cw_of (u_wild (as_universe TB)) 2 2).
Proof. vm_compute. intros [H | [H | []]]; discriminate H. Qed.
Print Assumptions room_cwof_A. Print Assumptions cwof_cursor_A. Print Assumptions cwof_ctl_A.
Print Assumptions room_cwof_B. Print Assumptions cwof_cursor_B. Print Assumptions cwof_ctl_B.

Print Assumptions cw_pj_A_ctl. Print Assumptions cw_pj_B_ctl.
Print Assumptions room_wk_A. Print Assumptions room_tx_A. Print Assumptions room_cw_A. Print Assumptions cw_pj_A.
Print Assumptions tx_chain_inU_A. Print Assumptions admits_cursor_A. Print Assumptions admits_fixed_A.
Print Assumptions room_wk_B. Print Assumptions room_tx_B. Print Assumptions room_cw_B. Print Assumptions cw_pj_B.
Print Assumptions tx_chain_inU_B. Print Assumptions admits_cursor_B. Print Assumptions admits_fixed_B.
Print Assumptions outcome_hyps_sat. Print Assumptions pjstring_bytes_sat. Print Assumptions strdup_bytes_sat.
Print Assumptions counts_A. Print Assumptions counts_B.
Print Assumptions room_ctl_A. Print Assumptions tx_chain_old_ctl_A. Print Assumptions admits_ctl_A.
Print Assumptions outcome_ctl. Print Assumptions pjstring_bytes_ctl. Print Assumptions wb_ctl.
