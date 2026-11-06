From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep ListRep CheckRep drain_b_c relay_remove_b_c SlotInv SlotReads check_shape_done_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dc_live : forall gn cl br dd TOT, (gn = 0 \/ gn = 1) ->
  (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  send_live cl br dd TOT = (gn =? 0) && negb (TOT =? 0).
Proof.
  intros gn cl br dd TOT [-> | ->] H0 H1.
  - destruct (H0 eq_refl) as (-> & -> & ->). unfold send_live, send_off. cbn.
    destruct (TOT =? 0); reflexivity.
  - destruct (H1 eq_refl) as [-> | [-> | ->]]; unfold send_live, send_off; cbn;
      rewrite ?orb_true_r, ?andb_false_r; reflexivity.
Qed.

Lemma with_nul_nil : forall Ls, Z.of_nat (length (with_nul Ls)) = 0 -> Ls = [].
Proof.
  intros [|l Ls] H; [reflexivity|]. pose proof (lines_count (l :: Ls)) as C. cbn [length] in C. lia.
Qed.

Lemma dc_live_nil : forall gn cl br dd Ls, (gn = 0 \/ gn = 1) ->
  (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  gn = 0 -> send_live cl br dd (Z.of_nat (length (with_nul Ls))) = false -> Ls = [].
Proof.
  intros gn cl br dd Ls G0 G1 G2 Hg L. rewrite (dc_live gn cl br dd _ G0 G1 G2) in L. subst gn.
  rewrite Z.eqb_refl, andb_true_l, negb_false_iff, Z.eqb_eq in L. apply with_nul_nil. exact L.
Qed.

Lemma dc_lines_range : forall h, Forall zrange (lines (hs_state h) (bzs (pending_stream h))).
Proof.
  intros h. exact (proj1 (lines_range (bzs (pending_stream h)) (hs_state h) (zrange_bzs (hs_W h)) (zrange_bzs _))).
Qed.

Lemma dc_bstream : forall (E E' : hlist) Ls LB, hl_recs E = [] ->
  map snd (hl_recs E') = map snd (hl_recs E) ++ map (map (Z_to_bv 8)) Ls ->
  Forall zrange Ls -> bzs LB = with_nul Ls -> bstream E' = LB.
Proof.
  intros E E' Ls LB HE HM HR HB. rewrite HE in HM. cbn [map app] in HM.
  apply bzs_inj. rewrite HB. exact (bstream_bzs E' Ls HM HR).
Qed.

Lemma dc_stream : forall gn cl br dd (live : bool) (E E' : hlist) Ls LB, (gn = 0 \/ gn = 1) ->
  (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (with_nul Ls))) ->
  hl_recs E = [] -> map snd (hl_recs E') = map snd (hl_recs E) ++ map (map (Z_to_bv 8)) Ls ->
  Forall zrange Ls -> bzs LB = with_nul Ls ->
  gn = 0 -> exists rest, skipn (Z.to_nat 0) (if live then LB else []) = bstream E' ++ rest.
Proof.
  intros gn cl br dd live E E' Ls LB G0 G1 G2 HL HE HM HR HB Hg.
  rewrite (dc_bstream E E' Ls LB HE HM HR HB). exists []. rewrite app_nil_r.
  destruct live; [reflexivity|].
  rewrite (dc_live_nil gn cl br dd Ls G0 G1 G2 Hg (eq_sym HL)) in HB.
  destruct LB as [|b LB]; [reflexivity|]. cbn in HB. discriminate HB.
Qed.

Lemma dc_nout : forall gn cl br dd (live : bool) (E E' : hlist) Ls LB NO, (gn = 0 \/ gn = 1) ->
  (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (with_nul Ls))) ->
  hl_recs E = [] -> map snd (hl_recs E') = map snd (hl_recs E) ++ map (map (Z_to_bv 8)) Ls ->
  Forall zrange Ls -> bzs LB = with_nul Ls -> NO = 0 ->
  (if live then NO + Z.of_nat (length (with_nul Ls)) else NO) =
  (if gn =? 0 then Z.of_nat (length (bstream E')) else 0).
Proof.
  intros gn cl br dd live E E' Ls LB NO G0 G1 G2 HL HE HM HR HB ->.
  rewrite (dc_bstream E E' Ls LB HE HM HR HB), HL, (dc_live gn cl br dd _ G0 G1 G2).
  assert (LL : length LB = length (with_nul Ls)) by (rewrite <- HB, bzs_length; reflexivity).
  rewrite LL. destruct G0 as [-> | ->]; [|reflexivity].
  rewrite Z.eqb_refl, andb_true_l. destruct (Z.of_nat (length (with_nul Ls)) =? 0) eqn:T; cbn [negb].
  - apply Z.eqb_eq in T. lia.
  - lia.
Qed.

Lemma if_word : forall (b : bool) (w : word) z,
  (if b then Z_to_bv 64 z else w) = Z_to_bv 64 (if b then z else bv_unsigned w).
Proof. intros [|] w z; [reflexivity | symmetry; apply Z_to_bv_bv_unsigned]. Qed.

Lemma dc_nout_w : forall gn cl br dd (live : bool) (E E' : hlist) Ls LB (nout : word), (gn = 0 \/ gn = 1) ->
  (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (with_nul Ls))) ->
  hl_recs E = [] -> map snd (hl_recs E') = map snd (hl_recs E) ++ map (map (Z_to_bv 8)) Ls ->
  Forall zrange Ls -> bzs LB = with_nul Ls -> bv_unsigned nout = 0 ->
  (if live then Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (with_nul Ls))) else nout) =
  Z_to_bv 64 (if gn =? 0 then 0 + Z.of_nat (length (bstream E')) else 0).
Proof.
  intros gn cl br dd live E E' Ls LB nout G0 G1 G2 HL HE HM HR HB HN.
  rewrite if_word. f_equal.
  rewrite (dc_nout gn cl br dd live E E' Ls LB (bv_unsigned nout) G0 G1 G2 HL HE HM HR HB HN).
  destruct (gn =? 0); lia.
Qed.

Lemma with_nul_bzs : forall Ls (LB : list byte), bzs LB = with_nul Ls ->
  Z.of_nat (length LB) = Z.of_nat (length (with_nul Ls)).
Proof. intros Ls LB HB. rewrite <- HB, bzs_length. reflexivity. Qed.

Lemma nodup_out_src : forall G OUT' (bs hs : list Z), NoDup (G :: OUT' :: bs ++ hs) -> ~ In OUT' hs.
Proof.
  intros G OUT' bs hs ND X. apply NoDup_ListNoDup in ND.
  inversion ND as [|? ? _ N1]; subst. inversion N1 as [|? ? N2 _]; subst.
  apply N2. apply in_app_iff. right. exact X.
Qed.

Lemma nodup_keys_texts : forall ks, NoDup (map key_text ks) -> NoDup (keys_texts ks).
Proof.
  intros ks H. apply NoDup_ListNoDup in H. apply NoDup_ListNoDup. unfold keys_texts.
  induction ks as [|k ks IH]; cbn [map] in *; [constructor|].
  inversion H as [|? ? H1 H2]; subst. constructor; [|exact (IH H2)].
  intros Hin. apply H1. apply in_map_iff in Hin. destruct Hin as (k' & E & Hk').
  apply bzs_inj in E. rewrite <- E. apply in_map. exact Hk'.
Qed.

Section DC.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.

Lemma fresh_unsigned : forall a n, fresh_block Bm a n -> 0 <= n -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a n (F1 & F2 & _) Hn. pose proof (@YM05.alloc_ceiling_lt rc) as AC. apply unsigned_lit. lia.
Qed.

Lemma dc_no_loss : forall gn cl br dd (live : bool) (h h' : hsrc) (e' : rentry) Ls (LB : list byte)
    (nout out : word) (OUT' CAP' G : Z) L A,
  (gn = 0 \/ gn = 1) -> (gn = 0 -> cl = 3 /\ br = 0 /\ dd = 0) -> (gn = 1 -> cl = -1 \/ br = 1 \/ dd = 1) ->
  live = send_live cl br dd (Z.of_nat (length (with_nul Ls))) ->
  hl_recs (hs_expected h) = [] ->
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls ->
  Forall zrange Ls -> bzs LB = with_nul Ls -> bv_unsigned nout = 0 ->
  (live = false -> OUT' = bv_unsigned out) ->
  (live = true -> bv_unsigned nout + Z.of_nat (length (with_nul Ls)) <= CAP' /\ In (OUT', CAP') (blocks L A) /\
     fresh_block Bm OUT' CAP') ->
  NoDup (G :: OUT' :: entry_blocks e' ++ hs_blocks h') ->
  bv_unsigned (if live then Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (with_nul Ls))) else nout) =
    (if gn =? 0 then Z.of_nat (length (bstream (hs_expected h'))) else 0) /\
  bv_unsigned (if live then Z_to_bv 64 OUT' else out) = OUT' /\
  Z.of_nat (length (if live then LB else [])) =
    bv_unsigned (if live then Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (with_nul Ls))) else nout) /\
  ((if live then LB else []) = [] \/
   exists CO, bv_unsigned (if live then Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (with_nul Ls))) else nout)
       <= CO /\ In (bv_unsigned (if live then Z_to_bv 64 OUT' else out), CO) (blocks L A) /\
     fresh_block Bm (bv_unsigned (if live then Z_to_bv 64 OUT' else out)) CO /\
     ~ In (bv_unsigned (if live then Z_to_bv 64 OUT' else out)) (hs_blocks h')) /\
  0 <= 0 <= bv_unsigned (if live then Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (with_nul Ls))) else nout) /\
  (gn = 0 -> exists rest, skipn (Z.to_nat 0) (if live then LB else []) = bstream (hs_expected h') ++ rest).
Proof.
  intros gn cl br dd live h h' e' Ls LB nout out OUT' CAP' G L A G0 G1 G2 HL HE HM HR HB HN HNL HLV HND.
  pose proof (dc_nout gn cl br dd live (hs_expected h) (hs_expected h') Ls LB (bv_unsigned nout)
    G0 G1 G2 HL HE HM HR HB HN) as ZN.
  pose proof (dc_stream gn cl br dd live (hs_expected h) (hs_expected h') Ls LB G0 G1 G2 HL HE HM HR HB) as ST.
  pose proof (with_nul_bzs Ls LB HB) as LL.
  pose proof (nodup_out_src G OUT' (entry_blocks e') (hs_blocks h') HND) as NI.
  destruct live; cbv beta iota in ZN, ST |- *.
  - destruct (HLV eq_refl) as (C1 & C2 & C3).
    pose proof C3 as (F1 & F2 & _). pose proof (@YM05.alloc_ceiling_lt rc) as AC.
    assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned nout + Z.of_nat (length (with_nul Ls)))) =
                 bv_unsigned nout + Z.of_nat (length (with_nul Ls))) by (apply unsigned_lit; lia).
    rewrite U1, (fresh_unsigned OUT' CAP' C3 ltac:(lia)).
    split; [exact ZN|]. split; [reflexivity|]. split; [lia|].
    split; [right; exists CAP'; split; [exact C1|]; split; [exact C2|]; split; [exact C3 | exact NI]|].
    split; [lia | exact ST].
  - pose proof (HNL eq_refl) as HO.
    split; [exact ZN|]. split; [symmetry; exact HO|]. split; [cbn [length]; lia|].
    split; [left; reflexivity|]. split; [lia | exact ST].
Qed.

Lemma dc_O_nil : forall L A (mem : word -> option byte) (NO CAP OUT : Z) (O junk : list byte),
  ((CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
   (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
    bytes_at (ms_segs Bm) mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO)) ->
  NO = 0 -> O = [].
Proof.
  intros L A mem NO CAP OUT O junk [(_ & _ & _ & HO) | (_ & _ & _ & _ & _ & HO & _)] HN; [exact HO|].
  destruct O as [|b O]; [reflexivity|]. cbn [length] in HO. lia.
Qed.

Lemma dc_ob_bytes : forall (m : word -> option byte) (live : bool) (LB O junk' : list byte) (out : word) (OUT' : Z),
  (live = true -> bytes_at (ms_segs Bm) m OUT' (O ++ LB ++ junk')) -> O = [] ->
  (live = false -> OUT' = bv_unsigned out) ->
  bytes_at (ms_segs Bm) m OUT' (if live then LB else []).
Proof.
  intros m [|] LB O junk' out OUT' HB HO HNL.
  - specialize (HB eq_refl). rewrite HO in HB. cbn [app] in HB. apply bytes_at_app in HB. exact (proj1 HB).
  - rewrite (HNL eq_refl). apply bytes_at_nil. pose proof (u64_range out). lia.
Qed.

Lemma dc_cost : forall L A mem (es : list rentry) hj e p k n,
  Forall (entry_ok Bm L A mem) es -> In (e, p) (combine es hj) ->
  slot_cost es hj <= k -> k <= n -> n < INPUT_MAX -> pair_cost e p < 2 ^ 26.
Proof.
  intros L A mem es hj e p k n HF Hin Hc Hk Hn.
  assert (NN : Forall (fun e0 => 0 <= re_used e0) es).
  { apply Forall_forall. intros e0 He0. rewrite Forall_forall in HF.
    destruct (HF e0 He0) as (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia. }
  pose proof (pair_cost_le_slot es hj e p Hin NN). unfold INPUT_MAX in Hn. lia.
Qed.

Lemma dc_counts : forall L A mem (es : list rentry) (hj : list (hsrc * nat)) (e : rentry) (h h' : hsrc) (j : nat) k n,
  Forall (entry_ok Bm L A mem) es -> In (e, (h, j)) (combine es hj) ->
  slot_cost es hj <= k -> k <= n -> n < INPUT_MAX ->
  same_set (keys_texts (re_keys e)) (texts (hs_held h)) -> NoDup (texts (hs_held h)) ->
  hl_recs (hs_expected h) = [] -> (hs_overlong h = 0 \/ hs_overlong h = 1) ->
  re_skip e = hs_overlong h -> (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) ->
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++
    map (map (Z_to_bv 8)) (lines (hs_state h) (bzs (pending_stream h))) ->
  hs_held h' = hs_held h ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  Z.of_nat (length (with_nul (lines (hs_state h) (bzs (pending_stream h))))) < 2 ^ 26 /\
  NoDup (texts (hs_held h')) /\
  hl_n (hs_expected h') < 2 ^ 26 /\
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22.
Proof.
  intros L A mem es hj e h h' j k n HF Hin Hc Hk Hn SS ND HE0 Hov Hsk HU HM HH.
  pose proof (dc_cost L A mem es hj e (h, j) k n HF Hin Hc Hk Hn) as PC.
  assert (EOK : entry_ok Bm L A mem e).
  { rewrite Forall_forall in HF. apply HF. exact (in_combine_l _ _ _ _ Hin). }
  destruct EOK as (_ & _ & _ & _ & _ & _ & HUl & _ & _ & _ & _ & _ & _ & NDk & KF).
  pose proof (reads_bound e h Hsk HU Hov HUl) as RB.
  assert (KF' : Forall (fun x => 14 <= Z.of_nat (length (key_text x))) (re_keys e)).
  { rewrite Forall_forall in KF |- *. intros x Hx. destruct (KF x Hx) as (_ & _ & _ & _ & (K14 & _) & _). exact K14. }
  pose proof (keys_total_count (re_keys e) KF') as KT.
  pose proof (keys_total_nonneg (re_keys e)) as KN.
  unfold pair_cost in PC. cbn [fst] in PC.
  assert (SK : 0 <= (if re_skip e =? 0 then re_used e else 0)) by (destruct (re_skip e =? 0); lia).
  rewrite HE0 in HM. cbn [map app] in HM.
  pose proof (texts_lines (hs_expected h') _ HM (dc_lines_range h)) as TL.
  pose proof (count_begin_bytes (lines (hs_state h) (bzs (pending_stream h)))) as CB.
  pose proof (lines_count (lines (hs_state h) (bzs (pending_stream h)))) as LC.
  assert (LE : length (hl_recs (hs_expected h')) = length (lines (hs_state h) (bzs (pending_stream h)))).
  { apply (f_equal (@length _)) in HM. rewrite !length_map in HM. exact HM. }
  assert (LH : length (hl_recs (hs_held h)) = length (re_keys e)).
  { pose proof (same_set_length _ _ (nodup_keys_texts _ NDk) ND SS) as SL.
    unfold keys_texts, texts in SL. rewrite !length_map in SL. symmetry. exact SL. }
  assert (P26 : 2 ^ 26 = 67108864) by reflexivity. assert (P22 : 2 ^ 22 = 4194304) by reflexivity.
  unfold hl_n. rewrite HH, TL, LE, LH.
  split; [lia|]. split; [lia|]. split; [exact ND|]. split; lia.
Qed.

Lemma dc_read : forall L A mem HA h, src_at Bm L A mem HA h -> hl_recs (hs_pending h) = [] ->
  bytes_at (ms_segs Bm) mem (HA + 24) (le4 (Z_to_bv 64 0)).
Proof.
  intros L A mem HA h HS HP.
  destruct HS as (_ & _ & _ & _ & _ & (((_ & BY) & _) & _) & _).
  unfold hl_n in BY. rewrite HP in BY. cbn [cells_bytes cbytes length Z.of_nat] in BY.
  rewrite bytes_at_app, length_le8 in BY. destruct BY as [_ BY].
  rewrite bytes_at_app in BY. destruct BY as [BY _].
  replace (HA + 24) with (HA + 16 + Z.of_nat 8) by lia. exact BY.
Qed.

End DC.

Lemma outv_bytes : forall segs m (mx nout cap out : word),
  rw_cells segs m G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
  bytes_at segs m G_NOUT (le8 nout) /\ bytes_at segs m G_OUT (le8 out).
Proof.
  intros segs m mx nout cap out ((_ & BY) & _). cbn [cells_bytes cbytes] in BY.
  rewrite !bytes_at_app, !length_le8 in BY. destruct BY as (_ & B1 & _ & B3 & _).
  split.
  - replace G_NOUT with (G_OUTV + Z.of_nat 8) by (unfold G_NOUT, G_OUTV; lia). exact B1.
  - replace G_OUT with (G_OUTV + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by (unfold G_OUT, G_OUTV; lia). exact B3.
Qed.
