(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module paths and module names changed; 195 of its 264 lines of code are new or changed and 595 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import
  Img0 Contract FrameAPI SlotKept SlotPack AllocPack AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotExitRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require SlotRI3 SlotNcWt ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fin_key_lens : forall ks, key_lens (map short_key ks) = key_lens ks.
Proof. intros ks. unfold key_lens. rewrite map_map. reflexivity. Qed.

Lemma fin_keys_out : forall ks, keys_out (map short_key ks) = keys_out ks.
Proof. intros ks. unfold keys_out. rewrite map_map. reflexivity. Qed.

Lemma fin_key_runs : forall nm ks, key_runs nm (map short_key ks) = key_runs nm ks.
Proof. intros nm ks. unfold key_runs. rewrite map_map. reflexivity. Qed.

Lemma fin_end_run : forall nm live mx es no cap j o,
  entries_end_run nm live mx no cap (map short_entry es) j o = entries_end_run nm live mx no cap es j o.
Proof.
  intros nm live mx es. induction es as [|e es IH]; intros no cap j o; [reflexivity|].
  cbn [map entries_end_run]. cbn [short_entry re_keys re_cap re_buf re_hp re_kh].
  rewrite fin_key_runs, fin_key_lens, short_keys_total, IH. reflexivity.
Qed.

Lemma fin_tr : forall nm live mx no cap es j o,
  relay_finish_tr nm live mx no cap (map short_entry es) j o = relay_finish_tr nm live mx no cap es j o.
Proof. intros nm live mx no cap es j o. unfold relay_finish_tr. rewrite fin_end_run. reflexivity. Qed.

Lemma fin_cap : forall live mx no cap es,
  relay_finish_cap live mx no cap (map short_entry es) = relay_finish_cap live mx no cap es.
Proof. intros live mx no cap es. unfold relay_finish_cap. rewrite fin_end_run. reflexivity. Qed.

Lemma fin_rout : forall nm live mx no cap es j o,
  relay_finish_out nm live mx no cap (map short_entry es) j o = relay_finish_out nm live mx no cap es j o.
Proof. intros nm live mx no cap es j o. unfold relay_finish_out. rewrite fin_end_run. reflexivity. Qed.

Lemma fin_total : forall es, entries_total (map short_entry es) = entries_total es.
Proof.
  induction es as [|e es IH]; [reflexivity|].
  unfold entries_total in *. cbn [map fold_right]. rewrite IH.
  cbn [short_entry re_keys]. rewrite short_keys_total. reflexivity.
Qed.

Lemma fin_out : forall es, entries_out (map short_entry es) = entries_out es.
Proof.
  intros es. unfold entries_out. rewrite map_map. f_equal. apply map_ext. intros e.
  cbn [short_entry re_keys]. apply fin_keys_out.
Qed.

Lemma fin_cleared : forall es, map entry_cleared (map short_entry es) = map entry_cleared es.
Proof. intros es. rewrite map_map. apply map_ext. intros e. reflexivity. Qed.

Lemma fin_blocks : forall es, concat (map entry_blocks (map short_entry es)) = concat (map entry_blocks es).
Proof. intros es. rewrite map_map. f_equal. apply map_ext. exact short_entry_blocks. Qed.

Lemma fin_end5 {rc : RunCeil} : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
  forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain B a.
Proof.
  intros B API LS SH SK ra empty FF a Ha. unfold frame_facts in FF.
  assert (SEG : ms_segs B = rsegs) by tauto. assert (GUARD : ms_guard B = 0x51de0) by tauto.
  assert (GOT : ms_got_guard B = 0x205e0) by tauto. assert (CTX : ms_ctx B = 0x51e78) by tauto.
  assert (LOCK : ms_lock B = 0x51e70) by tauto. assert (LIBC : ms_libc B = 0x51e00) by tauto.
  assert (SCL : ms_size_classes B = 0x10500) by tauto. assert (SMC : ms_small_cnt B = 0x10560) by tauto.
  assert (MDC : ms_med_cnt B = 0x1057b) by tauto. assert (DBJ : ms_debruijn B = 0x104e0) by tauto.
  assert (TP : ms_tp B = 0x31b70) by tauto. assert (EOFF : ms_errno_off B = -164) by tauto.
  assert (VML : ms_vmlock B = Some 0x52654) by tauto. clear FF.
  assert (RO : forallb (fun i => ro_addr rsegs (Z_to_bv 64 (END5_ADDR + Z.of_nat i))) (seq 0 5) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in RO. specialize (RO (Z.to_nat (a - END5_ADDR)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in RO by lia. replace (END5_ADDR + (a - END5_ADDR)) with a in RO by lia.
  split; [exact (ro_in_img B SEG a ltac:(unfold END5_ADDR in *; lia) RO)|].
  unfold static_owned, errno_addr, vml_lo, vml_len.
  rewrite GUARD, GOT, CTX, LOCK, LIBC, SCL, SMC, MDC, DBJ, TP, EOFF, VML. cbv beta iota.
  unfold END5_ADDR in *. lia.
Qed.

Section PreFrame.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variables (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono (ms_segs B) m m'.
Hypothesis AF : forall a n k, fresh_block B a n -> 0 < n -> 0 <= k <= n + 7 -> disjoint_from W a k.

Lemma pre_fresh_bytes : forall a n bs, fresh_block B a n -> 0 < n -> Z.of_nat (length bs) <= n + 7 ->
  bytes_at (ms_segs B) m a bs -> bytes_at (ms_segs B) m' a bs.
Proof.
  intros a n bs FR HN HL HB. eapply bytes_at_transport; [exact HB|exact MU|].
  apply (AF a n); [exact FR|exact HN|lia].
Qed.

Lemma pre_fresh_cells : forall a n cs, fresh_block B a n -> 0 < n -> Z.of_nat (cells_size cs) <= n ->
  rw_cells (ms_segs B) m a cs -> rw_cells (ms_segs B) m' a cs.
Proof.
  intros a n cs FR HN HL HC. eapply rw_cells_transport; [exact HC|exact MU|exact WM|].
  apply (AF a n); [exact FR|exact HN|lia].
Qed.

Lemma pre_entry : forall L A e, CF.RelayRep.entry_ok B L A m e -> CF.RelayRep.entry_ok B L A m' (short_entry e).
Proof.
  intros L A e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & BU & H10 & HP & ND1 & ND2 & KS).
  unfold CF.RelayRep.entry_ok, re_nheld in *.
  cbn [short_entry re_fd re_eof re_skip re_pad1 re_pad2 re_buf re_used re_cap re_hp re_kh re_keys re_U re_junk].
  rewrite length_map, short_keys_ptrs, short_keys_addr, short_keys_text.
  do 9 (split; [assumption|]). split.
  { destruct BU as [BU|(C & IN & FR & J & BC)]; [left; exact BU|right].
    split; [exact C|]. split; [exact IN|]. split; [exact FR|]. split; [exact J|].
    eapply pre_fresh_cells; [exact FR|exact C|cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia|exact BC]. }
  split; [exact H10|]. split.
  { destruct HP as [(HP & HK)|(IN & FR & HC & HH & HB)].
    - left. split; [exact HP|]. rewrite HK. reflexivity.
    - right. split; [exact IN|]. split; [exact FR|]. split; [exact HC|]. split; [exact HH|].
      eapply pre_fresh_bytes; [exact FR|lia| |exact HB].
      rewrite slot_key_ptrs_length. lia. }
  split; [exact ND1|]. split; [exact ND2|].
  apply Forall_map. eapply Forall_impl; [|exact KS].
  intros [[addr txt] slack] (IN & FR & HB & NZ & LEN & PAD).
  cbn [short_key key_addr key_text key_slack fst snd] in *.
  split; [exact IN|]. split; [exact FR|]. split.
  { eapply pre_fresh_bytes; [exact FR|lia| |].
    - cbn [short_key key_addr key_text key_slack fst snd]. rewrite length_app. cbn [length]. rewrite length_firstn. lia.
    - rewrite bytes_at_app in HB |- *. destruct HB as [HB HT]. split; [exact HB|].
      change (bytes_at (ms_segs B) m (addr + Z.of_nat (length txt))
        (firstn 8 (Z_to_bv 8 0 :: slack))). apply bytes_at_prefix. exact HT. }
  split; [exact NZ|]. split; [exact LEN|]. rewrite length_firstn.
  pose proof (Z.mod_pos_bound (- (addr + Z.of_nat (length txt) + 1)) 8 ltac:(lia)). lia.
Qed.
End PreFrame.

Lemma fin_apart : forall (rc : RunCeil) B b a n k, (forall x, 0x318a0 <= x < 0x31aa0 -> in_img B x) ->
  @YM05.alloc_ceiling rc <= b -> fresh_block (rc := rc) B a n -> 0 < n -> 0 <= k <= n + 7 ->
  disjoint_from (exit_pre_writes b) a k.
Proof.
  intros rc B b a n k IMG HB (F0 & F1 & NI) HN HK.
  assert (D : a + n + 7 <= 0x318e0 \/ 0x318e8 <= a).
  { destruct (Z_le_gt_dec (a + n + 7) 0x318e0) as [H|H]; [left; exact H|right].
    destruct (Z_le_gt_dec 0x318e8 a) as [H2|H2]; [exact H2|exfalso].
    destruct (Z_le_gt_dec a 0x318e0) as [A0|A0].
    - destruct (Z_le_gt_dec (a + n) 0x318e0) as [A1|A1].
      + apply (NI (n - 1) ltac:(lia)), IMG. lia.
      + apply (NI (0x318e0 - a) ltac:(lia)), IMG. lia.
    - apply (NI 0 ltac:(lia)), IMG. lia. }
  unfold exit_pre_writes. cbn [disjoint_from]. split; [left; lia|]. split; [left; lia|]. split; [lia|exact I].
Qed.

Lemma fin_fd_bound : forall (es : list rentry) i, Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  0 <= nth i (map re_fd es) 0 < 2 ^ 31.
Proof.
  intros es i HF. destruct (nth_in_or_default i (map re_fd es) 0) as [H|H]; [|rewrite H; lia].
  apply in_map_iff in H as (e & EQ & He). rewrite <- EQ. rewrite Forall_forall in HF. exact (HF e He).
Qed.

Lemma fin_fd_cell : forall (rc : RunCeil) B L A m G es tail i,
  Forall (CF.RelayRep.entry_ok (rc := rc) B L A m) es -> table_at B m G es tail -> (i < length es)%nat ->
  rw_cells (ms_segs B) m (G + 56 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))].
Proof.
  intros rc B L A m G es tail i HF (HT & (CW & HB) & W0 & W1 & WR) HI.
  destruct (nth_error es i) as [e|] eqn:HE; [|apply nth_error_None in HE; lia].
  assert (EF : nth i (map re_fd es) 0 = re_fd e) by (apply nth_error_nth; rewrite nth_error_map, HE; reflexivity).
  rewrite EF. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  destruct (table_slice rc B L A m es tail G i e HF HB HE) as [_ BE].
  unfold entry_bytes in BE. rewrite bytes_at_app in BE. destruct BE as [B4 _].
  cbn [cells_size csize] in W1, WR.
  split; [split; [cbn; tauto|cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B4]|].
  cbn [cells_size csize]. split; [lia|]. split; [lia|].
  intros j Hj. replace (G + 56 * Z.of_nat i + j) with (G + (56 * Z.of_nat i + j)) by lia. apply WR. lia.
Qed.

Lemma fin_forall2 : forall X Y (P Q : X -> Y -> Prop) xs ys, Forall2 P xs ys ->
  (forall x y, In x xs -> In y ys -> P x y -> Q x y) -> Forall2 Q xs ys.
Proof.
  intros X Y P Q xs ys H. induction H as [|x y xs ys HP HR IH]; intros HQ; constructor.
  - apply HQ; [left; reflexivity|left; reflexivity|exact HP].
  - apply IH. intros x' y' H1 H2 H3. apply HQ; [right; exact H1|right; exact H2|exact H3].
Qed.

Lemma fin_target : forall G OUT es hj, NoDup (target_addrs G OUT es hj) ->
  G <> OUT /\ ~ In G (concat (map entry_blocks es)) /\ ~ In OUT (concat (map entry_blocks es)) /\
  NoDup (concat (map entry_blocks es)) /\
  (forall p q, In p hj -> In q (hs_blocks (fst p)) ->
     q <> G /\ q <> OUT /\ ~ In q (concat (map entry_blocks es))).
Proof.
  intros G OUT es hj H. apply NoDup_ListNoDup in H. unfold target_addrs in H.
  apply List.NoDup_cons_iff in H as [NG H]. apply List.NoDup_cons_iff in H as [NO H].
  assert (HS : forall p q, In p hj -> In q (hs_blocks (fst p)) ->
                 In q (concat (map (fun p => hs_blocks (fst p)) hj))).
  { intros p q Hp Hq. apply in_concat. exists (hs_blocks (fst p)).
    split; [exact (in_map (fun p0 => hs_blocks (fst p0)) hj p Hp)|exact Hq]. }
  split; [intros EQ; apply NG; left; exact (eq_sym EQ)|].
  split; [intros X; apply NG; right; apply in_or_app; left; exact X|].
  split; [intros X; apply NO; apply in_or_app; left; exact X|].
  split; [apply NoDup_ListNoDup; exact (hf_nodup_l _ _ H)|].
  intros p q Hp Hq. pose proof (HS p q Hp Hq) as HQ.
  split; [intros ->; apply NG; right; apply in_or_app; right; exact HQ|].
  split; [intros ->; apply NO; apply in_or_app; right; exact HQ|].
  intros X. exact (hf_nodup_disj _ _ q H X HQ).
Qed.

Lemma fin_sz_le : forall L A q c, List.NoDup (map fst (blocks L A)) -> 0 <= c ->
  (forall m, In (q, m) (blocks L A) -> m <= c) -> CF.SlotRI3.nc_sz L A q <= c.
Proof.
  intros L A q c HN Hc HB.
  destruct (existsb (fun t => fst t =? q) (blocks L A)) eqn:EX.
  - apply existsb_exists in EX as ([a m] & Hin & Eq). cbn [fst] in Eq. apply Z.eqb_eq in Eq. subst a.
    rewrite (CF.SlotNcWt.nw_sz_at L A q m HN Hin). exact (HB m Hin).
  - rewrite CF.SlotNcWt.nw_sz_none; [exact Hc|]. intros m Hin.
    assert (X : existsb (fun t => fst t =? q) (blocks L A) = true).
    { apply existsb_exists. exists (q, m). split; [exact Hin|cbn [fst]; apply Z.eqb_refl]. }
    congruence.
Qed.

Lemma fin_ncs_view : forall L A G X hj,
  List.NoDup (map fst (blocks L A)) -> In (G, SRC_TABLE) (blocks L A) -> CF.SlotRI3.nc_sz L A X <= TBBYTES ->
  zsum (CF.SlotRI3.nc_sz L A) (concat (map (fun p => src_nc (fst p)) hj)) <= zsum (fun p => nw_src (fst p)) hj ->
  (length hj <= 4)%nat ->
  CF.SlotRI3.ncs (view_of G X [] hj) L A <= nc_wt [] hj.
Proof.
  intros L A G X hj HN HG HX HS Hl.
  pose proof (CF.SlotNcWt.nw_sz_at L A G SRC_TABLE HN HG) as EG.
  unfold CF.SlotRI3.ncs, view_of, nc_wt. cbn [rv_nc map concat app length]. rewrite !zsum_cons, EG, zsum_nil.
  unfold NW_ENT0, NW_SRC0, CF.op_add_c.PARTIAL_BYTES. lia.
Qed.

Lemma fin_src_wt : forall (rc : RunCeil) B L A mem t es hj, List.NoDup (map fst (blocks L A)) ->
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj ->
  zsum (CF.SlotRI3.nc_sz L A) (concat (map (fun p => src_nc (fst p)) hj)) <= zsum (fun p => nw_src (fst p)) hj.
Proof.
  intros rc B L A mem t es hj HN HP. rewrite CF.SlotNcWt.nw_zsum_concat. apply CF.SlotNcWt.nw_zsum_le.
  intros p Hp. destruct (CF.SlotNcWt.nw_f2_r _ _ _ p HP Hp) as (e & _ & Hok).
  unfold pair_ok in Hok. cbv zeta in Hok. destruct Hok as (Hsrc & _).
  exact (CF.SlotNcWt.nw_src_le B L A mem _ (fst p) HN Hsrc).
Qed.

Lemma fin_wt_clear : forall es hj, Forall (fun e => 0 <= re_used e) es -> nc_wt [] hj <= nc_wt es hj.
Proof.
  intros es hj HF. unfold nc_wt. rewrite zsum_nil. cbn [length].
  assert (Z.of_nat (length es) * (8192 + 8) <= zsum nw_ent es).
  { induction HF as [|e es He HF IH]; [rewrite zsum_nil; cbn [length]; lia|]. cbn [length]. rewrite zsum_cons.
    assert (8192 + 8 <= nw_ent e) by (unfold nw_ent, re_nheld, DATA_PER; lia). lia. }
  unfold NW_ENT0. lia.
Qed.

Lemma fin_keep_addr : forall A L L' A' (V V' : rview),
  WF A -> layout_le A L L' ->
  (forall q m, In (q, m) (blocks L' A') -> In q (rv_nc V) -> In q (rv_nc V')) ->
  forall p n n', In (p, n) (user_blocks A) -> In (p, n') (user_blocks A') ->
    In (ptr_addr L p) (rv_nc V) -> In (ptr_addr L' p) (rv_nc V').
Proof.
  intros A L L' A' V V' HW HLE HK p n n' H1 H2 H3.
  pose proof (CF.ListFrame.lf_addr A L L' p n HW HLE H1) as EA.
  apply (HK (ptr_addr L' p) n').
  - exact (in_map (fun b => (ptr_addr L' (fst b), snd b)) _ (p, n') H2).
  - rewrite EA. exact H3.
Qed.

Lemma fin_view_keep : forall G out es hj (live : bool) OUT' L A L' A' CAP' CAP,
  (forall q m, In (q, m) (blocks L' A') ->
     (In (q, m) (blocks L A) /\ q <> out /\ ~ In q (concat (map entry_blocks es))) \/
     (live = true /\ q = OUT' /\ m = CAP') \/ (live = false /\ 0 < CAP /\ q = out /\ m = CAP)) ->
  forall q m, In (q, m) (blocks L' A') -> In q (rv_nc (view_of G out es hj)) ->
    In q (rv_nc (view_of G (if live then OUT' else out) [] hj)).
Proof.
  intros G out es hj live OUT' L A L' A' CAP' CAP HB q m Hq Hv.
  unfold view_of in *. cbn [rv_nc concat map app] in *.
  destruct (HB q m Hq) as [(_ & No & Ne)|[(HL & -> & _)|(HL & _ & -> & _)]].
  - destruct Hv as [Hv|[Hv|Hv]]; [left; exact Hv|exfalso; exact (No (eq_sym Hv))|].
    apply in_app_iff in Hv as [Hv|Hv]; [exfalso; apply Ne|right; right; exact Hv].
    apply in_concat in Hv as (l & Hl & Hql). apply in_map_iff in Hl as (e & <- & He).
    apply in_concat. exists (entry_blocks e). split; [apply in_map; exact He|].
    unfold entry_blocks. unfold entry_nc in Hql. rewrite app_assoc. apply in_or_app. left. exact Hql.
  - rewrite HL. right. left. reflexivity.
  - rewrite HL. right. left. reflexivity.
Qed.
