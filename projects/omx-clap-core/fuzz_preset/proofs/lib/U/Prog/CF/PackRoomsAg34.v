From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 FrameAPI SlotPack AllocPack AllocPackRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjGrowUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c check_no_overread_c check_reject_clean_starved_c round_trip_text_c check_round_trip_c EntryDefs EntrySR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_set_c PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackFit PackOwn PackReparse PackVec PackBand PackBig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require AllocPackGSF AllocAgCf34.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require AgreeRoom.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require PackTraceT PackFitCf34 PackBytes34.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require PackFold PackTraceR PackRooms.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.

(* U twin of c-frame-gi's Prog/PackRoomsAg.v: the rooms of CF.PackRooms.rooms at the 2^34 form
   AllocAgCf34.pack_ag34_form. The folds of pack_ag34_form are those of pack_form (the bbg_* bridges below), so the
   bounds of CF.PackRooms' Section Dom hold for them; the form's room adds
   LIVE2c (pb_cap b) (pb_bytes b + n) + NONHEAP_CF <= 2^34, which PackFitCf34.pack_fit_cf_plain_BB gives for at most
   BBMAX live bytes. The live bytes since b0 stay under bbg_Y, so the live bytes stay under bbg_B <= BBMAX.
   The bridges are stated at pbound and proved by unfolding both forms (bbg_norm) or by induction (the folds whose
   fixpoint takes the form as an argument): a conversion that compares the records pack_ag34_form and pack_form
   costs time at each nesting level. *)

Definition bbg_Y : Z := 3103805312.
Definition bbg_B : Z := 3372240768.

Lemma bbg_Y_eq : bbg_Y = 3103805312.
Proof. reflexivity. Qed.

Lemma bbg_live_mono : forall caps y y', y <= y' ->
  U.AllocPackGSF.LIVE2c caps y <= U.AllocPackGSF.LIVE2c caps y'.
Proof.
  intros caps y y' H. unfold U.AllocPackGSF.LIVE2c.
  apply Z.add_le_mono; [apply Z.add_le_mono; [apply Z.add_le_mono; [apply Z.le_refl | exact H] | apply Z.le_refl] | apply Z.le_refl].
Qed.

Ltac bbg_norm := cbv [ent_brej ent_b3 ent_b2 ent_b1 cno_free3 cno_mid cno_b3 rf_frees rf_run rf_ev rf_grow
  rf_free rf_malloc rf_realloc rf_R AllocAgCf34.pack_ag34_form pack_form].

Lemma bbg_run : forall (b : pbound) tr,
  @eq pbound (rf_run AllocAgCf34.pack_ag34_form b tr) (rf_run pack_form b tr).
Proof. intros b tr. bbg_norm. reflexivity. Qed.

Lemma bbg_frees : forall (b : pbound) D,
  @eq pbound (rf_frees AllocAgCf34.pack_ag34_form b D) (rf_frees pack_form b D).
Proof. intros b D. bbg_norm. reflexivity. Qed.

Lemma bbg_malloc : forall (b : pbound) n,
  @eq pbound (rf_malloc AllocAgCf34.pack_ag34_form b n) (rf_malloc pack_form b n).
Proof. intros b n. bbg_norm. reflexivity. Qed.

Lemma bbg_free : forall (b : pbound) n,
  @eq pbound (rf_free AllocAgCf34.pack_ag34_form b n) (rf_free pack_form b n).
Proof. intros b n. bbg_norm. reflexivity. Qed.

Lemma bbg_csr : forall (b3 : pbound) n T (b4 : pbound) cset Do,
  crt_set_res AllocAgCf34.pack_ag34_form b3 n T b4 cset Do <-> crt_set_res pack_form b3 n T b4 cset Do.
Proof. intros. unfold crt_set_res. bbg_norm. reflexivity. Qed.

(* wfold takes the form as an argument of its fixpoint: its two folds are equal by induction. *)
Lemma bbg_wfold : forall P (b : pbound) st,
  @eq pbound (CF.WriterRet.wfold AllocAgCf34.pack_ag34_form b st P) (CF.WriterRet.wfold pack_form b st P).
Proof.
  induction P as [|bs P IH]; intros b st; cbn [CF.WriterRet.wfold]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bbg_txfold : forall ns (b : pbound) len cap,
  @eq pbound (tx_fold AllocAgCf34.pack_ag34_form b len cap ns) (tx_fold pack_form b len cap ns).
Proof.
  induction ns as [|n ns IH]; intros b len cap; cbn [tx_fold]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bbg_rtt_bw : forall (b : pbound) cnt t p,
  @eq pbound (rtt_bw AllocAgCf34.pack_ag34_form b cnt t p) (rtt_bw pack_form b cnt t p).
Proof. intros. unfold rtt_bw. apply bbg_wfold. Qed.

Lemma bbg_rtt_bt : forall (b : pbound) cnt t p,
  @eq pbound (rtt_bt AllocAgCf34.pack_ag34_form b cnt t p) (rtt_bt pack_form b cnt t p).
Proof. intros. unfold rtt_bt. rewrite bbg_rtt_bw. apply bbg_txfold. Qed.

Lemma bbg_rtt_bf : forall (b : pbound) cnt t p,
  @eq pbound (rtt_bf AllocAgCf34.pack_ag34_form b cnt t p) (rtt_bf pack_form b cnt t p).
Proof. intros. unfold rtt_bf, rtt_bp. rewrite bbg_rtt_bt, bbg_run, !bbg_free. reflexivity. Qed.

Lemma bbg_crt_b1 : forall (b : pbound) cnt t,
  @eq pbound (crt_b1 AllocAgCf34.pack_ag34_form b cnt t) (crt_b1 pack_form b cnt t).
Proof. intros. unfold crt_b1. apply bbg_rtt_bf. Qed.

Lemma bbg_crt_b2 : forall (b : pbound) cnt t Df,
  @eq pbound (crt_b2 AllocAgCf34.pack_ag34_form b cnt t Df) (crt_b2 pack_form b cnt t Df).
Proof. intros. unfold crt_b2. rewrite bbg_crt_b1, bbg_rtt_bf. apply bbg_frees. Qed.

Lemma bbg_crt_b5 : forall (b4 : pbound) c4 t,
  @eq pbound (crt_b5 AllocAgCf34.pack_ag34_form b4 c4 t) (crt_b5 pack_form b4 c4 t).
Proof. intros. unfold crt_b5. apply bbg_wfold. Qed.

Lemma bbg_wfull : forall (b : pbound) c t p,
  @eq pbound (wfull AllocAgCf34.pack_ag34_form b c t p) (wfull pack_form b c t p).
Proof. intros. unfold wfull. rewrite bbg_wfold. apply bbg_free. Qed.

Lemma bbg_cpf : forall (b : pbound) c y t p,
  @eq pbound (crs_pass_fold AllocAgCf34.pack_ag34_form b c y t p) (crs_pass_fold pack_form b c y t p).
Proof. intros. unfold crs_pass_fold, wstarve. cbv zeta. rewrite !bbg_wfull, !bbg_wfold, !bbg_free. reflexivity. Qed.

Lemma bbg_crt_fin : forall (b : pbound) c t cset (bf : pbound),
  crt_fin AllocAgCf34.pack_ag34_form b c t cset bf -> crt_fin pack_form b c t cset bf.
Proof.
  intros b c t cset bf (Df & HDf & H). exists Df. split; [exact HDf|].
  destruct t as [| | | txt bits | s | items | ms].
  7: { destruct H as (b4 & Do & Dp & Dp' & Do' & H1 & H2 & H3 & H4 & H5).
       exists b4, Do, Dp, Dp', Do'. rewrite bbg_crt_b2, bbg_malloc in H1. apply (proj1 (bbg_csr _ _ _ _ _ _)) in H1.
       split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
       rewrite H5, bbg_crt_b5, bbg_run, bbg_free, !bbg_frees. reflexivity. }
  all: destruct H as (Db & Db' & H1 & H2 & H3); exists Db, Db'; split; [exact H1|]; split; [exact H2|];
    rewrite H3, bbg_crt_b2, bbg_frees; reflexivity.
Qed.

Lemma bbg_eb1 : forall (b0 : pbound) x E1 E2 E3,
  @eq pbound (ent_b1 AllocAgCf34.pack_ag34_form b0 x E1 E2 E3) (ent_b1 pack_form b0 x E1 E2 E3).
Proof. intros. bbg_norm. reflexivity. Qed.

Lemma bbg_eb2 : forall (b0 : pbound) x E1 E2 E3 Dp,
  @eq pbound (ent_b2 AllocAgCf34.pack_ag34_form b0 x E1 E2 E3 Dp) (ent_b2 pack_form b0 x E1 E2 E3 Dp).
Proof. intros. bbg_norm. reflexivity. Qed.

Lemma bbg_eb3 : forall (b0 : pbound) x E1 E2 E3 Dp,
  @eq pbound (ent_b3 AllocAgCf34.pack_ag34_form b0 x E1 E2 E3 Dp) (ent_b3 pack_form b0 x E1 E2 E3 Dp).
Proof. intros. bbg_norm. reflexivity. Qed.

Lemma bbg_nlive_len : forall P, nlive P <= Z.of_nat (length P).
Proof. induction P as [|e P IH]; cbn [nlive length]; [lia|]. destruct e as [n|[|m] n|n|n]; cbn [nlive_ev]; lia. Qed.

Lemma bbg_capok : forall k, SlotSizes.capok k (rfcap k 0 0).
Proof.
  induction k as [|k IH]; [left; split; reflexivity|].
  rewrite rfcap_S. cbn [Nat.add]. apply SlotSizes.capok_step, IH.
Qed.

Lemma bbg_rfcap : forall k, Z.of_nat k <= 2097152 -> Z.of_nat (rfcap k 0 0) <= 2097152.
Proof.
  induction k as [|k IH]; intros Hk; [cbn; lia|].
  rewrite rfcap_S. cbn [Nat.add].
  destruct (Nat.ltb_spec k (rfcap k 0 0)) as [L|L].
  - unfold PjRoundTrip.gcap. rewrite (proj2 (Nat.ltb_lt _ _) L). cbv beta iota. apply IH. lia.
  - pose proof (SlotSizes.gcap_le k (rfcap k 0 0) (bbg_capok k) L ltac:(change (2 ^ 21) with 2097152; lia)) as G.
    change (2 ^ 21) with 2097152 in G. exact G.
Qed.

Lemma bbg_rkb_top : forall k, Z.of_nat k <= 2097152 -> zl (map Z.of_nat (rkb true (rfcap k 0 0))) <= 134217728.
Proof.
  intros k H. pose proof (bbg_rfcap k H) as C. unfold rkb.
  destruct (Nat.eqb (rfcap k 0 0) 0); cbn [map zl]; lia.
Qed.

Section Ag.

Variable b0 : pbound.
Variable beta : Z -> Z.
Hypothesis Hl0 : length (pb_live b0) = 49%nat.
Hypothesis Hlive0 : forall k, 0 <= k < 49 -> znth k (pb_live b0) <= 2.
Hypothesis Hbytes0 : pb_bytes b0 <= 2 ^ 28.
Hypothesis Hcap0 : forall k, 0 <= k < 49 -> znth k (pb_cap b0) = 3 * beta k + 271.
Hypothesis HC0 : CAPOK2 (GALL (pb_cap b0)) (GMAP (pb_cap b0)) pq_BMAX pq_NMAX.
Variable x : list byte.
Variable cnt0 : Z.
Hypothesis Hbeta : beta = beta2_x (zb x).
Hypothesis Hcnt : 0 <= cnt0 <= 3 * 2 ^ 60.
Hypothesis Hn : ent_n x <= 0x300000.
Variable BB : Z.
Hypothesis HBB : bbg_B <= BB.
Hypothesis Hfit : forall y, 0 <= y <= BB ->
  U.AllocPackGSF.LIVE2c (pb_cap b0) y + AgreeRoom.NONHEAP_CF <= 2 ^ 34.

Lemma bbg_bn : forall k, 0 <= beta k.
Proof. exact (CF.PackRooms.beta_nn beta x Hbeta). Qed.

Lemma bbg_nr : 0 <= ent_n x <= 3145728.
Proof. exact (CF.PackRooms.n_rng b0 Hl0 x Hn). Qed.

Lemma bbg_room : forall b V y r, CF.PackRooms.dom b0 b V y -> 0 <= r <= pq_NMAX -> y + r <= bbg_Y ->
  V (band r) <= 3 * beta (band r) + 268 -> rf_room AllocAgCf34.pack_ag34_form b r.
Proof.
  intros b V y r HD Hr Hy HV.
  cbn [rf_room AllocAgCf34.pack_ag34_form].
  split.
  - apply (CF.PackRooms.room_dom b0 beta Hl0 Hlive0 Hbytes0 Hcap0 HC0 b V y r HD Hr); [|exact HV].
    unfold bbg_Y in Hy. change (2 ^ 42) with 4398046511104. lia.
  - match goal with |- _ <= ?L => change L with (2 ^ 34) end.
    destruct HD as (H1 & H2 & H3 & H4). rewrite H2.
    assert (B0 : pb_bytes b0 <= 268435456) by (change 268435456 with (2 ^ 28); exact Hbytes0).
    unfold bbg_B, bbg_Y in *.
    pose proof (bbg_live_mono (pb_cap b0) (pb_bytes b + r) BB ltac:(lia)) as M.
    pose proof (Hfit BB ltac:(lia)) as F. lia.
Qed.

Lemma bbg_rb : forall b c a y r, CF.PackRooms.dom b0 b (fun k => c + a * beta k) y -> 0 <= a <= 3 -> c <= 268 ->
  0 <= r <= 536862720 -> y + r <= bbg_Y -> rf_room AllocAgCf34.pack_ag34_form b r.
Proof.
  intros b c a y r HD Ha Hc Hr Hy. apply (bbg_room b _ y r HD).
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. lia.
  - exact Hy.
  - cbv beta. pose proof (bbg_bn (band r)) as H0.
    pose proof (Z.mul_le_mono_nonneg_r a 3 (beta (band r)) H0 ltac:(lia)). lia.
Qed.

Lemma bbg_rr : forall b c a y tr c' a' yb es, CF.PackRooms.dom b0 b (fun k => c + a * beta k) y ->
  (forall P R, tr = P ++ R -> forall k, 0 <= k < 49 -> pq_run k P <= c' + a' * beta k) ->
  (forall P R, tr = P ++ R -> held P + 16 * nlive P <= yb) ->
  0 <= a -> 0 <= a' -> a + a' <= 3 -> c + c' <= 268 ->
  (forall e, In e tr -> is_call e = true -> Z.of_nat (esize e) + 16 <= es) -> es <= 268435456 ->
  y + yb + es <= bbg_Y -> room_run AllocAgCf34.pack_ag34_form b tr.
Proof.
  intros b c a y tr c' a' yb es HD HP HB Ha Ha' Haa Hcc He Hes Hy. apply CF.PackRooms.room_run_of.
  intros P e R E Hc.
  assert (Hin : In e tr) by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (He e Hin Hc) as Hs. split; [|change (2 ^ 28) with 268435456; lia].
  rewrite bbg_run.
  pose proof (HP P (e :: R) E) as HP'. pose proof (HB P (e :: R) E) as HB'.
  assert (Hb : 0 <= band (Z.of_nat (esize e) + 16) < 49)
    by (pose proof (band_nonneg (Z.of_nat (esize e) + 16) ltac:(lia));
        pose proof (band_le48 (Z.of_nat (esize e) + 16) ltac:(lia)); lia).
  apply (bbg_room _ _ _ _ (CF.PackRooms.dom_run b0 Hl0 b _ y P HD)).
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. lia.
  - lia.
  - cbv beta. pose proof (HP' _ Hb). pose proof (bbg_bn (band (Z.of_nat (esize e) + 16))) as H0.
    pose proof (Z.mul_le_mono_nonneg_r (a + a') 3 (beta (band (Z.of_nat (esize e) + 16))) H0 ltac:(lia)). lia.
Qed.

Lemma bbg_wr : forall b c a y t' p c0 f, CF.PackRooms.dom b0 b (fun k => c + a * beta k) y -> 0 <= a <= 3 -> c <= 267 ->
  0 <= wlen t' p <= 200000000 -> y + (4 * wlen t' p + 8224) <= bbg_Y ->
  CF.WriterRet.wr_rooms AllocAgCf34.pack_ag34_form b (w0 c0 f) (wdpieces t' p).
Proof.
  intros b c a y t' p c0 f HD Ha Hc Hw Hy. apply CF.PackRooms.wr_rooms_of. intros Q bs R E _ Hlt.
  pose proof (CF.PackRooms.H_wsize t' p c0 f Q bs R E Hlt) as Hn'.
  pose proof (CF.PackRooms.H_wcap t' p c0 f Q (bs :: R) E) as Hcp.
  pose proof (CF.PackRooms.newcap_ge (w_cap (putN (w0 c0 f) Q))
    (Z.of_nat (length (w_text (putN (w0 c0 f) Q))) + Z.of_nat (length bs) + 1) ltac:(lia)) as Hg.
  rewrite bbg_wfold.
  set (r := newcap _ _ + 16).
  pose proof (CF.PackRooms.dom_wfold b0 Hl0 b _ y (w0 c0 f) Q HD eq_refl ltac:(lia)) as D.
  apply (bbg_room _ _ _ r D).
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. unfold r. lia.
  - unfold r. lia.
  - cbv beta. pose proof (bbg_bn (band r)) as H0.
    pose proof (Z.mul_le_mono_nonneg_r a 3 (beta (band r)) H0 ltac:(lia)). lia.
Qed.

Lemma bbg_tx : forall b c a y t' p, CF.PackRooms.dom b0 b (fun k => c + a * beta k) y -> 0 <= a <= 3 -> c <= 267 ->
  0 <= wlen t' p <= 200000000 -> y + (4 * wlen t' p + 16) <= bbg_Y ->
  tx_rooms AllocAgCf34.pack_ag34_form b 0 0 (rtt_ns t' p).
Proof.
  intros b c a y t' p HD Ha Hc Hw Hy. apply CF.PackRooms.tx_rooms_of. intros Q m R E _.
  pose proof (CF.PackRooms.H_txsize t' p Q m R E) as Hs. pose proof (CF.PackRooms.H_txcap t' p Q (m :: R) E) as Hcp.
  pose proof (CF.PackRooms.H_txnn t' p) as Hnn.
  assert (HnnQ : Forall (fun m => 0 <= m) Q) by (rewrite E in Hnn; apply Forall_app in Hnn; exact (proj1 Hnn)).
  assert (Hm : 0 <= m) by (rewrite E in Hnn; apply Forall_app in Hnn; destruct Hnn as [_ Hnn]; inversion Hnn; assumption).
  assert (HzQ : 0 <= zsum Q).
  { clear -HnnQ. induction HnnQ as [|a0 l Ha0 _ IH]; cbn [zsum]; lia. }
  rewrite bbg_txfold.
  pose proof (CF.PackRooms.dom_txfold b0 Hl0 b _ y Q HD HnnQ ltac:(lia)) as D.
  apply (bbg_room _ _ _ _ D).
  - change pq_NMAX with (2 ^ 29 - 8192). change (2 ^ 29) with 536870912. lia.
  - lia.
  - cbv beta. pose proof (bbg_bn (band (2 * (0 + zsum Q + m + 1)))) as H0.
    pose proof (Z.mul_le_mono_nonneg_r a 3 (beta (band (2 * (0 + zsum Q + m + 1)))) H0 ltac:(lia)). lia.
Qed.

Lemma bbg_T_es : forall e, In e (ent_T x) -> is_call e = true -> Z.of_nat (esize e) + 16 <= 56 * ent_n x + 464.
Proof.
  intros e Hi Hc. pose proof (PackTraceT.run_esize jr_strtod (zb x) [] e Hi Hc) as H.
  rewrite CF.PackRooms.zb_len in H. unfold ent_n. lia.
Qed.

Lemma bbg_RT : forall b c a y, CF.PackRooms.dom b0 b (fun k => c + a * beta k) y -> 0 <= a <= 2 -> c <= 168 ->
  y + (256 * ent_n x + 16448) + (56 * ent_n x + 464) <= bbg_Y -> room_run AllocAgCf34.pack_ag34_form b (ent_T x).
Proof.
  intros b c a y HD Ha Hc Hy. pose proof bbg_nr.
  apply (bbg_rr b c a y (ent_T x) 100 1 (256 * ent_n x + 16448) (56 * ent_n x + 464) HD); try lia.
  - exact (CF.PackRooms.T_prefix b0 beta Hl0 x Hbeta).
  - exact (CF.PackRooms.T_bytes x).
  - exact bbg_T_es.
Qed.

Lemma bbg_cno : cno_room AllocAgCf34.pack_ag34_form b0 (ent_n x) (ent_T x) (cno_ok x).
Proof.
  pose proof bbg_nr as NR. pose proof bbg_bn as BN. pose proof bbg_Y_eq as EY. unfold cno_room.
  assert (R0 : forall j, (j <= 2)%nat ->
    rf_room AllocAgCf34.pack_ag34_form (rf_run pack_form b0 (repeat (EAlloc (length x)) j)) (ent_n x + 16)).
  { intros j Hj. apply (bbg_rb _ (0 + Z.of_nat j) (0 + 0) (0 + Z.of_nat j * (ent_n x + 16)) _ (CF.PackRooms.Dcpy b0 beta Hl0 x j));
      first [lia | idtac].
    pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat j) 2 (ent_n x + 16) ltac:(lia) ltac:(lia)). lia. }
  assert (E3 : @eq pbound (cno_b3 AllocAgCf34.pack_ag34_form b0 (ent_n x))
                 (rf_run pack_form b0 (repeat (EAlloc (length x)) 3))) by (bbg_norm; reflexivity).
  rewrite E3, !bbg_malloc.
  split; [exact (R0 0%nat ltac:(lia))|].
  split; [exact (R0 1%nat ltac:(lia))|].
  split; [exact (R0 2%nat ltac:(lia))|].
  pose proof (CF.PackRooms.Dcpy b0 beta Hl0 x 3) as D3. pose proof (proj1 D3) as L3.
  split; [apply (bbg_RT _ _ _ _ D3); cbn; lia|].
  destruct (cno_ok x).
  - pose proof (CF.PackRooms.dom_rb b0 beta Hl0 _ _ _ _ (ent_T x) 0 1 _ D3 (CF.PackRooms.T_le b0 beta Hl0 x Hbeta) (CF.PackRooms.T_full x)) as D4.
    pose proof (CF.PackRooms.dom_rb b0 beta Hl0 _ _ _ _ (ent_T x) 0 1 _ D4 (CF.PackRooms.T_le b0 beta Hl0 x Hbeta) (CF.PackRooms.T_full x)) as D5.
    rewrite !bbg_run.
    split; [apply (bbg_RT _ _ _ _ D4); cbn; lia | apply (bbg_RT _ _ _ _ D5); cbn; lia].
  - intros E1 [P1 L1]. rewrite ?bbg_run, ?bbg_frees.
    rewrite (CF.PackRooms.H_cancel _ (ent_T x) E1 L3 (CF.PackRooms.T_grow x) P1 L1).
    split; [apply (bbg_RT _ _ _ _ D3); cbn; lia|].
    intros E2 [P2 L2]. rewrite ?bbg_run, ?bbg_frees.
    rewrite (CF.PackRooms.H_cancel _ (ent_T x) E2 L3 (CF.PackRooms.T_grow x) P2 L2).
    apply (bbg_RT _ _ _ _ D3); cbn; lia.
Qed.

Lemma bbg_set_held : forall n cap, 0 <= n <= cap -> n <= 2097152 ->
  held (set_trace n cap 10) + 16 * nlive (set_trace n cap 10) <= 134217787.
Proof.
  intros n cap Hn' Hm. pose proof (bbg_nlive_len (set_trace n cap 10)) as Hl.
  pose proof (CF.PackRooms.set_len b0 Hl0 n cap) as Hs.
  assert (Hh : held (set_trace n cap 10) <= 134217739).
  { unfold set_trace. destruct (Z.eqb_spec n cap) as [<-|Hne]; cbn [app held held_ev].
    - unfold cap2. destruct (Z.eqb_spec n 0) as [->|Hz]; rewrite ?Z2Nat.id by lia; lia.
    - rewrite Z2Nat.id by lia. lia. }
  lia.
Qed.

Lemma bbg_dom_set : forall (B2 : pbound) V y n (b4 : pbound) cset Do T, CF.PackRooms.dom b0 (rf_malloc pack_form B2 37) V y ->
  0 <= n <= 2 ^ 21 -> crt_set_res pack_form (rf_malloc pack_form B2 37) n T b4 cset Do ->
  CF.PackRooms.dom b0 b4 (fun k => V k + 3) (y + 134217787) /\ 0 <= cset <= 3.
Proof.
  intros B2 V y n b4 cset Do T HD Hn' Hset.
  destruct Hset as (Db & (HP & _) & [(Hc0 & Di & Dr & Di' & a & HP1 & HP2 & Eb4 & _) |
                                     (cap & Dold & Dnew & Dr & a & a' & Hcap & Hcs & Eb4 & _)]).
  - subst b4. split; [|lia].
    eapply (CF.PackRooms.dom_mono b0 Hl0); [apply (CF.PackRooms.dom_fb b0 Hl0); [exact HD|] | intros k _; cbv beta; lia | lia].
    intros ak Hi. apply (CF.PackRooms.dl_nn b0 Hl0 T Db ak HP).
    apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left.
    exact (Permutation_in _ (Permutation_sym HP2) Hi).
  - subst b4. split; [| rewrite Hcs; pose proof (CF.PackRooms.set_len b0 Hl0 n cap); lia].
    eapply (CF.PackRooms.dom_mono b0 Hl0); [apply (CF.PackRooms.dom_run b0 Hl0), HD | intros k Hk; cbv beta | ].
    + pose proof (CF.PackRooms.set_prefix b0 beta Hl0 x n cap (set_trace n cap 10) [] ltac:(rewrite app_nil_r; reflexivity) k Hk). lia.
    + pose proof (bbg_set_held n cap ltac:(lia) ltac:(change (2 ^ 21) with 2097152 in Hn'; lia)). lia.
Qed.

Section Some.
Variable t : jv.
Hypothesis Ht : json_read jr_strtod (zb x) = Some t.

Lemma bbg_zt : zl (map Z.of_nat (rtsz t)) + 16 * Z.of_nat (length (rtsz t)) <= 232 * ent_n x.
Proof. pose proof (PackBytes34.bbg_read jr_strtod (zb x) t Ht) as H. rewrite CF.PackRooms.zb_len in H. exact H. Qed.

Lemma bbg_tt : forall P R, PjRoundTrip.ttrace t = P ++ R -> held P + 16 * nlive P <= 232 * ent_n x.
Proof. intros P R E. pose proof (CF.PackRooms.H_tbytes t P R E). pose proof bbg_zt. lia. Qed.

Lemma bbg_tt_full : held (PjRoundTrip.ttrace t) + 16 * nlive (PjRoundTrip.ttrace t) <= 232 * ent_n x.
Proof. apply (bbg_tt _ []). rewrite app_nil_r. reflexivity. Qed.

Lemma bbg_crt_zl : forall ms, t = JObj ms ->
  zl (map Z.of_nat (rtsz (crt_tree t))) + 16 * Z.of_nat (length (rtsz (crt_tree t))) <= 232 * ent_n x + 134218336.
Proof.
  intros ms E. pose proof bbg_zt as Z0. pose proof (CF.PackRooms.H_crt_len t) as L.
  pose proof (CF.PackRooms.ms_small b0 Hl0 x Hn t Ht ms E) as MS. change (2 ^ 21) with 2097152 in MS.
  rewrite E in Z0, L |- *.
  destruct (CF.PackTraceR.crt_zl_gen Z.of_nat ms) as [(A & v & B & _ & E1)|E1].
  - pose proof (CF.PackTraceR.zl_nn Z.of_nat (rtsz v) Nat2Z.is_nonneg). rewrite CF.PackTraceR.stamp_elen in E1. lia.
  - pose proof (CF.PackTraceR.rkb_gcap true (length ms) (rfcap (length ms) 0 0)) as G.
    rewrite rfcap_S in E1. cbn [Nat.add] in E1.
    pose proof (bbg_rkb_top (length ms) MS) as C.
    rewrite CF.PackTraceR.stamp_elen, CF.PackTraceR.modat_elen in E1. lia.
Qed.

Lemma bbg_ct : forall ms, t = JObj ms -> forall P R, PjRoundTrip.ttrace (crt_tree t) = P ++ R ->
  held P + 16 * nlive P <= 232 * ent_n x + 134218336.
Proof. intros ms E P R E2. pose proof (CF.PackRooms.H_tbytes (crt_tree t) P R E2). pose proof (bbg_crt_zl ms E). lia. Qed.

Lemma bbg_tes : forall e, In e (PjRoundTrip.ttrace t) \/ In e (PjRoundTrip.ttrace (crt_tree t)) ->
  is_call e = true -> Z.of_nat (esize e) + 16 <= 134217728.
Proof.
  intros e Hi Hc. pose proof (SlotSizes.crt_esz jr_strtod (zb x) t Ht (CF.PackRooms.zb_small b0 Hl0 x Hn) e Hi Hc) as H.
  change (2 ^ 27) with 134217728 in H. exact H.
Qed.

Lemma bbg_RTT : forall b c a y p cnt, CF.PackRooms.dom b0 b (fun k => c + a * beta k) y -> 0 <= a <= 2 -> c <= 200 ->
  0 <= wlen t p <= 56 * ent_n x -> y + (4 * wlen t p + 4120) + 232 * ent_n x + 134217728 <= bbg_Y ->
  rtt_rooms AllocAgCf34.pack_ag34_form b cnt t p.
Proof.
  intros b c a y p cnt HD Ha Hc Hw Hy. pose proof bbg_nr.
  unfold rtt_rooms. split; [|split].
  - apply (bbg_wr b c a y); [exact HD | lia | lia | lia | lia].
  - rewrite bbg_rtt_bw. apply (bbg_tx _ (c + 1) a (y + (2 * wlen t p + 4112))); [| lia | lia | lia | lia].
    exact (CF.PackRooms.D_bw b0 beta Hl0 b c a y cnt t p HD).
  - rewrite bbg_rtt_bt.
    apply (bbg_rr _ (c + 2) a (y + (2 * wlen t p + 4112) + (2 * wlen t p + 8)) _ 64 1 (232 * ent_n x) 134217728
             (CF.PackRooms.D_bt b0 beta Hl0 b c a y cnt t p HD)); try lia.
    + exact (CF.PackRooms.tt_prefix b0 beta Hl0 x Hbeta t Ht).
    + exact bbg_tt.
    + intros e Hi Hc'. exact (bbg_tes e (or_introl Hi) Hc').
Qed.

Lemma bbg_crt : crt_pre_rooms AllocAgCf34.pack_ag34_form (rf_run pack_form b0 (ent_T x)) (ent_c3 cnt0 x) t.
Proof.
  pose proof bbg_nr as NR. pose proof (CF.PackRooms.wl_false x t Ht) as WF. pose proof (CF.PackRooms.wl_true x t Ht) as WT.
  pose proof (CF.PackRooms.wl_nn b0 Hl0 t false). pose proof (CF.PackRooms.wl_nn b0 Hl0 t true).
  pose proof (CF.PackRooms.DB3 b0 beta Hl0 x Hbeta) as D3.
  pose proof (CF.PackRooms.H_wlen_crt b0 Hl0 t) as WC. pose proof (CF.PackRooms.wl_nn b0 Hl0 (crt_tree t) true).
  pose proof (CF.PackRooms.c3_62 b0 Hl0 x cnt0 Hcnt Hn) as C62. pose proof bbg_Y_eq as EY.
  assert (DB : CF.PackRooms.dom b0 (rf_run pack_form (rf_run pack_form b0 (ent_T x)) (PjRoundTrip.ttrace t))
                 (fun k => ((0 + 0) + 0) + ((0 + 1) + 1) * beta k) ((0 + (256 * ent_n x + 16448)) + 232 * ent_n x)).
  { exact (CF.PackRooms.dom_rb b0 beta Hl0 _ _ _ _ _ 0 1 _ D3 (CF.PackRooms.tt_le b0 beta Hl0 x Hbeta t Ht) bbg_tt_full). }
  unfold crt_pre_rooms. split; [|split].
  - apply (bbg_RTT _ _ _ _ false _ D3); lia.
  - rewrite bbg_crt_b1. unfold crt_b1.
    rewrite (CF.PackRooms.H_rtt_bf _ (ent_c3 cnt0 x) t false (proj1 D3) C62 ltac:(change (2 ^ 28) with 268435456; lia)).
    apply (bbg_RTT _ _ _ _ true _ DB); lia.
  - intros ms Hms Df HDf. rewrite bbg_crt_b2.
    rewrite (CF.PackRooms.H_crt_b2 _ (ent_c3 cnt0 x) t Df (zb x) (proj1 D3) C62 Ht (CF.PackRooms.zb_small b0 Hl0 x Hn) HDf).
    pose proof (CF.PackRooms.ms_small b0 Hl0 x Hn t Ht ms Hms) as MS. change (2 ^ 21) with 2097152 in MS.
    assert (DM : CF.PackRooms.dom b0 (rf_run pack_form (rf_run pack_form (rf_run pack_form b0 (ent_T x)) (PjRoundTrip.ttrace t)) [EAlloc 21])
                   (fun k => (((0 + 0) + 0) + 1) + (((0 + 1) + 1) + 0) * beta k)
                   (((0 + (256 * ent_n x + 16448)) + 232 * ent_n x) + 37)).
    { apply (CF.PackRooms.dom_rb b0 beta Hl0 _ _ _ _ _ 1 0 _ DB);
        [intros k _; pose proof (CF.PackRooms.pq_run_len k [EAlloc 21]); cbn [length] in *; lia | cbn; lia]. }
    unfold crt_obj_rooms. split; [|split].
    + apply (bbg_rb _ _ _ _ 37 DB); lia.
    + intros cap Hcap. rewrite bbg_malloc.
      change (room_run AllocAgCf34.pack_ag34_form
                (rf_run pack_form (rf_run pack_form (rf_run pack_form b0 (ent_T x)) (PjRoundTrip.ttrace t)) [EAlloc 21])
                (set_trace (Z.of_nat (length ms)) cap 10)).
      apply (bbg_rr _ _ _ _ _ 3 0 (3 * (112 * 2 ^ 21 + 464)) 234881488 DM).
      * intros P R E k Hk. exact (CF.PackRooms.set_prefix b0 beta Hl0 x _ _ P R E k Hk).
      * intros P R E. exact (CF.PackRooms.set_bytes b0 Hl0 x (Z.of_nat (length ms)) cap P R ltac:(lia)
                               ltac:(change (2 ^ 21) with 2097152; lia) E).
      * lia.
      * lia.
      * lia.
      * lia.
      * intros e Hi Hc. pose proof (CF.PackRooms.H_set_esize (Z.of_nat (length ms)) cap e ltac:(lia) Hi Hc). lia.
      * lia.
      * change (2 ^ 21) with 2097152. lia.
    + intros b4 cset Do Hset. rewrite bbg_malloc in Hset. apply (proj1 (bbg_csr _ _ _ _ _ _)) in Hset.
      destruct (bbg_dom_set _ _ _ (Z.of_nat (length ms)) b4 cset Do (PjRoundTrip.ttrace t) DM
                  ltac:(change (2 ^ 21) with 2097152; lia) Hset) as (D4 & Hcs).
      set (y4 := (((0 + (256 * ent_n x + 16448)) + 232 * ent_n x) + 37) + 134217787) in D4.
      assert (D4' : CF.PackRooms.dom b0 b4 (fun k => 4 + 2 * beta k) y4)
        by (eapply (CF.PackRooms.dom_mono b0 Hl0); [exact D4 | intros k _; cbv beta; lia | lia]).
      split.
      * apply (bbg_wr _ 4 2 y4 (crt_tree t) true _ _ D4'); unfold y4; lia.
      * unfold crt_b5. rewrite bbg_wfold.
        pose proof (CF.PackRooms.H_wcap (crt_tree t) true (crt_cnt2 (ent_c3 cnt0 x) t + 1 + cset) (2 ^ 64 - 1)
                      (wdpieces (crt_tree t) true) [] ltac:(rewrite app_nil_r; reflexivity)) as W.
        pose proof (CF.PackRooms.dom_wfold b0 Hl0 _ _ _ (w0 (crt_cnt2 (ent_c3 cnt0 x) t + 1 + cset) (2 ^ 64 - 1))
                      (wdpieces (crt_tree t) true) D4' eq_refl ltac:(lia)) as D5.
        assert (D5' : CF.PackRooms.dom b0 (CF.WriterRet.wfold pack_form b4 (w0 (crt_cnt2 (ent_c3 cnt0 x) t + 1 + cset) (2 ^ 64 - 1))
                            (wdpieces (crt_tree t) true))
                        (fun k => 5 + 2 * beta k) (y4 + (2 * wlen (crt_tree t) true + 4112)))
          by (eapply (CF.PackRooms.dom_mono b0 Hl0); [exact D5 | intros k _; cbv beta; lia | lia]).
        apply (bbg_rr _ 5 2 _ _ 68 1 (232 * ent_n x + 134218336) 134217728 D5').
        -- exact (CF.PackRooms.crt_prefix b0 beta Hl0 x Hbeta t Ht).
        -- exact (bbg_ct ms Hms).
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- intros e Hi Hc. exact (bbg_tes e (or_intror Hi) Hc).
        -- lia.
        -- unfold y4. lia.
Qed.

Lemma bbg_crs_doc : forall c, 0 <= c <= 4611686018427387904 - 8589934592 ->
  crs_doc_rooms AllocAgCf34.pack_ag34_form (rf_run pack_form b0 (ent_T x)) c (zb x) t.
Proof.
  intros c Hc. pose proof (CF.PackRooms.DB3 b0 beta Hl0 x Hbeta) as D3. pose proof bbg_nr as NR.
  pose proof (CF.PackRooms.wl_false x t Ht). pose proof (CF.PackRooms.wl_true x t Ht).
  pose proof (CF.PackRooms.wl_nn b0 Hl0 t false). pose proof (CF.PackRooms.wl_nn b0 Hl0 t true).
  pose proof bbg_Y_eq as EY.
  destruct (CF.PackRooms.H_cnt_bounds b0 Hl0 x Hn t true Ht) as (_ & _ & _ & _ & WN).
  pose proof (CF.PackRooms.pick_rng b0 Hl0 (zb x) (wN t true) (proj1 WN)) as PK.
  change (2 ^ 30) with 1073741824 in WN.
  unfold crs_doc_rooms. rewrite bbg_cpf.
  rewrite (CF.PackRooms.H_crs_pass_fold _ c (zb x) t true (proj1 D3) ltac:(change (2 ^ 62) with 4611686018427387904; lia)).
  unfold crs_pass_rooms. rewrite !bbg_wfull.
  rewrite (CF.PackRooms.H_wfull _ c t true (proj1 D3) ltac:(change (2 ^ 62) with 4611686018427387904; lia)).
  rewrite (CF.PackRooms.H_wfull _ (crs_pass_cnt c (zb x) t true) t false (proj1 D3)
             ltac:(unfold crs_pass_cnt; change (2 ^ 62) with 4611686018427387904; lia)).
  split; split; apply (bbg_wr _ _ _ _ _ _ _ _ D3); lia.
Qed.

Lemma bbg_crs : forall c, 0 <= c <= 4611686018427387904 - 17179869184 ->
  crs_rooms AllocAgCf34.pack_ag34_form (rf_run pack_form b0 (ent_T x)) c x 1 t.
Proof.
  intros c Hc. pose proof (CF.PackRooms.DB3 b0 beta Hl0 x Hbeta) as D3. pose proof bbg_nr as NR.
  pose proof bbg_Y_eq as EY.
  unfold crs_rooms. split; [|split].
  - intros _. apply (bbg_RT _ _ _ _ D3); lia.
  - intros _ _. apply bbg_crs_doc. lia.
  - intros _ _ tr D' Hpl. destruct Hpl as (ok & res & Ejr & _ & HP & HLn).
    assert (G : grow_up tr) by (pose proof (jr_grow_up jr_strtod (zb x) ok) as G; rewrite Ejr in G; exact G).
    rewrite bbg_run, bbg_frees.
    rewrite (CF.PackRooms.H_cancel _ tr D' (proj1 D3) G HP HLn).
    assert (Hct : Z.of_nat (calls tr) <= 2 * ent_n x + 2).
    { pose proof (G7_4 jr_strtod (zb x) ok) as H. rewrite Ejr in H. cbn [snd] in H.
      rewrite CF.PackRooms.zb_len in H. unfold ent_n. lia. }
    apply bbg_crs_doc. lia.
Qed.

End Some.

Lemma bbg_none : json_read jr_strtod (zb x) = None -> forall E1 E2 E3 D Dp,
  ent_b1 pack_form b0 x E1 E2 E3 = b0 -> Permutation D Dp -> ent_tree_dl x D ->
  rf_room AllocAgCf34.pack_ag34_form (ent_b2 pack_form b0 x E1 E2 E3 Dp) (ent_n x + 1) /\
  crs_rooms AllocAgCf34.pack_ag34_form (ent_b3 pack_form b0 x E1 E2 E3 Dp) (ent_c3 cnt0 x) x 0 JNull.
Proof.
  intros Hnone E1 E2 E3 D Dp Eb1 HP [HD HDl]. pose proof bbg_nr as NR. pose proof bbg_Y_eq as EY.
  assert (Hok : cno_ok x = false) by (unfold cno_ok; rewrite Hnone; reflexivity).
  assert (HPp : Permutation (map snd Dp) (map Z.of_nat (lsz (ent_T x))))
    by (eapply Permutation_trans; [apply Permutation_sym, Permutation_map, HP | exact HD]).
  assert (HLp : Z.of_nat (length Dp) = nlive (ent_T x)) by (rewrite <- (Permutation_length HP); exact HDl).
  assert (Eb2 : ent_b2 pack_form b0 x E1 E2 E3 Dp = b0).
  { unfold ent_b2. rewrite Hok, Eb1. exact (CF.PackRooms.H_cancel b0 (ent_T x) Dp Hl0 (CF.PackRooms.T_grow x) HPp HLp). }
  rewrite (CF.PackRooms.H_b3 b0 x E1 E2 E3 Dp Hl0), Eb2.
  pose proof (CF.PackRooms.D00 b0 beta Hl0) as D0.
  split; [apply (bbg_rb _ _ _ _ _ D0); lia|].
  unfold crs_rooms. split; [intros _; apply (bbg_RT _ _ _ _ D0); lia|].
  split; intros _ H0; exfalso; exact (H0 eq_refl).
Qed.

Theorem bbg_rooms : entry_rooms AllocAgCf34.pack_ag34_form b0 cnt0 x.
Proof.
  intros _. split; [exact bbg_cno|]. intros E1 E2 E3 HE1 HE2 HE3.
  assert (Eb1 : ent_b1 pack_form b0 x E1 E2 E3 = b0).
  { unfold ent_b1.
    exact (CF.PackRooms.H_cno_fold b0 (ent_n x) (ent_T x) (cno_ok x) E1 E2 E3 Hl0 HE1 HE2 HE3 (CF.PackRooms.T_grow x)). }
  pose proof (CF.PackRooms.DB3 b0 beta Hl0 x Hbeta) as D3. pose proof bbg_nr as NR. pose proof bbg_Y_eq as EY.
  rewrite (bbg_eb1 b0 x E1 E2 E3).
  split; [rewrite Eb1; apply (bbg_RT _ _ _ _ (CF.PackRooms.D00 b0 beta Hl0)); lia|].
  case_eq (json_read jr_strtod (zb x)); [intros t Ht | intros Ht].
  - assert (Hok : cno_ok x = true) by (unfold cno_ok; rewrite Ht; reflexivity).
    assert (Eb2 : ent_b2 pack_form b0 x E1 E2 E3 [] = rf_run pack_form b0 (ent_T x)).
    { unfold ent_b2. rewrite Hok, Eb1. reflexivity. }
    rewrite (bbg_eb2 b0 x E1 E2 E3 []), (bbg_eb3 b0 x E1 E2 E3 []), (CF.PackRooms.H_b3 b0 x E1 E2 E3 [] Hl0), Eb2.
    split; [apply (bbg_rb _ _ _ _ _ D3); lia|].
    split; [exact (bbg_crt t Ht)|].
    intros cset b4 Hfin. apply bbg_crt_fin in Hfin.
    pose proof (CF.PackRooms.H_crt_fin _ _ t cset b4 (zb x) (proj1 D3) (CF.PackRooms.c3_62 b0 Hl0 x cnt0 Hcnt Hn) Ht
                  (CF.PackRooms.zb_small b0 Hl0 x Hn) Hfin) as Eb4.
    subst b4.
    apply (bbg_crs t Ht).
    destruct (CF.PackRooms.H_cnt_bounds b0 Hl0 x Hn t false Ht) as (W1 & W2 & T1 & T2 & _).
    destruct (CF.PackRooms.H_cnt_bounds b0 Hl0 x Hn t true Ht) as (W3 & _ & _ & _ & _).
    pose proof (CF.PackRooms.crt_match_rng b0 Hl0 t _ _ cset _ W2 T2 Hfin) as HM.
    pose proof (CF.PackRooms.c3_rng b0 Hl0 x cnt0 Hcnt).
    unfold ent_c4, crt_count.
    change (2 ^ 60) with 1152921504606846976 in *.
    change (2 ^ 30) with 1073741824 in *. lia.
  - intros D Dp HP HD. rewrite (bbg_eb2 b0 x E1 E2 E3 Dp), (bbg_eb3 b0 x E1 E2 E3 Dp).
    exact (bbg_none Ht E1 E2 E3 D Dp Eb1 HP HD).
Qed.

End Ag.

Theorem rooms_ag34 : forall (b0 : pbound) (beta : Z -> Z),
  length (pb_live b0) = 49%nat ->
  (forall k, 0 <= k < 49 -> znth k (pb_live b0) <= 2) ->
  pb_bytes b0 <= 2 ^ 28 ->
  (forall k, 0 <= k < 49 -> znth k (pb_cap b0) = 3 * beta k + 271) ->
  CAPOK2 (GALL (pb_cap b0)) (GMAP (pb_cap b0)) pq_BMAX pq_NMAX ->
  forall (x : list byte) (cnt0 : Z), beta = beta2_x (zb x) -> 0 <= cnt0 <= 3 * 2 ^ 60 -> ent_n x <= 0x300000 ->
  pb_cap b0 = CS_of beta ->
  entry_rooms AllocAgCf34.pack_ag34_form b0 cnt0 x.
Proof.
  intros b0 beta Hl0 Hlive0 Hbytes0 Hcap0 HC0 x cnt0 Hbeta Hcnt Hn Hcs.
  apply bbg_rooms with (beta := beta) (BB := PackFitCf34.BBMAX); try assumption.
  - unfold bbg_B, PackFitCf34.BBMAX. lia.
  - intros y Hy. rewrite Hcs, Hbeta.
    assert (Hx : Z.of_nat (length (zb x)) <= pf_MAX)
      by (rewrite CF.PackRooms.zb_len; unfold ent_n, pf_MAX in *; lia).
    exact (PackFitCf34.pack_fit_cf_plain_BB (zb x) Hx y Hy).
Qed.

(* The entry's fold at pack_ag34_form is its fold at pack_form, and its witness at pack_ag34_form is one at
   pack_form: so CF.PackFold.entry_fold_pack gives the fold equality at pack_ag34_form. *)
Theorem ag_entry_fold34 : forall (b0 : pbound) cnt0 x E1 E2 E3 Dp cset (b4 : pbound) trs Ds Df,
  @eq pbound (entry_fold AllocAgCf34.pack_ag34_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df)
    (entry_fold pack_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df).
Proof.
  intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df. unfold entry_fold.
  destruct (0x300000 <? ent_n x). { reflexivity. }
  destruct (json_read jr_strtod (zb x)) as [t|].
  2: { bbg_norm. reflexivity. }
  unfold ent_b5, crs_doc_fold. rewrite !bbg_cpf. bbg_norm. reflexivity.
Qed.

Lemma ag_entry_wit34 : forall (b0 : pbound) cnt0 x E1 E2 E3 Dp cset (b4 : pbound) trs Ds Df,
  entry_wit AllocAgCf34.pack_ag34_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df ->
  entry_wit pack_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df.
Proof.
  intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df HW Hb.
  destruct (HW Hb) as (W1 & W2 & W3 & W). clear HW.
  split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
  destruct (json_read jr_strtod (zb x)) as [t|].
  2: { exact W. }
  destruct W as (WF & W4 & W5). split; [|split; [exact W4 | exact W5]].
  rewrite <- bbg_eb3. exact (bbg_crt_fin _ _ _ _ _ WF).
Qed.

Theorem entry_fold_ag34 : forall (b0 : pbound) cnt0 x E1 E2 E3 Dp cset (b4 : pbound) trs Ds Df,
  length (pb_live b0) = 49%nat -> 0 <= cnt0 <= 3 * 2 ^ 60 ->
  entry_wit AllocAgCf34.pack_ag34_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df ->
  entry_fold AllocAgCf34.pack_ag34_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df = b0.
Proof.
  intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df HL Hc HW. rewrite ag_entry_fold34.
  exact (CF.PackFold.entry_fold_pack b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df HL Hc
           (ag_entry_wit34 b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df HW)).
Qed.
