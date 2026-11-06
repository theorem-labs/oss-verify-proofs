(* check_latest_sent_cgW: the image-A caller-journal walk of check_latest_sent (fuzz_transport.asan, entry 0x84500 =
   transport_sigma TS_check_latest_sent), closing the FROZEN statement of lib/A/Prog/check_latest_sent_cg.v.

   The walk is cut at the four footprint runs of lib/A/Prog/check_latest_sent_seg_runs.v, each carried into SRr by
   lib/A/Prog/DgnTransportCgRun.v decode_run:
   - cls_run_entry from 0x84500, with two exits: len = 0 (to the epilogue 0x847b0) and the loop head 0x8459c;
   - the loop (cls_loop, an induction on the model's fuel): cls_run_pre from the loop head to the bcmp entry, the bcmp
     wrapper cut by its contract at the walk's G journal (lib/A/Prog/check_latest_sent_seg_cj.v cls_bcmp), then
     cls_run_post from the bcmp return, with two exits: the epilogue and the next loop head;
   - cls_run_epi from the epilogue to the return (cls_fin), where the post is assembled.
   Each round is the model's round (lib/A/Prog/check_latest_sent_seg_model.v cls_round); the bcmp result is 0 because
   the model's beq_bytes holds. The G journal is carried across each run by cls_jexec (the written bytes are the
   frame, bytes of G and the caller's int at dp). Three invariants ride along: cls_GA (presence grows from the call's
   memory), cls_KA (every byte outside the call's stack window and the ranges the runs may write keeps its view) and
   cls_PW (the world's bytes of g_cmd outside the st fields stay Bw's); at the return they give the kept fact
   (cls_close_kept). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0s YK0o YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09 YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YA0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportAddr DgnTransportImg DgnTransportCg TransportGCg TransportGRwA TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  check_latest_sent_seg_kit check_latest_sent_seg_model check_latest_sent_seg_cj check_latest_sent_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.

(* register r of the map R *)
Local Abbreviation gr R r := (YK11.getr R (Z_to_bv 5 r)).

(* A register of a state reached by a run, read off the run's register map. *)
Ltac cls_reg EQV := etransitivity; [apply (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV); reflexivity | reflexivity].

(* ------------------------------------------------------------------ *)
(* generic facts                                                       *)
(* ------------------------------------------------------------------ *)

(* Present bytes form a stack range in the sense of lib/Lib/Frame.v. *)
Lemma cls_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* four bytes read back as the low four bytes of a word *)
Lemma cls_rt4 : forall bs : list byte, length bs = 4%nat -> le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. unfold le4.
  pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1.
  rewrite Hl in H1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in H1.
  rewrite (MState.unsigned_lit (bytes_le_to_Z bs)) by lia.
  replace 4%nat with (length bs) by exact Hl. apply YA0d.Z_to_le_bytes_to_Z.
Qed.

(* Four present bytes are a writable C4 cell. *)
Lemma cls_rw_c4 : forall (m : word -> option byte) a b0 b1 b2 b3, 0 <= a -> a + 4 <= 2 ^ 64 ->
  m (wa (a + Z.of_nat 0)) = Some b0 -> m (wa (a + Z.of_nat 1)) = Some b1 ->
  m (wa (a + Z.of_nat 2)) = Some b2 -> m (wa (a + Z.of_nat 3)) = Some b3 ->
  rw_cells rsegs m a [C4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3]))].
Proof.
  intros m a b0 b1 b2 b3 H0 H1 E0 E1 E2 E3. split.
  - split; [first [cbn; tauto | repeat constructor] |].
    cbn [cells_bytes cbytes]. rewrite app_nil_r, (cls_rt4 [b0; b1; b2; b3] eq_refl).
    split; [exact H0|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. unfold mrd.
    destruct i as [|[|[|[|i]]]]; [rewrite E0 | rewrite E1 | rewrite E2 | rewrite E3 | lia]; reflexivity.
  - change (Z.of_nat (cells_size [C4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3]))])) with 4.
    split; [exact H0|]. split; [exact H1|]. intros i Hi.
    assert (Hc : i = Z.of_nat 0 \/ i = Z.of_nat 1 \/ i = Z.of_nat 2 \/ i = Z.of_nat 3) by lia.
    unfold wview. destruct Hc as [-> | [-> | [-> | ->]]];
      [rewrite E0 | rewrite E1 | rewrite E2 | rewrite E3]; discriminate.
Qed.

(* A byte the view reads is not hidden. *)
Lemma cls_vis_av : forall (W : world tfibsegs) (m : word -> option byte) a,
  aview tfibsegs (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a H. destruct (aview tfibsegs (w_H W) m a) as [v|] eqn:E;
    [exact (decode_aview_vis W m a v E) | exfalso; exact (H eq_refl)].
Qed.

(* Two memories with the same view of a visible byte read the same byte. *)
Lemma cls_mrd_eq : forall (W : world tfibsegs) (m m2 : word -> option byte) a,
  w_H W (Z_to_bv 64 a) = false -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a ->
  mrd rsegs m2 (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m2 a Hv E. rewrite !(decode_aview_mrd W _ a Hv) in E.
  destruct (mrd rsegs m2 (wa a)) as [b2|]; destruct (mrd rsegs m (wa a)) as [b1|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* AsanCells' addressable from the view's range_addressable, over application memory. *)
Lemma cls_addressable : forall (W : world tfibsegs) (m : word -> option byte) p n,
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n -> 0 <= p -> 0 <= n -> amem_range p n ->
  addressable m p n.
Proof.
  intros W m p n HA Hp Hn Hm. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi. split.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
  - destruct (HA (p + i) ltac:(lia)) as (s & Hs & Hok).
    destruct (decode_aview_some W m _ s Hs) as (_ & b & Hb & Eb).
    exists b. split.
    + replace (AsanCells.shadow_addr (p + i)) with (shadow_of_addr SHADOW_OFF (p + i))
        by (unfold AsanCells.shadow_addr, shadow_of_addr, ASAN_K, SHADOW_OFF; lia).
      exact Hb.
    + pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
      unfold saddr_ok in Hok. unfold AsanCells.shadow_ok.
      rewrite decode_byte_signed by lia. lia.
Qed.

(* the shadow byte of x + o lies in the 8-aligned shadow cover of [x, x + n) *)
Lemma cls_hull_in : forall x n o, 0 <= x -> 0 <= o < n ->
  YG0f.shadow_addr x / 8 * 8 <= (x + o) / 8 + 2147450880 < YG0f.shadow_addr (x + n - 1) / 8 * 8 + 8.
Proof.
  intros x n o Hx Ho. unfold YG0f.shadow_addr, SHADOW_OFF.
  assert (D1 : x / 8 <= (x + o) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (x + o) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (M1 : (2147450880 + x / 8) / 8 * 8 <= 2147450880 + x / 8)
    by (pose proof (Z.mul_div_le (2147450880 + x / 8) 8 ltac:(lia)); lia).
  assert (M2 : 2147450880 + (x + n - 1) / 8 < (2147450880 + (x + n - 1) / 8) / 8 * 8 + 8)
    by (pose proof (Z.mod_pos_bound (2147450880 + (x + n - 1) / 8) 8 ltac:(lia));
        pose proof (Z.div_mod (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)); lia).
  lia.
Qed.

Lemma cls_nth_firstn : forall {A : Type} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|i] d Hi; cbn; try lia; try reflexivity.
  apply IH. lia.
Qed.

Lemma cls_nth_skipn : forall {A : Type} k (l : list A) i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros A k. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct i; reflexivity | apply IH].
Qed.

Lemma cls_nth_sub : forall (l : list byte) k n i d, 0 <= k -> (i < n)%nat ->
  nth i (TW.sub l k n) d = nth (Z.to_nat k + i) l d.
Proof. intros l k n i d Hk Hi. unfold TW.sub. rewrite cls_nth_firstn by exact Hi. apply cls_nth_skipn. Qed.

Lemma cls_sub1_nth : forall (X Y : list byte) j d, (Z.to_nat j < length X)%nat -> (Z.to_nat j < length Y)%nat ->
  TW.sub X j 1 = TW.sub Y j 1 -> nth (Z.to_nat j) X d = nth (Z.to_nat j) Y d.
Proof.
  intros X Y j d HX HY E. unfold TW.sub in E. rewrite !cls_firstn1 in E.
  rewrite (nth_error_nth' X d HX), (nth_error_nth' Y d HY) in E.
  injection E as E. exact E.
Qed.

(* every range of G_HARNESS is non-empty *)
Lemma cls_G_pos : forall b n, In (b, n) TG.G_HARNESS -> 0 < n.
Proof.
  intros b n H. unfold TG.G_HARNESS in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.

(* the three harness ranges the walk stores into are bytes of G *)
Lemma cls_inG_w : forall a, (6181888 <= a < 6181888 + 40960) \/ (6233088 <= a < 6233088 + 4096) \/
  (6158688 <= a < 6158688 + 4) -> inG TG.G_HARNESS a.
Proof.
  intros a Ha. unfold inG. apply Exists_exists. destruct Ha as [Ha | [Ha | Ha]].
  - exists (TA_g_cmd, TW.SZ_g_cmd). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_cmd)|].
    unfold in_zr. cbn [fst snd]. unfold TA_g_cmd, TW.SZ_g_cmd. lia.
  - exists (TA_g_q, TW.SZ_g_q). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_q)|].
    unfold in_zr. cbn [fst snd]. unfold TA_g_q, TW.SZ_g_q. lia.
  - exists (TA_g_nq, TW.SZ_g_nq). split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_nq)|].
    unfold in_zr. cbn [fst snd]. unfold TA_g_nq, TW.SZ_g_nq. lia.
Qed.

(* a byte read back through le_byte *)
Lemma cls_byte_le : forall b : byte, Z_to_bv 8 (le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as HR. unfold bv_modulus in HR. change (2 ^ Z.of_N 8) with 256 in HR.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold le_byte, bv_wrap, bv_modulus.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.shiftr_0_r, !Z.mod_small by lia. reflexivity.
Qed.

(* the bytes of a visible bytes_at, read as garr8 of the view, and back *)
Lemma cls_bytes_of_garr8 : forall (W : world tfibsegs) (m : word -> option byte) a (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  garr8 tfibsegs (mrestrict (w_H W) m) a (TW.zs bs) ->
  (forall i, (i < length bs)%nat -> w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  bytes_at rsegs m a bs.
Proof.
  intros W m a bs H0 H1 HG HV. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  assert (Hm : (i < length (TW.zs bs))%nat) by (unfold TW.zs; rewrite length_map; exact Hi).
  destruct (HG i Hm) as [HV1 _]. specialize (HV1 0%nat ltac:(lia)).
  cbn [Z.of_nat] in HV1. rewrite Z.add_0_r in HV1.
  unfold mbyte, mrestrict in HV1. rewrite (HV i Hi) in HV1.
  unfold mrd, wa.
  transitivity (Some (Z_to_bv 8 (le_byte (nth i (TW.zs bs) 0) 1 0))); [exact HV1|].
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal.
  assert (EN : nth i (TW.zs bs) 0 = bv_unsigned (nth i bs (Z_to_bv 8 0))).
  { unfold TW.zs. rewrite (nth_indep (map bv_unsigned bs) 0 (bv_unsigned (Z_to_bv 8 0)))
      by (rewrite length_map; exact Hi).
    apply map_nth. }
  rewrite EN. apply cls_byte_le.
Qed.

Lemma cls_garr8_of_bytes : forall (W : world tfibsegs) (m : word -> option byte) a (bs : list byte),
  bytes_at rsegs m a bs ->
  (forall i, (i < length bs)%nat -> w_H W (Z_to_bv 64 (a + Z.of_nat i)) = false) ->
  garr8 tfibsegs (mrestrict (w_H W) m) a (TW.zs bs).
Proof.
  intros W m a bs (H0 & H1 & HB) HV j Hj. unfold TW.zs in Hj. rewrite length_map in Hj.
  assert (EN : nth j (TW.zs bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
  { unfold TW.zs. rewrite (nth_indep (map bv_unsigned bs) 0 (bv_unsigned (Z_to_bv 8 0)))
      by (rewrite length_map; exact Hj).
    apply map_nth. }
  pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as HR.
  unfold bv_modulus in HR. change (2 ^ Z.of_N 8) with 256 in HR.
  split; [|rewrite EN; lia].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold mbyte, mrestrict. rewrite (HV j Hj).
  specialize (HB j Hj). unfold mrd, wa in HB.
  transitivity (Some (nth j bs (Z_to_bv 8 0))).
  { rewrite <- (nth_error_nth' bs (Z_to_bv 8 0) Hj). exact HB. }
  f_equal. rewrite EN. symmetry. apply cls_byte_le.
Qed.

(* ---- the world's bytes of g_cmd outside the st fields ---- *)

Ltac cls_lia2 :=
  unfold TW.A_Cmd_st, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.OFF_g_q, TW.OFF_g_nq, TW.W_LEN, TC.CMDS_MAX in *;
  rewrite ?TWorldLemmas.length_put; lia.

Definition cls_PW (Bref Bc : list byte) : Prop :=
  forall j, TW.OFF_g_cmd <= j < TW.OFF_g_cmd + TW.SZ_g_cmd ->
    (forall s, 0 <= s < TC.CMDS_MAX -> ~ (TW.A_Cmd_st s <= j < TW.A_Cmd_st s + 4)) ->
    TW.sub Bc j 1 = TW.sub Bref j 1.

Lemma cls_PW_q : forall Bref X k v, Z.of_nat (length X) = TW.W_LEN -> 0 <= k < TC.CMDS_MAX ->
  cls_PW Bref X -> cls_PW Bref (TW.set_Q_at X k v).
Proof.
  intros Bref X k v HL Hk H j Hj Hn. unfold TW.set_Q_at.
  rewrite TWorldLemmas.sub_upd_out; [exact (H j Hj Hn) | ..]; cls_lia2.
Qed.

Lemma cls_PW_nq : forall Bref X v, Z.of_nat (length X) = TW.W_LEN -> cls_PW Bref X -> cls_PW Bref (TW.set_g_nq X v).
Proof.
  intros Bref X v HL H j Hj Hn. unfold TW.set_g_nq.
  rewrite TWorldLemmas.sub_upd_out; [exact (H j Hj Hn) | ..]; cls_lia2.
Qed.

Lemma cls_PW_st : forall Bref X s, Z.of_nat (length X) = TW.W_LEN -> 0 <= s < TC.CMDS_MAX ->
  cls_PW Bref X -> cls_PW Bref (TW.set_Cmd_st X s TC.SENT).
Proof.
  intros Bref X s HL Hs H j Hj Hn. pose proof (Hn s Hs) as Hns. unfold TW.set_Cmd_st.
  rewrite TWorldLemmas.sub_upd_out; [exact (H j Hj Hn) | ..]; cls_lia2.
Qed.

(* ------------------------------------------------------------------ *)
(* the walk                                                            *)
(* ------------------------------------------------------------------ *)

Section clsw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HSC : trans_cls_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok segs B TG.G_HARNESS.
Hypothesis HBC : forall fx' : YK11.FPState,
  @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp).

Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sj : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (bp len dp disp : Z)
  (body : list byte) (Bw Bw' : list byte).
Hypothesis HJ : @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sj W0 mem0 md0 own
  lyc Sc W memc mdc k.
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis Htp : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 bp.
Hypothesis H11 : YK11.getr regs 11 = w64 len.
Hypothesis H12 : YK11.getr regs 12 = w64 dp.
Hypothesis Hsp16 : spZ regs mod 16 = 0.
Hypothesis Hlo : sp0 - STK <= spZ regs - CLS_STK.
Hypothesis Hhi : spZ regs <= sp0.
Hypothesis Hbp : 0 < bp.
Hypothesis Hlen : Z.of_nat (length body) = len.
Hypothesis HG8 : garr8 segs (mrestrict (w_H W) memc) bp (TW.zs body).
Hypothesis HSRC : trans_src_ok B lyc Sc W memc bp len.
Hypothesis HOW : decode_off_win regs CLS_STK bp len.
Hypothesis HBD : forall x, bp <= x < bp + len -> ~ cls_wr dp x.
Hypothesis Hdp4 : dp mod 4 = 0.
Hypothesis HTWR : transport_twr_ok_g segs B TG.G_HARNESS STK sp0 FP ly Sj lyc Sc own W memc (spZ regs) dp 4.
Hypothesis HDR : decode_rd_ok W memc dp 4.
Hypothesis HDOW : decode_off_win regs CLS_STK dp 4.
Hypothesis HDG : forall x, dp <= x < dp + 4 -> ~ inG TG.G_HARNESS x.
Hypothesis HTW : tw_at TMAP_A (aview segs (w_H W) memc) Bw.
Hypothesis HM : TC.check_latest_sent_m Bw body len = Some (Bw', disp).
Hypothesis HINV : forall s, 0 <= s < TW.g_ncmd Bw -> TW.Cmd_st Bw s = TC.PENDING ->
  TW.Cmd_len Bw s <= DSpec.SPEC_CMD_MAX.
Hypothesis Hev : st_nev Sj + k + CLS_EV <= EV_MAX.

(* the post the walk proves *)
Definition cls_Q : world segs -> config -> Prop :=
  @transport_cg_post_out fx rc tfib_sink_head segs B MT TG.G_HARNESS [(dp, 4)] STK sp0 FP ly Sj W0 mem0 md0 own
    lyc Sc W memc k regs CLS_STK CLS_EV 0 (cls_wr dp)
    (fun regs2 W2 mem2 => tw_at TMAP_A (aview segs (w_H W2) mem2) Bw' /\
                          garr8 segs (mrestrict (w_H W2) mem2) dp (TW.zs (TW.put 4 disp))).

(* the frame at the loop head and at the epilogue, with the saved registers of the call *)
Definition cls_fh (j0 : list byte) : list cell :=
  cls_fr j0 dp bp (gr regs 1) (gr regs 8) (gr regs 9) (gr regs 18) (gr regs 19) (gr regs 20) (gr regs 21)
    (gr regs 22) (gr regs 23) (gr regs 24) (gr regs 25) (gr regs 26) (gr regs 27).
Definition cls_fe (j : list byte) : list cell :=
  cls_fr_e j (gr regs 1) (gr regs 8) (gr regs 9) (gr regs 18) (gr regs 19) (gr regs 20) (gr regs 21)
    (gr regs 22) (gr regs 23) (gr regs 24) (gr regs 25) (gr regs 26) (gr regs 27).

(* ---- the fixed facts of the call ---- *)

Lemma cls_fx_stk : AR segs B lyc Sc W memc mdc /\
  (forall a, spZ regs - CLS_STK <= a < spZ regs -> apresent (w_H W) memc a) /\
  @YM05.alloc_ceiling rc <= spZ regs - CLS_STK /\ spZ regs <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ 0 <= STK.
Proof.
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HAR|]. split; [intros a Ha; apply Hpres0; lia|]. lia.
Qed.

Lemma cls_fx_dp : forall a, dp <= a < dp + 4 ->
  awr_byte STK sp0 FP (ablocks B ly Sj) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a.
Proof.
  intros a Ha. destruct (HTWR a Ha) as [(Hw & Hp & _ & _) | HG]; [exact (conj Hw Hp) | exfalso; exact (HDG a Ha HG)].
Qed.

Lemma cls_fx_bp : bp + len <= 2 ^ 47.
Proof.
  pose proof cls_fx_stk as (HAR & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HSRC as [(bA & nA & Hin & Hb1 & Hb2) | (_ & (_ & _ & _ & Hm & _ & _))].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm. lia.
Qed.

Lemma cls_fx_body_rd : 0 < len -> decode_rd_ok W memc bp len.
Proof.
  intros Hn. pose proof cls_fx_stk as (HAR & _).
  exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc bp len HAR HSRC Hn).
Qed.

Lemma cls_fx_vis_body : forall i, 0 <= i < len -> w_H W (Z_to_bv 64 (bp + i)) = false.
Proof.
  intros i Hi. pose proof (cls_fx_body_rd ltac:(lia)) as (Bv & _).
  apply (cls_vis_av W memc). apply Bv. lia.
Qed.

Lemma cls_fx_cb : cls_body memc bp body.
Proof.
  unfold cls_body. pose proof cls_fx_bp as Hb.
  destruct (Z.eq_dec len 0) as [L0|L0].
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - apply (cls_bytes_of_garr8 W memc bp body); [lia | lia | exact HG8 |].
    intros i Hi. apply cls_fx_vis_body. lia.
Qed.

Lemma cls_fx_bounds : cls_bounds (spZ regs - 144) dp bp len.
Proof.
  pose proof cls_fx_stk as (_ & _ & Hce & H47 & _).
  pose proof asan_consts as (C1 & _).
  pose proof HDR as (_ & _ & _ & _ & D0 & D63).
  pose proof cls_fx_bp as Hb.
  assert (CS : CLS_STK = 8336) by reflexivity.
  unfold cls_bounds. lia.
Qed.

Lemma cls_fx_app_sp : cls_app (spZ regs - 144) 144.
Proof.
  pose proof cls_fx_stk as (_ & _ & Hce & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  right. unfold HIGHMEM_BEG, APPMEM_END. lia.
Qed.

Lemma cls_fx_app_dp : cls_app dp 4.
Proof.
  pose proof HDR as (_ & _ & _ & Hm & D0 & D63).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm.
  unfold cls_app, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

Lemma cls_fx_off : cls_off (spZ regs - 144) dp bp len.
Proof.
  pose proof cls_fx_stk as (_ & _ & Hce & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  pose proof HDOW as HD. pose proof HOW as HO. unfold decode_off_win in HD, HO.
  unfold cls_off. split; [right; unfold TransportG.G_HARNESS_HI; lia|].
  split; [right; lia|]. split; [right; lia|]. split; [lia|]. split; [lia|].
  split.
  { intros b n Hin. pose proof (cls_G_pos b n Hin) as Hn.
    destruct (Z_le_gt_dec (dp + 4) b) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (b + n) dp) as [L'|L']; [right; exact L'|].
    exfalso. apply (HDG (Z.max dp b)); [lia|]. unfold inG. apply Exists_exists. exists (b, n).
    split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  split.
  { intros Hn s Hs.
    destruct (Z_le_gt_dec (bp + len) (6181888 + 40 * s)) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (6181888 + 40 * s + 4) bp) as [L'|L']; [right; exact L'|].
    exfalso. apply (HBD (Z.max bp (6181888 + 40 * s))); [lia|]. left. exists s.
    split; [unfold TC.CMDS_MAX; lia|]. unfold twa_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TA_g_cmd. lia. }
  split.
  { intros Hn.
    destruct (Z_le_gt_dec (bp + len) 6233088) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (6233088 + 4096) bp) as [L'|L']; [right; exact L'|].
    exfalso. apply (HBD (Z.max bp 6233088)); [lia|]. right. left.
    unfold twa_fld, TW.OFF_g_q, TA_g_q, TW.SZ_g_q. lia. }
  split.
  { intros Hn.
    destruct (Z_le_gt_dec (bp + len) 6158688) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (6158688 + 4) bp) as [L'|L']; [right; exact L'|].
    exfalso. apply (HBD (Z.max bp 6158688)); [lia|]. right. right. left.
    unfold twa_fld, TW.OFF_g_nq, TA_g_nq, TW.SZ_g_nq. lia. }
  { intros Hn.
    destruct (Z_le_gt_dec (bp + len) dp) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (dp + 4) bp) as [L'|L']; [right; exact L'|].
    exfalso. apply (HBD (Z.max bp dp)); [lia|]. right. right. right. lia. }
Qed.

Lemma cls_fx_rng : cls_rng (LCK.RNG_W (world segs) (@w_H segs) W) (spZ regs - 144) dp bp len.
Proof.
  pose proof cls_fx_stk as (HAR & Hwin & Hce & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  pose proof HDR as (_ & _ & Dh & Dm & D0 & D63).
  pose proof cls_fx_bp as Hb.
  pose proof HSC as [HZq HZc].
  unfold cls_rng.
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. exact (proj1 (Hwin b ltac:(lia))). }
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. apply (decode_vis_seg W).
    apply (decode_covers_img 671888 8 b); [decode_seg | lia]. }
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. apply (decode_vis_seg W).
    apply (decode_covers_img 707064 8 b); [decode_seg | lia]. }
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. exact (proj1 (proj2 (cls_fx_dp b Hr))). }
  split.
  { pose proof (Z.div_pos dp 8 ltac:(lia) ltac:(lia)).
    apply (decode_rng W); [lia | lia |]. intros b Hr.
    replace b with ((dp + 0) / 8 + 2147450880) by (rewrite Z.add_0_r; lia).
    apply (cls_vis_av W memc). apply Dh. apply cls_hull_in; lia. }
  split.
  { destruct (Z.eq_dec len 0) as [L0|L0].
    - apply (decode_rng W); [lia | lia |]. intros b Hr. lia.
    - apply (decode_rng W); [lia | lia |]. intros b Hr.
      replace b with (bp + (b - bp)) by lia. apply cls_fx_vis_body. lia. }
  split.
  { intros o Ho. pose proof (cls_fx_body_rd ltac:(lia)) as (_ & _ & Bh & _ & B0 & B63).
    pose proof (Z.div_pos (bp + o) 8 ltac:(lia) ltac:(lia)).
    apply (decode_rng W); [lia | lia |]. intros b Hr.
    replace b with ((bp + o) / 8 + 2147450880) by lia.
    apply (cls_vis_av W memc). apply Bh. apply cls_hull_in; lia. }
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. apply (cls_vis B HGX W b).
    exists TW.OFF_g_cmd, TA_g_cmd, TW.SZ_g_cmd. split; [exact TMAP_A_g_cmd | unfold TA_g_cmd, TW.SZ_g_cmd; lia]. }
  split.
  { destruct (decode_zshadow_ra B lyc Sc W memc mdc TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) 6181888 40960 HAR HZc
                ltac:(lia) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as [_ Hh].
    assert (E1 : YG0f.shadow_addr 6181888 / 8 * 8 = 2148223616) by reflexivity.
    assert (E2 : YG0f.shadow_addr (6181888 + 40960 - 1) / 8 * 8 + 8 = 2148228736) by reflexivity.
    apply (decode_rng W); [lia | lia |]. intros b Hr.
    apply (cls_vis_av W memc). apply Hh. rewrite E1, E2. lia. }
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. apply (cls_vis B HGX W b).
    exists TW.OFF_g_q, TA_g_q, TW.SZ_g_q. split; [exact TMAP_A_g_q | unfold TA_g_q, TW.SZ_g_q; lia]. }
  split.
  { destruct (decode_zshadow_ra B lyc Sc W memc mdc TA_g_q (TA_g_q + TW.SZ_g_q) 6233088 4096 HAR HZq
                ltac:(lia) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as [_ Hh].
    assert (E1 : YG0f.shadow_addr 6233088 / 8 * 8 = 2148230016) by reflexivity.
    assert (E2 : YG0f.shadow_addr (6233088 + 4096 - 1) / 8 * 8 + 8 = 2148230528) by reflexivity.
    apply (decode_rng W); [lia | lia |]. intros b Hr.
    apply (cls_vis_av W memc). apply Hh. rewrite E1, E2. lia. }
  split.
  { apply (decode_rng W); [lia | lia |]. intros b Hr. apply (cls_vis B HGX W b).
    exists TW.OFF_g_nq, TA_g_nq, TW.SZ_g_nq. split; [exact TMAP_A_g_nq | unfold TA_g_nq, TW.SZ_g_nq; lia]. }
  { apply (decode_rng W); [lia | lia |]. intros b Hr. apply (cls_vis B HGX W b).
    exists TW.OFF_g_ncmd, TA_g_ncmd, TW.SZ_g_ncmd. split; [exact TMAP_A_g_ncmd | unfold TA_g_ncmd, TW.SZ_g_ncmd; lia]. }
Qed.

(* ---- the invariants ---- *)

(* the G journal of the caller, at the walk's memory m *)
Definition cls_J (m : word -> option byte) (md : Model) : Prop :=
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W m md k.
(* presence grows from the call's memory *)
Definition cls_GA (m : word -> option byte) : Prop :=
  forall a, apresent (w_H W) memc a -> apresent (w_H W) m a.
(* every byte outside the call's window and outside the ranges the runs may store into keeps its view *)
Definition cls_KA (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CLS_STK <= a < spZ regs) -> ~ cls_wrange dp a ->
    aview segs (w_H W) m a = aview segs (w_H W) memc a.

Lemma cls_KA_sh : forall m, cls_KA m -> forall s, kLowMemEnd <= s < kHighShadowEnd ->
  aview segs (w_H W) m s = aview segs (w_H W) memc s.
Proof.
  intros m KAm s Hs. pose proof cls_fx_stk as (_ & _ & Hce & _).
  pose proof asan_consts as (C1 & _).
  pose proof HDR as (_ & _ & _ & Hm & _ & _).
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm.
  unfold kLowMemEnd, kHighShadowEnd in Hs.
  assert (CS : CLS_STK = 8336) by reflexivity.
  apply KAm; [lia | lia |]. intros Hw. unfold cls_wrange in Hw. lia.
Qed.

Lemma cls_ra_KA : forall m, cls_KA m -> forall q n,
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF q n -> amem_range q n -> 0 <= q ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF q n.
Proof.
  intros m KAm q n HRA Hm Hq x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite (cls_KA_sh m KAm); [exact Hs|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *.
  unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd. lia.
Qed.

Lemma cls_addr_G : forall m md, AR segs B lyc Sc W m md ->
  addressable m 6181888 40960 /\ addressable m 6233088 4096.
Proof.
  intros m md HARm. pose proof HSC as [HZq HZc]. split.
  - destruct (decode_zshadow_ra B lyc Sc W m md TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) 6181888 40960 HARm HZc
                ltac:(lia) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as [HRA _].
    apply (cls_addressable W m 6181888 40960 HRA); [lia | lia | unfold amem_range, kLowMemEnd; lia].
  - destruct (decode_zshadow_ra B lyc Sc W m md TA_g_q (TA_g_q + TW.SZ_g_q) 6233088 4096 HARm HZq
                ltac:(lia) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as [HRA _].
    apply (cls_addressable W m 6233088 4096 HRA); [lia | lia | unfold amem_range, kLowMemEnd; lia].
Qed.

Lemma cls_addr_KA : forall m, cls_KA m -> addressable m dp 4 /\ addressable m bp len.
Proof.
  intros m KAm. pose proof HDR as (_ & HRA & _ & Hm & D0 & _). split.
  - apply (cls_addressable W m dp 4); [exact (cls_ra_KA m KAm dp 4 HRA Hm D0) | lia | lia | exact Hm].
  - destruct (Z.eq_dec len 0) as [L0|L0].
    + pose proof cls_fx_bp as Hb. split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
      intros i Hi. lia.
    + pose proof (cls_fx_body_rd ltac:(lia)) as (_ & BRA & _ & Bm & B0 & _).
      apply (cls_addressable W m bp len); [exact (cls_ra_KA m KAm bp len BRA Bm B0) | lia | lia | exact Bm].
Qed.

Lemma cls_wok_GA : forall m, cls_GA m -> cls_wok dp m.
Proof.
  intros m GAm a Ha. unfold cls_wrange in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - exact (gx_rw_writable tfibsegs TG.G_HARNESS a G_HARNESS_rw (cls_inG_w a ltac:(lia)) m).
  - exact (gx_rw_writable tfibsegs TG.G_HARNESS a G_HARNESS_rw (cls_inG_w a ltac:(lia)) m).
  - exact (gx_rw_writable tfibsegs TG.G_HARNESS a G_HARNESS_rw (cls_inG_w a ltac:(lia)) m).
  - destruct (GAm a (proj2 (cls_fx_dp a Ha))) as (_ & b & Hb). unfold wview, wa. rewrite Hb. discriminate.
Qed.

Lemma cls_mem_mk : forall m md Bc v,
  tw_at TMAP_A (csw_view m) Bc -> rw_cells rsegs m dp [C4 v] -> cls_body m bp body ->
  AR segs B lyc Sc W m md -> cls_KA m -> cls_GA m -> cls_mem m Bc body dp bp len v.
Proof.
  intros m md Bc v H1 H2 H3 HARm KAm GAm.
  destruct (cls_addr_G m md HARm) as [A1 A2]. destruct (cls_addr_KA m KAm) as [A3 A4].
  exact (conj H1 (conj H2 (conj H3 (conj A1 (conj A2 (conj A3 (conj A4 (cls_wok_GA m GAm)))))))).
Qed.

(* the body and g_cmd's payload, read through the view *)
Lemma cls_body_av : forall m, cls_body m bp body -> forall i, 0 <= i < len ->
  aview segs (w_H W) m (bp + i) = Some (bv_unsigned (nth (Z.to_nat i) body (Z_to_bv 8 0))).
Proof.
  intros m (B0 & B1 & B2) i Hi. rewrite (decode_aview_mrd W m (bp + i) (cls_fx_vis_body i Hi)).
  replace (bp + i) with (bp + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (B2 (Z.to_nat i) ltac:(lia)).
  rewrite (nth_error_nth' body (Z_to_bv 8 0) (ltac:(lia) : (Z.to_nat i < length body)%nat)). reflexivity.
Qed.

Lemma cls_cmd_av : forall m Bc, tw_at TMAP_A (csw_view m) Bc -> forall i, 0 <= i < 40960 ->
  aview segs (w_H W) m (6181888 + i) = Some (bv_unsigned (nth (Z.to_nat (TW.OFF_g_cmd + i)) Bc (Z_to_bv 8 0))).
Proof.
  intros m Bc HTWm i Hi.
  rewrite (cls_view_eq B HGX W m (6181888 + i))
    by (exists TW.OFF_g_cmd, TA_g_cmd, TW.SZ_g_cmd; split; [exact TMAP_A_g_cmd | unfold TA_g_cmd, TW.SZ_g_cmd; lia]).
  destruct HTWm as [_ HT]. exact (HT _ _ _ i TMAP_A_g_cmd ltac:(unfold TW.SZ_g_cmd; lia)).
Qed.

(* the body's decode_rd_ok at a later memory of the walk *)
Lemma cls_rd_body_m : forall m, cls_body m bp body -> cls_KA m -> 0 < len -> decode_rd_ok W m bp len.
Proof.
  intros m HBm KAm Hn. apply (trans_rd_ok_view W W memc m bp len (cls_fx_body_rd Hn)).
  - intros a Ha. replace a with (bp + (a - bp)) by lia.
    rewrite (cls_body_av m HBm (a - bp)) by lia. rewrite (cls_body_av memc cls_fx_cb (a - bp)) by lia.
    reflexivity.
  - intros s Hs. exact (cls_KA_sh m KAm s Hs).
Qed.

(* ---- one footprint run ---- *)

Lemma cls_step_run : forall m m' md md',
  cls_J m md -> cls_GA m -> cls_KA m ->
  munch (cls_W (spZ regs - 144) dp) m m' -> mem_grows m m' -> same_but_materialized md md' ->
  cls_J m' md' /\ cls_GA m' /\ cls_KA m'.
Proof.
  intros m m' md md' HJm GAm KAm MU MG SBM.
  pose proof cls_fx_stk as (HAR & Hwin & Hce & H47 & Hsp0 & HSTK).
  assert (CS : CLS_STK = 8336) by reflexivity.
  assert (Hout : forall a, ~ ((spZ regs - 144 <= a < spZ regs - 144 + 144) \/ cls_wrange dp a) ->
            outside (cls_W (spZ regs - 144) dp) a).
  { intros a Ha. unfold cls_W, cls_wrange in *. cbn [outside].
    repeat split; try exact I; intros Hx; apply Ha; lia. }
  split; [|split].
  - apply (cls_jexec B LAWS HGX STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W m m' md md' k
             (fun a => (spZ regs - 144 <= a < spZ regs - 144 + 144) \/ cls_wrange dp a) HJm).
    + intros z Hz. apply MU. apply Hout. exact Hz.
    + exact MG.
    + exact SBM.
    + intros a [Ha | Ha].
      * left. split; [left; lia | apply GAm, Hwin; lia].
      * unfold cls_wrange in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
        -- right. apply cls_inG_w. lia.
        -- right. apply cls_inG_w. lia.
        -- right. apply cls_inG_w. lia.
        -- left. destruct (cls_fx_dp a Ha) as [Hw Hp]. split; [exact Hw | exact (GAm a Hp)].
  - intros a Ha. destruct (GAm a Ha) as (Hh & b & Hb). split; [exact Hh|].
    destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
    exfalso. apply (MG (Z_to_bv 64 a)); [rewrite Hb; discriminate | exact E].
  - intros a Ha Hw Hr. rewrite <- (KAm a Ha Hw Hr). apply aview_eq_of. unfold mrestrict.
    rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite (MState.unsigned_lit a Ha).
    apply Hout. intros [Hx | Hx]; [apply Hw; lia | exact (Hr Hx)].
Qed.

(* ---- the bcmp call: what its contract keeps ---- *)

Lemma cls_step_bcmp : forall m m2 lo2 hi2, spZ regs - CLS_STK <= lo2 -> hi2 <= spZ regs ->
  cls_GA m -> cls_KA m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo2 <= a < hi2) -> aview segs (w_H W) m2 a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  cls_GA m2 /\ cls_KA m2.
Proof.
  intros m m2 lo2 hi2 Hl Hh GAm KAm KB GB. split.
  - intros a Ha. exact (GB a (GAm a Ha)).
  - intros a Ha Hw Hr. rewrite (KB a Ha ltac:(lia)). exact (KAm a Ha Hw Hr).
Qed.

Lemma cls_frame_bcmp : forall m m2 lo2 hi2 cs, hi2 <= spZ regs - 144 -> cls_GA m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo2 <= a < hi2) -> aview segs (w_H W) m2 a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  Z.of_nat (cells_size cs) <= 144 -> rw_cells rsegs m (spZ regs - 144) cs -> rw_cells rsegs m2 (spZ regs - 144) cs.
Proof.
  intros m m2 lo2 hi2 cs Hh GAm KB GB Hsz FR.
  pose proof cls_fx_stk as (_ & Hwin & Hce & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  apply (decode_frame_ext (spZ regs - 144) 144 cs m m2 Hsz); [|exact FR].
  intros i Hi. unfold wa.
  apply (decode_present_eq W m m2 (spZ regs - 144 + i)).
  - apply GAm, Hwin. lia.
  - apply GB, GAm, Hwin. lia.
  - apply KB; lia.
Qed.

Lemma cls_mem_bcmp : forall m m2 md2 lo2 hi2 Bc v, spZ regs - CLS_STK <= lo2 -> hi2 <= spZ regs ->
  cls_GA m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo2 <= a < hi2) -> aview segs (w_H W) m2 a = aview segs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  cls_GA m2 -> cls_KA m2 -> AR segs B lyc Sc W m2 md2 ->
  cls_mem m Bc body dp bp len v -> cls_mem m2 Bc body dp bp len v.
Proof.
  intros m m2 md2 lo2 hi2 Bc v Hl Hh GAm KB GB GA2 KA2 HAR2 (HTWm & HDPm & HBm & _).
  pose proof cls_fx_stk as (HAR & Hwin & Hce & H47 & _).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  pose proof HDR as (_ & _ & _ & _ & D0 & D63).
  pose proof HDOW as HD. pose proof HOW as HO. unfold decode_off_win in HD, HO.
  pose proof cls_fx_bp as Hb.
  apply (cls_mem_mk m2 md2 Bc v); [ | | | exact HAR2 | exact KA2 | exact GA2].
  - apply (tw_kept TMAP_A (csw_view m) (csw_view m2) Bc HTWm). intros x Hx.
    rewrite <- (cls_view_eq B HGX W m2 x Hx), <- (cls_view_eq B HGX W m x Hx).
    pose proof (TMAP_A_hull x Hx) as Hhull. unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in Hhull.
    apply KB; lia.
  - apply (decode_rw_cells_ext m m2 dp [C4 v]); [|exact HDPm].
    intros i Hi. change (Z.of_nat (cells_size [C4 v])) with 4 in Hi. unfold wa.
    destruct (cls_fx_dp (dp + i) ltac:(lia)) as [_ Hp].
    apply (decode_present_eq W m m2 (dp + i)); [exact (GAm _ Hp) | exact (GB _ (GAm _ Hp)) | apply KB; lia].
  - unfold cls_body in *. destruct HBm as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|].
    intros i Hi. rewrite <- (B2 i Hi). apply (cls_mrd_eq W m m2 (bp + Z.of_nat i)).
    + apply cls_fx_vis_body. lia.
    + apply KB; lia.
Qed.

(* the 4 bytes at dp, as the post reads them *)
Lemma cls_garr8_dp : forall m d, rw_cells rsegs m dp [C4 (Z_to_bv 64 d)] ->
  garr8 segs (mrestrict (w_H W) m) dp (TW.zs (TW.put 4 d)).
Proof.
  intros m d [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. rewrite decode_le4 in HB.
  apply (cls_garr8_of_bytes W m dp (TW.put 4 d)); [exact HB|].
  intros i Hi. unfold TW.put in Hi. rewrite length_Z_to_le_bytes in Hi.
  exact (proj1 (proj2 (cls_fx_dp (dp + Z.of_nat i) ltac:(lia)))).
Qed.

(* ---- the states the runs reach ---- *)

(* the registers the loop head fixes (and those the walk keeps: sp, gp, tp) *)
Definition cls_regsH (R : bvmap 5 word) (pos : Z) : Prop :=
  gr R 2 = Z_to_bv 64 (spZ regs - 144) /\ gr R 3 = gr regs 3 /\ gr R 4 = gr regs 4 /\
  gr R 8 = Z_to_bv 64 dp /\ gr R 9 = Z_to_bv 64 len /\ gr R 21 = Z_to_bv 64 2147450880 /\
  gr R 23 = Z_to_bv 64 pos /\ gr R 24 = Z_to_bv 64 6157680 /\ gr R 26 = Z_to_bv 64 6181888 /\
  gr R 27 = Z_to_bv 64 6157684.

Lemma cls_regsH_eqv : forall R F pc fc rv mm ro ms' pos,
  Regs6ss.ms_eqv (MS R F pc fc rv mm ro) ms' -> cls_regsH R pos -> cls_regsH (ms_regs ms') pos.
Proof.
  intros R F pc fc rv mm ro ms' pos EQV H. unfold cls_regsH in *.
  repeat rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity. exact H.
Qed.

(* the epilogue state, from m0 *)
Definition cls_atE (Bc : list byte) (dv : Z) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists R m' j, ms = MS R (@YK11.fp_regs fx) (Z_to_bv 64 542640) (@YK11.fp_csr fx) None m' (YK11.seg_rom segs) /\
    gr R 2 = Z_to_bv 64 (spZ regs - 144) /\ gr R 3 = gr regs 3 /\ gr R 4 = gr regs 4 /\
    length j = 40%nat /\ rw_cells rsegs m' (spZ regs - 144) (cls_fe j) /\
    cls_mem m' Bc body dp bp len (Z_to_bv 64 dv) /\
    munch (cls_W (spZ regs - 144) dp) m0 m' /\ mem_grows m0 m'.

(* a loop-head state, from m0 *)
Definition cls_atH (Bc : list byte) (pos nqv dv : Z) (m0 : word -> option byte) (ms : machine_state) : Prop :=
  exists R m' j0, ms = MS R (@YK11.fp_regs fx) (Z_to_bv 64 542108) (@YK11.fp_csr fx) None m' (YK11.seg_rom segs) /\
    cls_regsH R pos /\ gr R 25 = Z_to_bv 64 nqv /\
    length j0 = 8%nat /\ rw_cells rsegs m' (spZ regs - 144) (cls_fh j0) /\
    cls_mem m' Bc body dp bp len (Z_to_bv 64 dv) /\
    munch (cls_W (spZ regs - 144) dp) m0 m' /\ mem_grows m0 m'.

(* ---- the epilogue and the post ---- *)

Lemma cls_fin : forall (Rg : bvmap 5 word) m md j,
  gr Rg 2 = Z_to_bv 64 (spZ regs - 144) -> gr Rg 3 = gr regs 3 -> gr Rg 4 = gr regs 4 ->
  length j = 40%nat -> rw_cells rsegs m (spZ regs - 144) (cls_fe j) ->
  cls_J m md -> cls_GA m -> cls_KA m -> cls_PW Bw Bw' ->
  cls_mem m Bw' body dp bp len (Z_to_bv 64 disp) ->
  SRr segs W (mkCfg (YK11.mkst Rg (Z_to_bv 64 542640) m (YK11.seg_rom segs)) md) cls_Q.
Proof.
  intros Rg m md j R2 R3 R4 Hj FR HJm GAm KAm PWm HMm.
  pose proof cls_fx_stk as (HAR & Hwin & Hce & H47 & Hsp0 & HSTK).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  pose proof cls_fx_rng as (RFR & _).
  change (SRr segs W (@cfg_at fx segs 542640 Rg m md) cls_Q).
  eapply (@decode_run fx W Rg m md 542640).
  { unfold LCK.ms_of_regs. rewrite R2, R3, R4.
    eapply (cls_run_epi _ _ m (@YK11.fp_regs fx) (@YK11.fp_csr fx) (spZ regs - 144) j
              (gr regs 1) (gr regs 8) (gr regs 9) (gr regs 18) (gr regs 19) (gr regs 20) (gr regs 21)
              (gr regs 22) (gr regs 23) (gr regs 24) (gr regs 25) (gr regs 26) (gr regs 27)
              (gr Rg 1) (gr Rg 8) (gr Rg 9) (gr Rg 18) (gr Rg 19) (gr Rg 20) (gr Rg 21) (gr Rg 22) (gr Rg 23)
              (gr Rg 24) (gr Rg 25) (gr Rg 26) (gr Rg 27)
              (gr regs 3) (gr regs 4) (gr Rg 5) (gr Rg 6) (gr Rg 7) (gr Rg 10) (gr Rg 11) (gr Rg 12) (gr Rg 13)
              (gr Rg 14) (gr Rg 15) (gr Rg 16) (gr Rg 17) (gr Rg 28) (gr Rg 29) (gr Rg 30) (gr Rg 31)).
    - lia.
    - lia.
    - exact FR.
    - exact RFR.
    - match goal with |- ExecF.evtF _ _ _ ?st => exact (ExecF.evtF_done _ _ (fun ms => ms = st) st eq_refl) end. }
  intros ms' md' (ms0 & Hms0 & EQV) SBM. subst ms0.
  rewrite (decode_ms_shape _ _ _ _ EQV).
  destruct (cls_step_run m m md md' HJm GAm KAm (munch_refl _ _) (mem_grows_refl _) SBM) as (HJ2 & _ & _).
  pose proof HMm as (HTWm & HDPm & _).
  apply SRr_ret. unfold cls_Q, transport_cg_post_out.
  exists lyc, Sc, (ms_regs ms'), m, md', 0.
  split. { rewrite (LeafCgFacts.ret_ok_stmt_YK0s (gr regs 1) Hra). reflexivity. }
  split; [unfold CLS_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJ2|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                 r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
      try cls_reg EQV.
    transitivity (Z_to_bv 64 (spZ regs - 144 + 144)); [cls_reg EQV|].
    replace (spZ regs - 144 + 144) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (cls_close_kept B LAWS HGX lyc Sc W memc mdc m dp (spZ regs - CLS_STK) (spZ regs) HAR);
      [lia | lia | exact Hwin | | exact GAm].
    intros a Ha Hw Hn.
    destruct (Z_le_gt_dec 6181888 a) as [G1|G1]; [destruct (Z_lt_ge_dec a (6181888 + 40960)) as [G2|G2]|].
    - (* a byte of g_cmd's payload outside every st field: the world agrees *)
      assert (Hnst : forall s, 0 <= s < TC.CMDS_MAX ->
                ~ (TW.A_Cmd_st s <= TW.OFF_g_cmd + (a - 6181888) < TW.A_Cmd_st s + 4)).
      { intros s Hs Hin. apply Hn. left. exists s. split; [exact Hs|].
        unfold twa_fld, TW.A_Cmd_st, TW.OFF_g_cmd, TA_g_cmd in *. lia. }
      pose proof (PWm (TW.OFF_g_cmd + (a - 6181888)) ltac:(unfold TW.OFF_g_cmd, TW.SZ_g_cmd; lia) Hnst) as E.
      pose proof (tw_len _ _ _ HTWm) as L1. pose proof (tw_len _ _ _ HTW) as L2.
      replace a with (6181888 + (a - 6181888)) by lia.
      rewrite (cls_cmd_av m Bw' HTWm (a - 6181888) ltac:(lia)).
      pose proof HTW as [_ HT].
      pose proof (HT _ _ _ (a - 6181888) TMAP_A_g_cmd ltac:(unfold TW.SZ_g_cmd; lia)) as HTa.
      change (TA_g_cmd + (a - 6181888)) with (6181888 + (a - 6181888)) in HTa. rewrite HTa.
      rewrite (cls_sub1_nth Bw' Bw (TW.OFF_g_cmd + (a - 6181888)) (Z_to_bv 8 0)); [reflexivity | | | exact E];
        unfold TW.W_LEN, TW.OFF_g_cmd in *; lia.
    - apply KAm; [exact Ha | exact Hw |]. intros Hr. unfold cls_wrange in Hr.
      destruct Hr as [Hr | [Hr | [Hr | Hr]]]; [lia | | |].
      + apply Hn. right. left. unfold twa_fld, TW.OFF_g_q, TA_g_q, TW.SZ_g_q. lia.
      + apply Hn. right. right. left. unfold twa_fld, TW.OFF_g_nq, TA_g_nq, TW.SZ_g_nq. lia.
      + apply Hn. right. right. right. exact Hr.
    - apply KAm; [exact Ha | exact Hw |]. intros Hr. unfold cls_wrange in Hr.
      destruct Hr as [Hr | [Hr | [Hr | Hr]]]; [lia | | |].
      + apply Hn. right. left. unfold twa_fld, TW.OFF_g_q, TA_g_q, TW.SZ_g_q. lia.
      + apply Hn. right. right. left. unfold twa_fld, TW.OFF_g_nq, TA_g_nq, TW.SZ_g_nq. lia.
      + apply Hn. right. right. right. exact Hr. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  split; [exact (cls_tw_av B HGX W m Bw' HTWm) | exact (cls_garr8_dp m disp HDPm)].
Qed.

(* ---- the loop ---- *)

Lemma cls_loop : forall fuel Bc pos dispc m md (regsH : bvmap 5 word) j0,
  TC.latest_sent_loop fuel Bc body len pos dispc = Some (Bw', disp) ->
  0 <= pos < len -> Z.of_nat (length Bc) = TW.W_LEN -> cls_inv_c Bc -> cls_PW Bw Bc ->
  cls_J m md -> cls_GA m -> cls_KA m ->
  cls_mem m Bc body dp bp len (Z_to_bv 64 dispc) ->
  length j0 = 8%nat -> rw_cells rsegs m (spZ regs - 144) (cls_fh j0) ->
  cls_regsH regsH pos ->
  (TW.g_nq Bc < 2 ^ 31 -> gr regsH 25 = Z_to_bv 64 (TW.g_nq Bc)) ->
  SRr segs W (mkCfg (YK11.mkst regsH (Z_to_bv 64 542108) m (YK11.seg_rom segs)) md) cls_Q.
Proof.
  induction fuel as [|fuel IH];
    intros Bc pos dispc m md regsH j0 HL Hpos HLB HIC HPW HJm GAm KAm HMm Hj0 FR HRH HNQ.
  { cbn in HL. discriminate HL. }
  pose proof cls_fx_stk as (HAR & Hwin & Hce & H47 & Hsp0 & HSTK).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  assert (EST : ESTACK = 4096) by reflexivity.
  pose proof cls_fx_bp as Hbl.
  pose proof HOW as HO. unfold decode_off_win in HO.
  destruct (cls_round fuel Bc body len pos dispc Bw' disp HL Hpos Hlen)
    as (s & B2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  assert (F4n : 0 <= s < 1024) by exact F4.
  (* g_nq <= CMDS_MAX: q_remove succeeded *)
  assert (HNQB : 0 <= TW.g_nq Bc <= TC.CMDS_MAX).
  { destruct (cls_qrm _ _ _ F9) as (B1 & kq & HQ & _).
    pose proof (cls_q_nqle _ _ _ _ _ _ _ _ HQ ltac:(unfold TC.CMDS_MAX; lia)) as NQ.
    rewrite (cls_g_nq_set_st Bc s TC.SENT HLB F4) in NQ. pose proof (cls_g_nq_range Bc). lia. }
  assert (E25 : gr regsH 25 = Z_to_bv 64 (TW.g_nq Bc)) by (apply HNQ; unfold TC.CMDS_MAX in HNQB; lia).
  (* the command's length *)
  assert (HCL : TW.Cmd_len Bc s <= 24).
  { change 24 with DSpec.SPEC_CMD_MAX. apply (HIC s); [lia | exact (proj2 F4) | exact F6]. }
  pose proof (cls_cmd_len_range Bc s) as HCLR.
  pose proof HMm as (HTWm & HDPm & HBm & _).
  pose proof HRH as (R2 & R3 & R4 & R8 & R9 & R21 & R23 & R24 & R26 & R27).
  (* ---- the loop head to the bcmp entry ---- *)
  change (SRr segs W (@cfg_at fx segs 542108 regsH m md) cls_Q).
  apply (@decode_run fx W regsH m md 542108
           (fun ms => exists a13 a14 a15 : word,
              ms = MS (cls_regs_call (gr regsH 5) (gr regsH 6) (gr regsH 7) a13 a14 a15 (gr regsH 16) (gr regsH 17)
                         (gr regsH 28) (gr regsH 29) (gr regsH 30) (gr regsH 31) (gr regs 3) (gr regs 4)
                         (spZ regs - 144) dp bp len pos (TW.g_nq Bc) s (TW.Cmd_len Bc s))
                      (@YK11.fp_regs fx) (Z_to_bv 64 273656) (@YK11.fp_csr fx) None m (YK11.seg_rom segs))).
  { unfold LCK.ms_of_regs. rewrite R2, R3, R4, R8, R9, R21, R23, R24, E25, R26, R27.
    refine (cls_run_pre _ _ m (@YK11.fp_regs fx) (@YK11.fp_csr fx) (spZ regs - 144) dp bp len pos (TW.g_nq Bc) s Bc
              body (Z_to_bv 64 dispc) j0
              (gr regs 1) (gr regs 8) (gr regs 9) (gr regs 18) (gr regs 19) (gr regs 20) (gr regs 21)
              (gr regs 22) (gr regs 23) (gr regs 24) (gr regs 25) (gr regs 26) (gr regs 27)
              (gr regsH 1) (gr regsH 5) (gr regsH 6) (gr regsH 7) (gr regsH 10) (gr regsH 11) (gr regsH 12)
              (gr regsH 13) (gr regsH 14) (gr regsH 15) (gr regsH 16) (gr regsH 17) (gr regsH 18) (gr regsH 19)
              (gr regsH 20) (gr regsH 22) (gr regsH 28) (gr regsH 29) (gr regsH 30) (gr regsH 31)
              (gr regs 3) (gr regs 4)
              cls_fx_bounds cls_fx_off cls_fx_rng Hlen HLB (proj1 Hpos) F1 F2 F3 F4 F5 F6 F7 FR Hj0 HMm _).
    intros a13 a14 a15. apply ExecF.evtF_done. exists a13, a14, a15. reflexivity. }
  intros ms1 md1 (ms0 & (a13 & a14 & a15 & Hms0) & EQV1) SBM1. subst ms0.
  rewrite (decode_ms_shape _ _ _ _ EQV1).
  destruct (cls_step_run m m md md1 HJm GAm KAm (munch_refl _ _) (mem_grows_refl _) SBM1) as (HJ1 & _ & _).
  set (RT := ms_regs ms1).
  assert (T1 : gr RT 1 = Z_to_bv 64 542300) by cls_reg EQV1.
  assert (T2 : gr RT 2 = Z_to_bv 64 (spZ regs - 144)) by cls_reg EQV1.
  assert (T3 : gr RT 3 = gr regs 3) by cls_reg EQV1.
  assert (T4 : gr RT 4 = gr regs 4) by cls_reg EQV1.
  assert (T8 : gr RT 8 = Z_to_bv 64 dp) by cls_reg EQV1.
  assert (T9 : gr RT 9 = Z_to_bv 64 len) by cls_reg EQV1.
  assert (T10 : gr RT 10 = Z_to_bv 64 (bp + pos)) by cls_reg EQV1.
  assert (T11 : gr RT 11 = Z_to_bv 64 (6181888 + 40 * s + 12)) by cls_reg EQV1.
  assert (T12 : gr RT 12 = Z_to_bv 64 (TW.Cmd_len Bc s)) by cls_reg EQV1.
  assert (T18 : gr RT 18 = Z_to_bv 64 s) by cls_reg EQV1.
  assert (T19 : gr RT 19 = Z_to_bv 64 (6181888 + 40 * s)) by cls_reg EQV1.
  assert (T20 : gr RT 20 = Z_to_bv 64 (TW.Cmd_len Bc s)) by cls_reg EQV1.
  assert (T21 : gr RT 21 = Z_to_bv 64 2147450880) by cls_reg EQV1.
  assert (T22 : gr RT 22 = Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880)) by cls_reg EQV1.
  assert (T23 : gr RT 23 = Z_to_bv 64 pos) by cls_reg EQV1.
  assert (T24 : gr RT 24 = Z_to_bv 64 6157680) by cls_reg EQV1.
  assert (T25 : gr RT 25 = Z_to_bv 64 (TW.g_nq Bc)) by cls_reg EQV1.
  assert (T26 : gr RT 26 = Z_to_bv 64 6181888) by cls_reg EQV1.
  assert (T27 : gr RT 27 = Z_to_bv 64 6157684) by cls_reg EQV1.
  assert (TSP : spZ RT = spZ regs - 144).
  { change (spZ RT) with (bv_unsigned (gr RT 2)). rewrite T2, MState.unsigned_lit by lia. reflexivity. }
  (* the two ranges bcmp compares *)
  pose proof (trans_rd_ok_sub W m bp len (bp + pos) (TW.Cmd_len Bc s)
                (cls_rd_body_m m HBm KAm ltac:(lia)) ltac:(lia) ltac:(lia) ltac:(lia))
    as (Xv & Xra & Xh & Xm & X0 & X63).
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
  assert (YRA : range_addressable (aview segs (w_H W) m) SHADOW_OFF (6181888 + 40 * s + 12) (TW.Cmd_len Bc s) /\
                (0 < TW.Cmd_len Bc s ->
                 shadow_hull_vis (aview segs (w_H W) m) (6181888 + 40 * s + 12) (TW.Cmd_len Bc s))).
  { destruct (Z.eq_dec (TW.Cmd_len Bc s) 0) as [N0|N0].
    - split; [intros x Hx; lia | intros Hn; lia].
    - pose proof HSC as [_ HZc].
      destruct (decode_zshadow_ra B lyc Sc W m md1 TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) (6181888 + 40 * s + 12)
                  (TW.Cmd_len Bc s) HAR1 HZc ltac:(lia)) as [YA YH].
      + unfold TA_g_cmd. unfold TC.CMDS_MAX in F4.
        pose proof (Z.div_le_mono 6181888 (6181888 + 40 * s + 12) 64 ltac:(lia) ltac:(lia)) as D.
        change (6181888 / 64) with 96592 in D. lia.
      + unfold TA_g_cmd, TW.SZ_g_cmd. unfold TC.CMDS_MAX in F4.
        pose proof (Z.div_le_mono (6181888 + 40 * s + 12 + TW.Cmd_len Bc s - 1) 6222847 64 ltac:(lia) ltac:(lia)) as D.
        change (6222847 / 64) with 97231 in D. lia.
      + split; [exact YA | intros _; exact YH]. }
  (* ---- the bcmp call ---- *)
  replace (Z_to_bv 64 273656) with (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp))
    by (f_equal; vm_compute; reflexivity).
  eapply SRr_bind.
  { apply (cls_bcmp B LAWS STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W m md1 k RT (bp + pos) (6181888 + 40 * s + 12)
             (TW.Cmd_len Bc s) (spZ regs - 144 - sp0) (Z_to_bv 64 542300) (HBC fx) HJ1 T10 T11 T12).
    - unfold TC.CMDS_MAX in *. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite TSP. lia.
    - apply Z.mod_divide; [lia|].
      destruct (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hsp16) as [a Ha].
      destruct (proj1 (Z.mod_divide _ 16 ltac:(lia)) Hsp0) as [b Hb'].
      exists (a - 9 - b). lia.
    - lia.
    - lia.
    - change (gr RT 3 = w64 (as_gp B)). rewrite T3. exact Hgp.
    - change (gr RT 4 = w64 (as_tp B)). rewrite T4. exact Htp.
    - exact T1.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [exact (Xv a Ha) | rewrite TSP; lia].
    - intros a Ha. split; [|rewrite TSP; lia].
      replace a with (6181888 + (a - 6181888)) by lia.
      rewrite (cls_cmd_av m Bc HTWm (a - 6181888) ltac:(unfold TC.CMDS_MAX in *; lia)). discriminate.
    - intros a Ha. lia.
    - intros a Ha. lia.
    - exact Xm.
    - unfold amem_range, kLowMemEnd. unfold TC.CMDS_MAX in *. lia.
    - exact Xra.
    - intros _. exact Xh.
    - exact (proj1 YRA).
    - exact (proj2 YRA). }
  cbv beta. intros W2 c2 _ (EW & regs2 & mem2 & md2 & Hc2 & HJ2 & v & HP2 & H10v & Hcmp & KB & GB).
  subst W2 c2.
  (* the bytes agree: a0 = 0 *)
  assert (Hv0 : v = w64 0).
  { apply Hcmp. intros i Hi.
    replace (bp + pos + i) with (bp + (pos + i)) by lia.
    replace (6181888 + 40 * s + 12 + i) with (6181888 + (40 * s + 12 + i)) by lia.
    rewrite (cls_body_av m HBm (pos + i)) by lia.
    rewrite (cls_cmd_av m Bc HTWm (40 * s + 12 + i)) by (unfold TC.CMDS_MAX in *; lia).
    do 2 f_equal.
    transitivity (nth (Z.to_nat i) (TW.sub body pos (Z.to_nat (TW.Cmd_len Bc s))) (Z_to_bv 8 0)).
    { rewrite cls_nth_sub by lia. f_equal. lia. }
    rewrite F8. rewrite cls_nth_sub by (unfold TW.A_Cmd_bytes, TW.OFF_g_cmd; lia).
    f_equal. unfold TW.A_Cmd_bytes, TW.OFF_g_cmd. lia. }
  rewrite Hv0 in H10v.
  (* the invariants at the bcmp return *)
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  destruct (cls_step_bcmp m mem2 (sp0 + (spZ regs - 144 - sp0) - 2 * ESTACK) (sp0 + (spZ regs - 144 - sp0))
              ltac:(lia) ltac:(lia) GAm KAm KB GB) as [GA2 KA2].
  pose proof (cls_frame_bcmp m mem2 (sp0 + (spZ regs - 144 - sp0) - 2 * ESTACK) (sp0 + (spZ regs - 144 - sp0))
                (cls_fh j0) ltac:(lia) GAm KB GB
                ltac:(unfold cls_fh, cls_fr; cbn [cells_size csize]; lia) FR) as FR2.
  pose proof (cls_mem_bcmp m mem2 md2 (sp0 + (spZ regs - 144 - sp0) - 2 * ESTACK) (sp0 + (spZ regs - 144 - sp0))
                Bc (Z_to_bv 64 dispc) ltac:(lia) ltac:(lia) GAm KB GB GA2 KA2 HAR2 HMm) as HM2.
  assert (STK2 : stk rsegs mem2 (spZ regs - CLS_STK) (spZ regs - 144)).
  { apply (cls_stk_present (w_H W) mem2); [lia | lia |]. intros a Ha. apply GA2, Hwin. lia. }
  (* the registers at the bcmp return *)
  assert (U2 : gr regs2 2 = Z_to_bv 64 (spZ regs - 144))
    by (transitivity (gr RT 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact T2]).
  assert (U3 : gr regs2 3 = gr regs 3)
    by (transitivity (gr RT 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact T3]).
  assert (U4 : gr regs2 4 = gr regs 4)
    by (transitivity (gr RT 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact T4]).
  assert (U8 : gr regs2 8 = Z_to_bv 64 dp)
    by (transitivity (gr RT 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact T8]).
  assert (U9 : gr regs2 9 = Z_to_bv 64 len)
    by (transitivity (gr RT 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact T9]).
  assert (U10 : gr regs2 10 = Z_to_bv 64 0) by exact H10v.
  assert (U18 : gr regs2 18 = Z_to_bv 64 s)
    by (transitivity (gr RT 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact T18]).
  assert (U19 : gr regs2 19 = Z_to_bv 64 (6181888 + 40 * s))
    by (transitivity (gr RT 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact T19]).
  assert (U20 : gr regs2 20 = Z_to_bv 64 (TW.Cmd_len Bc s))
    by (transitivity (gr RT 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact T20]).
  assert (U21 : gr regs2 21 = Z_to_bv 64 2147450880)
    by (transitivity (gr RT 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact T21]).
  assert (U22 : gr regs2 22 = Z_to_bv 64 ((6181888 + 40 * s) / 8 + 2147450880))
    by (transitivity (gr RT 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact T22]).
  assert (U23 : gr regs2 23 = Z_to_bv 64 pos)
    by (transitivity (gr RT 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact T23]).
  assert (U24 : gr regs2 24 = Z_to_bv 64 6157680)
    by (transitivity (gr RT 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact T24]).
  assert (U25 : gr regs2 25 = Z_to_bv 64 (TW.g_nq Bc))
    by (transitivity (gr RT 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact T25]).
  assert (U26 : gr regs2 26 = Z_to_bv 64 6181888)
    by (transitivity (gr RT 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact T26]).
  assert (U27 : gr regs2 27 = Z_to_bv 64 6157684)
    by (transitivity (gr RT 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact T27]).
  (* ---- the bcmp return to the next loop head or the epilogue ---- *)
  change (SRr segs W (@cfg_at fx segs 542300 regs2 mem2 md2) cls_Q).
  apply (@decode_run fx W regs2 mem2 md2 542300
           (fun ms => (cls_atE B2 (Z.lor dispc (TW.Cmd_display B2 s)) mem2 ms /\ len <= pos + TW.Cmd_len Bc s) \/
                      (cls_atH B2 (pos + TW.Cmd_len Bc s) (TW.g_nq B2) (Z.lor dispc (TW.Cmd_display B2 s)) mem2 ms /\
                       pos + TW.Cmd_len Bc s < len))).
  { unfold LCK.ms_of_regs.
    rewrite U2, U3, U4, U8, U9, U10, U18, U19, U20, U21, U22, U23, U24, U25, U26, U27.
    refine (cls_run_post _ _ mem2 (@YK11.fp_regs fx) (@YK11.fp_csr fx) (spZ regs - CLS_STK) (spZ regs - 144) dp bp
              len pos s dispc Bc B2 body j0
              (gr regs 1) (gr regs 8) (gr regs 9) (gr regs 18) (gr regs 19) (gr regs 20) (gr regs 21)
              (gr regs 22) (gr regs 23) (gr regs 24) (gr regs 25) (gr regs 26) (gr regs 27)
              (gr regs2 1) (gr regs2 5) (gr regs2 6) (gr regs2 7) (gr regs2 11) (gr regs2 12) (gr regs2 13)
              (gr regs2 14) (gr regs2 15) (gr regs2 16) (gr regs2 17) (gr regs2 28) (gr regs2 29) (gr regs2 30)
              (gr regs2 31) (gr regs 3) (gr regs 4)
              cls_fx_bounds cls_fx_app_sp cls_fx_app_dp cls_fx_off cls_fx_rng Hlen HLB (proj1 Hpos) F1 HNQB F4 F7 F9
              STK2 ltac:(lia) FR2 Hj0 HM2 _ _).
    - intros m' j y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17
        z28 z29 z30 z31 Hj FR' _ HM' MU' _ MG' Hle.
      apply ExecF.evtF_done. left. split; [|exact Hle].
      eexists. exists m', j.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hj|]. split; [exact FR'|]. split; [exact HM'|]. split; [exact MU' | exact MG'].
    - intros m' j0' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y22 y28 y29 y30 y31
        Hj0' FR' _ HM' MU' _ MG' Hlt.
      apply ExecF.evtF_done. right. split; [|exact Hlt].
      eexists. exists m', j0'.
      split; [reflexivity|].
      split; [unfold cls_regsH; repeat (split; [reflexivity|]); reflexivity|].
      split; [reflexivity|].
      split; [exact Hj0'|]. split; [exact FR'|]. split; [exact HM'|]. split; [exact MU' | exact MG']. }
  intros ms3 md3 (ms0 & HP3 & EQV3) SBM3.
  pose proof (cls_round_gen (cls_PW Bw) (cls_PW_q Bw) (cls_PW_nq Bw) (cls_PW_st Bw) Bc s B2 HLB HPW F4 F9)
    as (_ & PW2 & _).
  destruct HP3 as [((R & m' & j & Hms & E2 & E3 & E4 & Hj & FR' & HM' & MU' & MG') & Hle) |
                   ((R & m' & j0' & Hms & HRH' & E25' & Hj0' & FR' & HM' & MU' & MG') & Hlt)];
    subst ms0; rewrite (decode_ms_shape _ _ _ _ EQV3);
    destruct (cls_step_run mem2 m' md2 md3 HJ2 GA2 KA2 MU' MG' SBM3) as (HJ3 & GA3 & KA3).
  - (* the exit: the model's loop ends here too *)
    destruct (cls_exit fuel B2 body len (pos + TW.Cmd_len Bc s) (Z.lor dispc (TW.Cmd_display B2 s)) Bw' disp F10 Hle)
      as [EB ED].
    rewrite <- EB in HM', PW2.
    replace (Z_to_bv 64 (Z.lor dispc (TW.Cmd_display Bw' s))) with (Z_to_bv 64 disp) in HM'
      by (rewrite ED, EB; reflexivity).
    apply (cls_fin (ms_regs ms3) m' md3 j); [ | | | exact Hj | exact FR' | exact HJ3 | exact GA3 | exact KA3
                                             | exact PW2 | exact HM'].
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV3) by reflexivity. exact E2.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV3) by reflexivity. exact E3.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV3) by reflexivity. exact E4.
  - (* the next round *)
    destruct (cls_round_inv_c Bc s B2 HLB HIC F4 F9) as (L2 & I2 & _).
    apply (IH B2 (pos + TW.Cmd_len Bc s) (Z.lor dispc (TW.Cmd_display B2 s)) m' md3 (ms_regs ms3) j0' F10
             ltac:(lia) L2 I2 PW2 HJ3 GA3 KA3 HM' Hj0' FR' (cls_regsH_eqv _ _ _ _ _ _ _ _ _ EQV3 HRH')).
    intros _. rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV3) by reflexivity. exact E25'.
Qed.

(* ---- the walk ---- *)

Lemma cls_main : SRr segs W (@cfg_at fx segs (transport_sigma TS_check_latest_sent) regs memc mdc) cls_Q.
Proof using All.
  pose proof cls_fx_stk as (HAR & Hwin & Hce & H47 & Hsp0 & HSTK).
  pose proof asan_consts as (C1 & _).
  assert (CS : CLS_STK = 8336) by reflexivity.
  pose proof HDR as (_ & _ & _ & _ & D0 & D63).
  replace (transport_sigma TS_check_latest_sent) with 541952 by (vm_compute; reflexivity).
  assert (E2 : gr regs 2 = Z_to_bv 64 (spZ regs)) by (unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E10 : gr regs 10 = Z_to_bv 64 bp) by exact H10.
  assert (E11 : gr regs 11 = Z_to_bv 64 len) by exact H11.
  assert (E12 : gr regs 12 = Z_to_bv 64 dp) by exact H12.
  (* the caller's int at dp, as a C4 cell of the four bytes there *)
  destruct (proj2 (proj2 (cls_fx_dp (dp + Z.of_nat 0) ltac:(lia)))) as [b0 Hb0].
  destruct (proj2 (proj2 (cls_fx_dp (dp + Z.of_nat 1) ltac:(lia)))) as [b1 Hb1].
  destruct (proj2 (proj2 (cls_fx_dp (dp + Z.of_nat 2) ltac:(lia)))) as [b2 Hb2].
  destruct (proj2 (proj2 (cls_fx_dp (dp + Z.of_nat 3) ltac:(lia)))) as [b3 Hb3].
  pose proof (cls_rw_c4 memc dp b0 b1 b2 b3 D0 ltac:(lia) Hb0 Hb1 Hb2 Hb3) as HDP0.
  assert (HM0 : cls_mem memc Bw body dp bp len (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])))
    by exact (cls_mem_mk memc mdc Bw _ (cls_tw_raw B HGX W memc Bw HTW) HDP0 cls_fx_cb HAR
                (fun a _ _ _ => eq_refl) (fun a H => H)).
  apply (@decode_run fx W regs memc mdc 541952
           (fun ms => (cls_atE Bw 0 memc ms /\ len = 0) \/
                      (cls_atH Bw 0 (TW.s32_at Bw TW.OFF_g_nq) 0 memc ms /\ 0 < len))).
  { unfold LCK.ms_of_regs. rewrite E2, E10, E11, E12.
    refine (cls_run_entry _ _ memc (@YK11.fp_regs fx) (@YK11.fp_csr fx) (spZ regs - CLS_STK) (spZ regs) bp len dp
              Bw body (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3]))
              (gr regs 1) (gr regs 3) (gr regs 4) (gr regs 5) (gr regs 6) (gr regs 7) (gr regs 8) (gr regs 9)
              (gr regs 13) (gr regs 14) (gr regs 15) (gr regs 16) (gr regs 17) (gr regs 18) (gr regs 19)
              (gr regs 20) (gr regs 21) (gr regs 22) (gr regs 23) (gr regs 24) (gr regs 25) (gr regs 26)
              (gr regs 27) (gr regs 28) (gr regs 29) (gr regs 30) (gr regs 31)
              cls_fx_bounds cls_fx_app_sp cls_fx_app_dp cls_fx_off cls_fx_rng Hlen ltac:(lia) _
              (decode_cells_asan B HCELLS lyc Sc W memc mdc (w_Hoff W) HAR) HM0 _ _).
    - apply (cls_stk_present (w_H W) memc); [lia | lia |]. intros a Ha. apply Hwin. lia.
    - intros m' j x10 x11 Hj FR _ HM' MU _ MG Hl0.
      apply ExecF.evtF_done. left. split; [|exact Hl0].
      eexists. exists m', j.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hj|]. split; [exact FR|]. split; [exact HM'|]. split; [exact MU | exact MG].
    - intros m' j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31
        Hj0 FR _ HM' MU _ MG Hlp.
      apply ExecF.evtF_done. right. split; [|exact Hlp].
      eexists. exists m', j0.
      split; [reflexivity|].
      split; [unfold cls_regsH; repeat (split; [reflexivity|]); reflexivity|].
      split; [reflexivity|].
      split; [exact Hj0|]. split; [exact FR|]. split; [exact HM'|]. split; [exact MU | exact MG]. }
  intros ms1 md1 (ms0 & HP & EQV) SBM.
  destruct HP as [((R & m' & j & Hms & R2 & R3 & R4 & Hj & FR & HM' & MU & MG) & Hl0) |
                  ((R & m' & j0 & Hms & HRH & R25 & Hj0 & FR & HM' & MU & MG) & Hlp)];
    subst ms0; rewrite (decode_ms_shape _ _ _ _ EQV);
    destruct (cls_step_run memc m' mdc md1 HJ (fun a H => H) (fun a _ _ _ => eq_refl) MU MG SBM)
      as (HJ1 & GA1 & KA1).
  - (* len = 0: the model returns Bw and 0 *)
    destruct (cls_exit _ _ _ _ _ _ _ _ (cls_start _ _ _ _ _ HM) ltac:(lia)) as [EB ED].
    rewrite <- EB in HM'.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 disp) in HM' by (rewrite ED; reflexivity).
    apply (cls_fin (ms_regs ms1) m' md1 j); [ | | | exact Hj | exact FR | exact HJ1 | exact GA1 | exact KA1
                                             | | exact HM'].
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity. exact R2.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity. exact R3.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity. exact R4.
    + intros jj _ _. rewrite EB. reflexivity.
  - (* the loop *)
    assert (HLB : Z.of_nat (length Bw) = TW.W_LEN).
    { rewrite (tw_len _ _ _ HTW). rewrite Z2Nat.id; [reflexivity | unfold TW.W_LEN; lia]. }
    apply (cls_loop (Nat.succ (Z.to_nat len)) Bw 0 0 m' md1 (ms_regs ms1) j0 (cls_start _ _ _ _ _ HM)
             ltac:(lia) HLB (cls_inv_to_c Bw HINV) (fun jj _ _ => eq_refl) HJ1 GA1 KA1 HM' Hj0 FR
             (cls_regsH_eqv _ _ _ _ _ _ _ _ _ EQV HRH)).
    intros Hlt. rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity. rewrite R25.
    f_equal. unfold TW.g_nq. apply cls_s32_small. exact Hlt.
Qed.

End clsw.

(* The statement of lib/A/Prog/check_latest_sent_cg.v. *)
Theorem transport_check_latest_sent_cg_holds :
  forall fx rc B MT, @transport_check_latest_sent_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT. unfold transport_check_latest_sent_cg_holds_stmt.
  intros HCELLS HSC LAWS MTL HGX HBC. unfold transport_check_latest_sent_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs bp len dp disp body Bw Bw'
    HJ Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hbp Hlen HG8 HSRC HOW HBD Hdp4 HTWR HDR HDOW HDG HTW HM HINV Hev.
  exact (@cls_main fx rc B MT HCELLS HSC LAWS MTL HGX HBC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
           bp len dp disp body Bw Bw' HJ Hra Hra4 Hgp Htp H10 H11 H12 Hsp16 Hlo Hhi Hbp Hlen HG8 HSRC HOW HBD Hdp4
           HTWR HDR HDOW HDG HTW HM HINV Hev).
Qed.

Print Assumptions transport_check_latest_sent_cg_holds.
