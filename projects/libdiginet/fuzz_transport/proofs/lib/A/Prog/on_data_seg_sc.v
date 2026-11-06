(* on_data_seg_sc: the piece sc of the image-A walk of on_data (the cuts of lib/A/Prog/on_data_seg_cut.v): the call of
   send_control (lib/A/Prog/send_control_cg.v transport_send_control_cg at transport_sigma TS_send_control, a G-form
   callee composed in the caller's G journal) from its entry, the cut od_sc_at, to its return at +0x16c, the cut
   od_r1_at. No instruction runs: the cut is at the callee's entry, and the callee's post is at the return address.
   The callee's premises, from the cut's state:
     the journal of od_sc_cur (the own frame live, own' = (ONDATA_CID, pos) :: own, at k + 0 = k); ra = BASE + OD_R1
     (ret_ok, 4096 <= ra); gp / tp, a0 = s, a1 = 0xa0 = DIGINET_CMD_ACK, a2 = the sign extension of fr_send b
     (0 <= fr_send b < 2 ^ 32: DgnSpec.v be32_range), a3 = kp = 0, a4 = klp = 0 (od_regs_sc); sp = sp1, the realigned
     sp: 32-aligned, sp - 176 <= sp1 <= sp - 160 (the entry sp is 16-aligned), so sp0 - STK <= sp1 - SENDCTL_STK
     (ONDATA_STK = 176 + SENDCTL_STK, on_data_cg.v ondata_stk_eq) and sp1 <= sp0; tw_at at Bw (od_sc_cur); g_fail_next
     Bw <= 1 and the run invariants (1) and (4) (od_pre); the model call send_control_m timg_A TF Bw DIGINET_CMD_ACK
     (fr_send b) = Some (B1, (r, f)) from on_data_m (on_data_cg.v ondata_model; the None case contradicts on_data_m's
     result); trans_rom_view_rd at the call memory (od_pre's at memc, and the cut's acall_kept_g image clause keeps
     each TRANS_RO_RD byte: an image byte below G_HARNESS_LO, not owned, not errno: DgnTransportCg.v trans_ro_img,
     trans_ro_rd_bounds, trans_ro_rd_scoped); count_cid 2 (frames S2) = count_cid 2 (frames Sc) + 1; st_nev
     (ONDATA_EV = SENDCTL_EV + NOTICE_EV, NOTICE_EV = 0).
   Its post: transport_sendctl_post at kp = 0 is TransportGCg.v transport_cg_post_out over sendctl_outs 0 0 = [], so
   transport_cg_post (transport_cg_post_out_nil). It gives od_r1_cur at the return state (ly3, S3, W2, mem3, md3, e):
   the journal at k + e, 0 <= e <= SENDCTL_EV <= ONDATA_EV, frames S3 = frames S2, the blocks by transitivity, ly_F of
   both journals' layout_le, the meter by mle_station; the cut's acall_kept_g composed with the callee's
   (TransportGCg.v dk_kept_trans_nf_g, NF = dkg_nf of the own frame, apart by dkg_nf_sep; sendctl_wr 0 0 is a part of
   ondata_wr Bw b); the 13 saved words (in [sp - 104, sp), above sp1, so outside the callee's window
   [sp1 - SENDCTL_STK, sp1) and at or above alloc_ceiling: the callee's first kept clause); the frame's last word at
   F + 248 (a byte of the own frame, a frame of frames S2, and not a byte of sendctl_wr 0 0, each of which is a byte of
   G, so an image byte: the callee's frame clause); X: a0 = r, tw_at at B1, g_fail_next B1 <= 1. The registers:
   od_regs_s, s6, s7 and s8 callee-saved (aregs_preserved), a0 = r. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require DgnTransportPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_frame_is_keepalive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_data_cg on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- arithmetic of the call ---- *)

(* The realigned sp: sp1 = (sp - 160) & -32 with sp 16-aligned lies in [sp - 176, sp - 160]; with the journal's
   window it gives send_control's stack premises and the window inclusion of the kept facts. *)
Lemma odsc_arith : forall spr sp0 STK ce sp1 : Z,
  0 <= spr < 2 ^ 64 -> spr mod 16 = 0 -> 0x7fff7f800000 <= ce -> ce <= sp0 - STK ->
  sp0 - STK <= spr - ONDATA_STK -> spr <= sp0 -> sp1 = 32 * ((spr - ONDATA_FRAME) / 32) ->
  0 <= sp1 < 2 ^ 64 /\ sp1 mod 16 = 0 /\ sp0 - STK <= sp1 - SENDCTL_STK /\ sp1 <= sp0 /\
  ce <= spr - ONDATA_STK /\ spr - ONDATA_STK <= sp1 - SENDCTL_STK /\ sp1 + 160 <= spr /\ 104 <= ONDATA_STK.
Proof.
intros spr sp0 STK ce sp1 H1 H2 H3 H4 H5 H6 H7.
assert (EO : ONDATA_STK = 8816) by (vm_compute; reflexivity).
assert (ES : SENDCTL_STK = 8640) by (vm_compute; reflexivity).
rewrite EO in H5 |- *. rewrite ES. unfold ONDATA_FRAME in H7. subst sp1.
repeat split; lia.
Qed.

(* The return address. *)
Lemma odsc_r1_rng : 0 <= OD_R1 < 2 ^ 40 /\ OD_R1 mod 2 = 0.
Proof. unfold OD_R1, AF_on_data. split; [lia | reflexivity]. Qed.

(* cmd = DIGINET_CMD_ACK fits in a byte. *)
Lemma odsc_cmd : 0 <= TS0.DIGINET_CMD_ACK < 2 ^ 8.
Proof. unfold TS0.DIGINET_CMD_ACK. lia. Qed.

(* The class-2 count at the call state: the own frame on top of the call's frames. *)
Lemma odsc_cnt : forall (l : list (Z * Z)) (pos : Z),
  count_cid ONDATA_CID l + 2 < fs_frames ONDATA_CID ->
  count_cid SENDCTL_CID ((ONDATA_CID, pos) :: l) + 1 < fs_frames SENDCTL_CID.
Proof.
intros l pos H. change SENDCTL_CID with ONDATA_CID. cbn [count_cid]. rewrite Z.eqb_refl. lia.
Qed.

(* The event budget: ONDATA_EV = SENDCTL_EV + NOTICE_EV, NOTICE_EV = 0. *)
Lemma odsc_nev : forall x, x + ONDATA_EV <= EV_MAX -> x + SENDCTL_EV <= EV_MAX.
Proof. intros x H. unfold ONDATA_EV, NOTICE_EV in H. lia. Qed.

Lemma odsc_ev : forall e, 0 <= e <= SENDCTL_EV -> 0 <= e <= ONDATA_EV.
Proof. intros e H. unfold ONDATA_EV, NOTICE_EV. lia. Qed.

(* ---- the bytes send_control writes are bytes of G ---- *)

Lemma odsc_row_inG : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Ltac odsc_num :=
  unfold TW.A_S_stats_tx_frames, TW.A_GOT_e2, TW.A_GOT_e3, TW.A_GOT_acks, TW.A_M_host_counter, TW.A_M_next_ka,
    TW.A_M_last_display, TW.A_M_display_sent, TW.A_M_fly_on, TW.A_M_fly_cmd, TW.A_M_fly_counter,
    TW.A_M_fly_retries, TW.A_M_fly_sent, TW.A_M_fly_len, TW.A_M_fly_frame, TW.A_Cmd_st, TC.SPEC_MAX_FRAME,
    TC.CMDS_MAX, TW.OFF_M, TW.SZ_M, TW.OFF_g_s, TW.SZ_g_s, TW.OFF_g_cmd, TW.SZ_g_cmd, TW.OFF_g_q, TW.SZ_g_q,
    TW.OFF_g_fail_next, TW.OFF_g_last_counter, TW.SZ_g_last_counter, TW.OFF_g_nq, TW.SZ_g_nq, TW.OFF_GOT,
    TW.SZ_GOT in *;
  lia.

Lemma odsc_wr_inG : forall a, sendctl_wr 0 0 a -> inG TG.G_HARNESS a.
Proof.
intros a H. unfold sendctl_wr, iosend_wr, SENDCTL_F, twa_fld in H.
destruct H as [H|[H|[H0 _]]]; [| | exfalso; exact (H0 eq_refl)].
- apply (odsc_row_inG _ _ _ a TMAP_A_g_s). odsc_num.
- destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]].
  + apply (odsc_row_inG _ _ _ a TMAP_A_g_fail_next). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_GOT). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_GOT). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_GOT). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_g_last_counter). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_M). odsc_num.
  + destruct H as (s & Hs & H). apply (odsc_row_inG _ _ _ a TMAP_A_g_cmd). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_g_q). odsc_num.
  + apply (odsc_row_inG _ _ _ a TMAP_A_g_nq). odsc_num.
Qed.

Section sc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Lemma odsc_ret : YK0s.ret_ok (Z_to_bv 64 (@pa_val _ transport_listing PI_transport A_TEXT + OD_R1)).
Proof.
exact (DgnTransportPaLib.ret_ok_codeptr_v (PI := PI_transport) OD_R1 (proj1 odsc_r1_rng) (proj2 odsc_r1_rng)).
Qed.

Lemma odsc_ra : 4096 <= bv_unsigned (Z_to_bv 64 (@pa_val _ transport_listing PI_transport A_TEXT + OD_R1)).
Proof. destruct od_cut_pcs as (_ & HR1 & _). rewrite HR1. rewrite YP03.unsigned_lit_small by lia. lia. Qed.

(* ---- the registers at the return ---- *)

Lemma odsc_regs : forall (regs regs2 regs3 : bvmap 5 word) (fp now : Z) (b : list byte) (sp1 F r : Z),
  od_regs_sc regs regs2 fp now b sp1 F ->
  aregs_preserved regs2 regs3 -> YK11.getr regs3 10 = w64 r ->
  od_regs_r1 regs regs3 fp now r sp1 F.
Proof.
intros regs regs2 regs3 fp now b sp1 F r
  (((R2 & R3 & R4 & R8 & R9 & R25 & R26) & R18 & R19 & R20 & R21 & R27) & _ & R22 & R23 & R24 & _) HP R10.
unfold od_regs_r1, od_regs_s, od_regs_rel.
refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))
  (conj _ (conj _ (conj _ (conj _ _))))) (conj _ (conj _ (conj _ R10)))).
- rewrite <- R2. exact (HP 2 ltac:(unfold acallee_saved; lia)).
- rewrite <- R3. exact (HP 3 ltac:(unfold acallee_saved; lia)).
- rewrite <- R4. exact (HP 4 ltac:(unfold acallee_saved; lia)).
- rewrite <- R8. exact (HP 8 ltac:(unfold acallee_saved; lia)).
- rewrite <- R9. exact (HP 9 ltac:(unfold acallee_saved; lia)).
- rewrite <- R25. exact (HP 25 ltac:(unfold acallee_saved; lia)).
- rewrite <- R26. exact (HP 26 ltac:(unfold acallee_saved; lia)).
- rewrite <- R18. exact (HP 18 ltac:(unfold acallee_saved; lia)).
- rewrite <- R19. exact (HP 19 ltac:(unfold acallee_saved; lia)).
- rewrite <- R20. exact (HP 20 ltac:(unfold acallee_saved; lia)).
- rewrite <- R21. exact (HP 21 ltac:(unfold acallee_saved; lia)).
- rewrite <- R27. exact (HP 27 ltac:(unfold acallee_saved; lia)).
- rewrite <- R22. exact (HP 22 ltac:(unfold acallee_saved; lia)).
- rewrite <- R23. exact (HP 23 ltac:(unfold acallee_saved; lia)).
- rewrite <- R24. exact (HP 24 ltac:(unfold acallee_saved; lia)).
Qed.

(* What the walk reads off a G journal: the current state's AR, the frames' base, the window above alloc_ceiling. *)
Lemma odsc_jfacts : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own ly2 S2 (W2 : world segs) mem2 md2 k,
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  AR segs B ly2 S2 W2 mem2 md2 /\ ly_F ly2 = ly_F ly /\ alloc_ceiling <= sp0 - STK.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k (_ & _ & (memS & HJ & _) & _).
destruct HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hly as (_ & _ & _ & _ & _ & HF & _).
destruct Hstk as (_ & _ & Hce & Hlo & _).
split; [exact HAR|]. split; [exact HF|]. clear - Hce Hlo. lia.
Qed.

(* The TRANS_RO_RD bytes through a kept fact at the same world: image bytes outside G, the owned statics and errno. *)
Lemma odsc_rom : forall lyc Sc (W : world segs) memc mem2 slo shi (E : Z -> Prop),
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 slo shi E ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W mem2.
Proof.
intros lyc Sc W memc mem2 slo shi E HRU HRE (_ & _ & K3 & _) HR a Ha.
destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
rewrite (K3 a (trans_ro_img a Ha)); [exact (HR a Ha) | | exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_LO in Gh. clear - Gh Rb. lia.
Qed.

(* The 13 saved words, kept when their bytes [sp - 104, sp) are. *)
Lemma odsc_saved : forall (Wa Wb : world segs) (ma mb : word -> option byte) (regs : bvmap 5 word),
  Forall (fun o : Z * Z => rdword (aview segs (w_H Wa) ma) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED ->
  (forall a, spZ regs - 104 <= a < spZ regs -> aview segs (w_H Wb) mb a = aview segs (w_H Wa) ma a) ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H Wb) mb) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED.
Proof.
intros Wa Wb ma mb regs H K. rewrite Forall_forall in H |- *. intros o Ho.
rewrite <- (H o Ho). apply rdword_ext. intros i Hi. apply K.
assert (Hd : 8 <= fst o <= 104).
{ unfold OD_SAVED in Ho. repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
clear - Hd Hi. lia.
Qed.

(* The frame's last word, kept when the frame's bytes are. *)
Lemma odsc_flag : forall (Wa Wb : world segs) (ma mb : word -> option byte) (F v : Z),
  rdword (aview segs (w_H Wa) ma) (F + OD_FBYTES - 8) = Some v ->
  (forall a, F <= a < F + OD_FBYTES -> aview segs (w_H Wb) mb a = aview segs (w_H Wa) ma a) ->
  rdword (aview segs (w_H Wb) mb) (F + OD_FBYTES - 8) = Some v.
Proof.
intros Wa Wb ma mb F v H K. rewrite <- H. apply rdword_ext. intros i Hi. apply K.
unfold OD_FBYTES. clear - Hi. lia.
Qed.

Lemma odsc_main : @od_sc_stmt fx rc B MT.
Proof.
unfold od_sc_stmt, od_sc_at.
intros R1AT HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  S2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HL as (HSM & HCELLS & HODC & HGU & HGNE & HRU & HRE & LAWS & MTL & MTFL & SMP & ASF & FFL & HGX & HGXNE).
pose proof HC as (HSMR & HSC & HKA & HMS & HNT).
pose proof HFIX as (HPRE & HTFNG & Hsp1 & HFeq & HF4096 & HF64 & HFce & HFapp).
pose proof HPRE as (HJ0 & Hra0 & Hra40 & Hgp0 & Htp0 & Ha00 & Ha10 & Ha20 & Hsp16 & Hstk0 & Hsp0 & Hnow & HDF &
  HTW0 & HGF0 & HM & HTFA & HROV & HAP & HI1 & HI4 & HI3 & HCNT & HNEV).
destruct HCUR as ((HJ2 & He0 & HFR2 & HPERM2 & HLYF2 & HMO2 & HKEPT2 & HSAVED2 & HFLAG2) & HABL & HTW2).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R25 & R26) & R18 & R19 & R20 & R21 & R27) & R1 & R22 & R23 & R24 &
  R10 & R11 & R12 & R13 & R14).
rewrite Z.add_0_r in HJ2.
(* The model call of send_control, from on_data_m. *)
destruct (TSS.send_control_m timg_A TF Bw TS0.DIGINET_CMD_ACK (DSpec.fr_send b)) as [[B1 [r f]]|] eqn:HSCM.
2: { exfalso. rewrite ondata_model, HSCM in HM.
     change (@None (list byte * unit) = Some (Bw', tt)) in HM. discriminate HM. }
(* The journal at the call state, and the stack arithmetic. *)
destruct (odsc_jfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & HLY2 & HCE).
assert (Hsprng : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; exact (bv_unsigned_in_range _ _)).
pose proof (@ASAN_CEIL_range rc) as ((HCE0 & _) & _). unfold ASAN_CEIL in HCE0.
destruct (odsc_arith (spZ regs) sp0 STK alloc_ceiling sp1 Hsprng Hsp16 HCE0 HCE Hstk0 Hsp0 Hsp1)
  as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hspr2 : spZ regs2 = sp1).
{ change (spZ regs2) with (bv_unsigned (YK11.getr regs2 2)). rewrite R2. unfold w64.
  exact (YP03.unsigned_lit_small sp1 A1). }
(* send_control's premises. *)
assert (P2 : YK0s.ret_ok (YK11.getr regs2 1)) by (rewrite R1; exact odsc_ret).
assert (P3 : 4096 <= raZ regs2)
  by (change (raZ regs2) with (bv_unsigned (YK11.getr regs2 1)); rewrite R1; exact odsc_ra).
assert (P4 : YK11.getr regs2 3 = w64 (as_gp B)) by (rewrite R3; exact Hgp0).
assert (P5 : YK11.getr regs2 4 = w64 (as_tp B)) by (rewrite R4; exact Htp0).
assert (P11 : spZ regs2 mod 16 = 0) by (rewrite Hspr2; exact A2).
assert (P12 : sp0 - STK <= spZ regs2 - SENDCTL_STK) by (rewrite Hspr2; exact A3).
assert (P13 : spZ regs2 <= sp0) by (rewrite Hspr2; exact A4).
assert (P20 : trans_rom_view_rd W mem2) by exact (odsc_rom lyc Sc W memc mem2 _ _ _ HRU HRE HKEPT2 HROV).
assert (P23 : count_cid SENDCTL_CID (frames S2) + 1 < fs_frames SENDCTL_CID)
  by (rewrite HFR2; exact (odsc_cnt (frames Sc) pos HCNT)).
assert (P24 : st_nev S + k + SENDCTL_EV <= EV_MAX) by exact (odsc_nev (st_nev S + k) HNEV).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_send_control) rg mm mdx) Q) end.
eapply SRr_bind.
{ exact (HSC fx STK sp0 FP ly S W0 mem0 md0 ((ONDATA_CID, pos) :: own) lyc S2 W mem2 md2 k regs2
    TS0.DIGINET_CMD_ACK (DSpec.fr_send b) 0 0 r [] [] f TF Bw B1
    HJ2 P2 P3 P4 P5 R10 R11 R12 R13 R14 P11 P12 P13 odsc_cmd (DSpec.be32_range b 18) (or_introl eq_refl)
    HTW2 HGF0 HSCM P20 HI1 HI4 P23 P24). }
cbv beta. intros W2 c2 _ HQ.
unfold transport_sendctl_post in HQ.
change (sendctl_outs 0 0) with (@nil (Z * Z)) in HQ.
apply transport_cg_post_out_nil in HQ.
unfold transport_cg_post in HQ.
destruct HQ as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & HX3).
destruct HX3 as (HR10 & HTW3 & HGF3 & _).
subst c2. rewrite R1.
(* The return state. *)
destruct (odsc_jfacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (_ & HLY3 & _).
pose proof HK3 as (HK1 & _ & _ & HK4 & _).
assert (HinS2 : In (ONDATA_CID, pos) (frames S2)) by (rewrite HFR2; left; reflexivity).
assert (KS : forall a, spZ regs - 104 <= a < spZ regs -> aview segs (w_H W2) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha. apply HK1.
  - clear - Ha Hsprng A5 A8. lia.
  - rewrite Hspr2. clear - Ha A7. lia. }
assert (KF : forall a, F <= a < F + OD_FBYTES -> aview segs (w_H W2) mem3 a = aview segs (w_H W) mem2 a).
{ intros a Ha.
  assert (Hr : frame_addr lyc ONDATA_CID pos <= a < frame_addr lyc ONDATA_CID pos + fs_frame_bytes ONDATA_CID)
    by (rewrite <- HFeq, od_fbytes; exact Ha).
  apply (HK4 ONDATA_CID pos a HinS2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. exact Hr.
  - intros Hw. exact (frm_img tfibsegs B LAWS lyc S2 W mem2 md2 ONDATA_CID pos a HAR2 HinS2 Hr
      (trans_g_img a (odsc_wr_inG a Hw))). }
destruct (dkg_nf_sep tfibsegs B LAWS DgnTransportImg.transport_segs_low lyc Sc S2 W mem2 md2 ONDATA_CID pos F
  (flag_addr lyc ONDATA_CID pos) HAR2 HFR2 HABL HFeq eq_refl FFL) as (N1 & _ & N3 & _).
assert (KK : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - ONDATA_STK) (spZ regs)
  (ondata_wr Bw b)).
{ apply (dk_kept_trans_nf_g tfibsegs B TG.G_HARNESS lyc Sc lyc S2 W memc W mem2 W2 mem3
    (spZ regs - ONDATA_STK) (spZ regs) (spZ regs2 - SENDCTL_STK) (spZ regs2) (ondata_wr Bw b) (sendctl_wr 0 0)
    (dkg_nf ONDATA_CID F (flag_addr lyc ONDATA_CID pos))).
  - exact A5.
  - clear - Hsprng. lia.
  - intros c p. reflexivity.
  - intros f0 Hf0. rewrite HFR2. right. exact Hf0.
  - intros bm Hbm. rewrite HABL. exact Hbm.
  - exact N1.
  - exact N3.
  - exact HKEPT2.
  - exact HK3.
  - rewrite Hspr2. exact A6.
  - rewrite Hspr2. clear - A7. lia.
  - intros a Ha. left. destruct Ha as [Ha|[Ha|[Ha _]]].
    + left. exact Ha.
    + right. left. exact Ha.
    + exfalso. exact (Ha eq_refl). }
refine (R1AT HL HC STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  B1 r f ly3 S3 W2 mem3 md3 e regs3 HFIX _ (odsc_regs regs regs2 regs3 fp now b sp1 F r HREGS HP3 HR10)).
unfold od_r1_cur, od_cur.
split; [|split; [exact HSCM | split; [exact HTW3 | exact HGF3]]].
split; [exact HJ3|].
split; [exact (odsc_ev e He3)|].
split; [rewrite Hfr3; exact HFR2|].
split; [rewrite <- HABL; exact Hperm3|].
split; [exact (eq_trans HLY3 (eq_sym HLY2))|].
split; [exact (mle_station MT Sc S2 S3 0 0 MTL HMO2 Hmo3)|].
split; [exact KK|].
split.
- exact (odsc_saved W W2 mem2 mem3 regs HSAVED2 KS).
- exact (odsc_flag W W2 mem2 mem3 F (flag_addr lyc ONDATA_CID pos) HFLAG2 KF).
Qed.

End sc.

Theorem od_sc : forall fx rc B MT, @od_sc_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odsc_main fx rc B MT). Qed.

Print Assumptions od_sc.
