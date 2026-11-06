From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes tx_put_c TxCalls TxRet WriterSpec WriterValue PjWriteHyp round_trip_text_c RttDefs
strcmp_c strlen_c pj_parse_c parse_noting_c fuzz_alloc_ran_out_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase RttA_Lib RttB_Cmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require RttRunsB strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rf_trace : forall x ok cnt fail res tr, jr_run jr_strtod x ok = (res, tr) ->
  oks ok cnt fail (calls tr) -> cnt + Z.of_nat (calls tr) <= fail ->
  res = json_read jr_strtod x /\ tr = snd (jr_run jr_strtod x []).
Proof.
  intros x ok cnt fail res tr HR HO HF.
  destruct (ok_upto_dec ok (ncalls jr_strtod x)) as [Hu | (j & Hj & Hf & Hu)].
  - rewrite (G7_1 jr_strtod x ok Hu) in HR. injection HR as <- <-. split; reflexivity.
  - exfalso. destruct (G7_2 jr_strtod x ok j Hj Hf Hu) as [_ HC]. rewrite HR in HC. cbn [snd] in HC.
    rewrite HC in HO, HF. specialize (HO j ltac:(lia)). rewrite Hf in HO.
    destruct (Z.eqb_spec (cnt + Z.of_nat j) fail); [lia | cbn in HO; discriminate HO].
Qed.

Lemma rf_dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (Z.leb_spec need c) as [H|H]; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma rf_dbl_le : forall f c need, 0 < c -> dbl f c need <= Z.max c (2 * need).
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (Z.leb_spec need c) as [H|H]; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma rf_dbl_S : forall f c need, c < need -> dbl (S f) c need = dbl f (2 * c) need.
Proof. intros f c need H. cbn [dbl]. destruct (Z.leb_spec need c) as [H'|H']; [lia | reflexivity]. Qed.

Lemma rf_newcap : forall c need, (c = 0 \/ 4096 <= c) -> c < need ->
  c + 4096 <= newcap c need /\ newcap c need <= Z.max 4096 (2 * need).
Proof.
  intros c need Hc Hn. unfold newcap.
  destruct (Z.eqb_spec c 0) as [->|H0]; cbv beta iota.
  - pose proof (rf_dbl_ge 64 4096 need ltac:(lia)). pose proof (rf_dbl_le 64 4096 need ltac:(lia)). lia.
  - destruct Hc as [Hc|Hc]; [contradiction|]. rewrite (rf_dbl_S 63 c need Hn).
    pose proof (rf_dbl_ge 63 (2 * c) need ltac:(lia)). pose proof (rf_dbl_le 63 (2 * c) need ltac:(lia)). lia.
Qed.

Lemma rf_zsum_nn : forall ls, Forall (fun l => 0 <= l) ls -> 0 <= zsum ls.
Proof. intros ls H. induction H as [|l ls Hl _ IH]; cbn [zsum]; lia. Qed.

Lemma rf_gc : forall ls x c M, (c = 0 \/ 4096 <= c) -> Forall (fun l => 0 <= l) ls -> x + zsum ls + 1 <= M ->
  c + 4096 * Z.of_nat (length (grow_calls x c ls)) <= Z.max c (Z.max 4096 (2 * M)).
Proof.
  induction ls as [|l ls IH]; intros x c M Hc Hl HM; cbn [grow_calls length zsum] in *.
  - lia.
  - apply Forall_cons_iff in Hl. destruct Hl as [Hl0 Hls]. pose proof (rf_zsum_nn ls Hls) as Z0.
    destruct (Z.ltb_spec c (x + l + 1)) as [H|H]; cbn [length].
    + destruct (rf_newcap c (x + l + 1) Hc H) as [N1 N2].
      pose proof (IH (x + l) (newcap c (x + l + 1)) M ltac:(right; lia) Hls ltac:(lia)) as IH'. lia.
    + pose proof (IH (x + l) c M Hc Hls ltac:(lia)) as IH'. lia.
Qed.

Lemma rf_wcalls : forall t p, 4096 * wcalls t p <= Z.max 4096 (2 * (wlen t p + 1)).
Proof.
  intros t p. unfold wcalls.
  assert (HF : Forall (fun l => 0 <= l) (piece_lens (wdpieces t p))).
  { apply Forall_forall. intros l Hl. unfold piece_lens in Hl. apply in_map_iff in Hl. destruct Hl as (b & <- & _). lia. }
  assert (HZ : zsum (piece_lens (wdpieces t p)) = wlen t p).
  { change (piece_lens (wdpieces t p)) with (plen (wdpieces t p)). rewrite zsum_plen. reflexivity. }
  pose proof (rf_gc (piece_lens (wdpieces t p)) 0 0 (wlen t p + 1) (or_introl eq_refl) HF ltac:(lia)) as H.
  lia.
Qed.


(* round_trip_text of the #102 plain twin c8f4d6b8, stage stg_cmp_st (RttBase.v) at 0x14e0c, rendered() done.
   RttRunsB.rtt_segF: lw failed (0 by text_rec), ld want, lbu g_own_ran_out, fuzz_alloc_ran_out; a nonzero flag byte
   goes to the ran-out arm stg_oom_st (0x14e38); both bytes 0 go on to 0x14e74, where RttRunsB.rtt_seg4 runs the NULL
   text test, strcmp, strlen and jal parse_noting(text, len, &back).  parse_noting_c's contract needs g_ran_out = 0
   (fuzz_alloc_ran_out_c.G_RAN_OUT), which this stage has from rtt_segF's ro = 0 arm; it returns to 0x14ea0 =
   stg_ff_st with rc = 0. *)
Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis SC : strcmp_contract.
Hypothesis SL : strlen_contract.
Hypothesis FRO : fuzz_alloc_ran_out_contract.
Hypothesis PNC : forall fx' : YK11.FPState, @parse_noting_contract fx' rc B API F.
Hypothesis OOM : stg_oom_st B API F.
Hypothesis NEXT : stg_ff_st B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Theorem stg_cmp_holds : stg_cmp_st B API F.
Proof.
  unfold stg_cmp_st.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regs mem md Lam peak q want cap s3v.
  cbv zeta. intros ENT FL INV RG TXT HARN HCAPF.
  pose proof ENT as (REN & INIT0 & LED0 & CNT0 & RES0 & G10d & G11p & G12c & PR & NODE0 & DSUB & DOC0 & DOCS & WF &
    DEP & WLEN & COPY & ROOM).
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODE & RES & _).
  pose proof RS as (MRc & WFc & BDc & _ & PSc & _ & _ & _ & _ & WRc).
  pose proof RG as (R2 & R8 & R9 & R18 & R19 & R20 & R21 & R3 & R4 & R22).
  pose proof TXT as (Q0 & QIN & QNB & QF & QB).
  pose proof HARN as (W0 & LN0 & CP0 & TREC & TWR & TINV & WNB & WNL).
  destruct (rtt_fl_inv B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A mem md
    _ _ _ _ _ ENT INV FL) as (Hro & Hoo & BRO & BOO).
  set (p := negb (pretty =? 0)) in *.
  pose proof alloc_ceiling_val as HCV.
  assert (HRK : RTT_K = 13808) by (vm_compute; reflexivity).
  assert (HPK : PN_K = 13696) by (vm_compute; reflexivity).
  assert (HERR : errno_addr B = strtod_c.STRTOD_ERRNO) by exact ERRB. unfold strtod_c.STRTOD_ERRNO in HERR.
  assert (HST : forall a, alloc_statics a -> GL_FAIL <= a < GL_COUNT + 8).
  { intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold GL_FAIL, GL_COUNT. lia. }
  unfold GL_FAIL, GL_COUNT in HST.
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (lb_perm_in _ _ _ bk PERM). right. exact (DSUB bk Hb). }
  pose proof (lb_node_top _ _ _ _ _ _ NODE0) as DOCT.
  pose proof (lb_wlen_pos t p WF) as HWL1.
  assert (LW : Z.of_nat (length (map (Z_to_bv 8) (wdoc t p))) = wlen t p) by (rewrite length_map; reflexivity).
  destruct (lb_text B API HSEG FA L A mem md Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) t p q MRc LED QIN WLEN)
    as (QT1 & QT2 & QT3 & QBLK & QT5 & _).
  destruct TINV as (TL & [(C0 & _ & HL0) | (CP1 & WBLK & WLT & WBY & WIMG)]); [lia|].
  destruct (rg_blk B API HSEG AX FG L A mem md want cap 0 MRc WBLK ltac:(lia)) as (_ & WR1 & WR2 & _).
  destruct ROOM as (_ & _ & ROOMR).
  pose proof (rf_wcalls t p) as HWB.
  assert (HWC : 1 <= wcalls t p) by apply wcalls_pos.
  destruct (rtt_G9 t p WF) as (G9a & G9b & G9c).
  assert (Ecalls : calls (PjRoundTrip.ttrace t) = PjRoundTrip.tcalls t)
    by (unfold ncalls in G9c; rewrite G9b in G9c; exact G9c).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  assert (RA : ro_agree (ms_segs B) mem) by exact (proj1 RD).
  destruct TREC as (TR3 & T28 & TF0).
  assert (PB0 : Mem.bytes_at (ms_segs B) mem (spZ regs0 - 112)
      (Mem.le8 (Z_to_bv 64 want) ++ Mem.le8 (Z_to_bv 64 (wlen t p)) ++ Mem.le8 (Z_to_bv 64 cap))).
  { apply (lb_mbytes B API HSEG FA); [lia | rewrite !length_app, !Mem.length_le8; lia | exact TR3]. }
  assert (PBw : Mem.bytes_at (ms_segs B) mem (spZ regs0 - 112) (Mem.le8 (Z_to_bv 64 want))).
  { apply Mem.bytes_at_app in PB0. exact (proj1 PB0). }
  assert (PBf : Mem.bytes_at (ms_segs B) mem (spZ regs0 - 112 + 24) (Mem.le4 (Z_to_bv 64 0))).
  { apply (lb_mbytes B API HSEG FA); [lia | rewrite Mem.length_le4; lia | exact TF0]. }
  rewrite HSEG in PBw, PBf, BRO, BOO.
  (* the failed test, want, and the two flag bytes (memory unchanged) *)
  eapply (@ra_run fx rc B API F HSEG FA fx1 regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite R2.
    exact (RttRunsB.rtt_segF FRO (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx1) (@fp_csr fx1) mem (spZ regs0 - 112) want ro oo
      ltac:(lia) ltac:(lia) ltac:(lia) Hro Hoo PBw PBf BOO BRO). }
  { intros ms' (ra' & a0' & [(_ & E) | (_ & _ & E)]); eexists _, _, _; exact E. }
  intros RF pcF memF regsF HQF HGF.
  destruct HQF as (ra' & a0' & [(HRO & EF) | (Ero & Eoo & EF)]); ra_inj EF RF pcF memF.
  - (* a flag byte is nonzero: the ran-out arm *)
    apply (OOM L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ro oo fx1 L A regsF mem md Lam peak q want
      (wlen t p) cap (getr regs0 20) (Z_to_bv 64 0x34e24) ENT FL HRO INV).
    + split; [rewrite HGF; reflexivity|].
      split; [rewrite HGF; exact R8|].
      split; [rewrite HGF; exact R9|].
      split; [rewrite HGF; exact R18|].
      split; [rewrite HGF; reflexivity|].
      split; [rewrite HGF; exact R20|].
      split; [rewrite HGF; reflexivity|].
      split; [rewrite HGF; exact R3|].
      split; [rewrite HGF; exact R4|].
      intros r Hr. rewrite HGF, <- (R22 r Hr).
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
    + exact TXT.
    + exact W0.
    + exact CP1.
    + exact WBLK.
    + exact WLT.
    + exact HCAPF.
    + exact WIMG.
    + exact WNB.
    + exact WNL.
  - (* both bytes 0: strcmp, strlen, parse_noting *)
    subst ro oo.
    assert (F2 : getr regsF 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGF; reflexivity).
    assert (F18 : getr regsF 18 = Z_to_bv 64 q) by (rewrite HGF; exact R18).
    assert (F19 : getr regsF 19 = Z_to_bv 64 want) by (rewrite HGF; reflexivity).
    assert (F21 : getr regsF 21 = Z_to_bv 64 0x34e24) by (rewrite HGF; reflexivity).
    assert (F3 : getr regsF 3 = getr regs0 3) by (rewrite HGF; exact R3).
    assert (F4 : getr regsF 4 = getr regs0 4) by (rewrite HGF; exact R4).
    assert (F8 : getr regsF 8 = Z_to_bv 64 copy) by (rewrite HGF; exact R8).
    assert (F9 : getr regsF 9 = getr regs0 10) by (rewrite HGF; exact R9).
    assert (F20 : getr regsF 20 = getr regs0 20) by (rewrite HGF; exact R20).
    assert (F22 : forall r, 22 <= r <= 27 -> getr regsF (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
    { intros r Hr. rewrite HGF, <- (R22 r Hr).
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
    assert (MREL : mem_rel (ms_segs B) mem (normalize (ms_segs B) mem)) by exact (mem_rel_normalize _ mem RA).
    assert (NB : forall a bs, Mem.bytes_at (ms_segs B) mem a bs -> Mem.bytes_at rsegs (normalize rsegs mem) a bs).
    { intros a bs Hb. rewrite <- HSEG. exact (proj1 (bytes_at_rel _ _ _ a bs MREL) Hb). }
    destruct (lb_slack B API HSEG FA L A mem md Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) t p q MRc LED QIN WLEN RA QB)
      as (sl & SLB & SLM).
    assert (WB : Mem.bytes_at rsegs (normalize rsegs mem) want (map (Z_to_bv 8) (wdoc t p) ++ [Z_to_bv 8 0])).
    { apply NB. apply (lb_mbytes B API HSEG FA); [lia | | exact WBY].
      rewrite length_app, Nat2Z.inj_add, LW. cbn [length]. lia. }
    destruct (kb_md B API L A mem md MRc) as (HhF & HzF).
    eapply (lb_run B API HSEG FA fx1 regsF (Z_to_bv 64 0x14e74) mem md _ _ HhF HzF RA).
    { unfold rmk. rewrite F2, F18, F19.
      apply (RttRunsB.rtt_seg4 SC SL (getr regsF 1) (getr regsF 3) (getr regsF 4) (getr regsF 5) (getr regsF 6)
        (getr regsF 7) (getr regsF 8) (getr regsF 9) (getr regsF 10) (getr regsF 11) (getr regsF 12) (getr regsF 13)
        (getr regsF 14) (getr regsF 15) (getr regsF 16) (getr regsF 17) (getr regsF 20) (getr regsF 21) (getr regsF 22)
        (getr regsF 23) (getr regsF 24) (getr regsF 25) (getr regsF 26) (getr regsF 27) (getr regsF 28) (getr regsF 29)
        (getr regsF 30) (getr regsF 31) (@fp_regs fx1) (@fp_csr fx1) (normalize rsegs mem) (spZ regs0 - 112) q want
        (map (Z_to_bv 8) (wdoc t p)) sl);
        [lia | lia | lia | exact SLB | exact (bytes_nz _ QF) | exact SLM | exact WB | apply mem_inv_normalize]. }
    { intros ms' (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & _ & _ & _ & E).
      eexists _, _, _. exact E. }
    intros R pc' m0 mem1 regs1 HQ HREL HROS HGr.
    destruct HQ as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & MU & WM & MI & E).
    lb_inj E R pc' m0.
    rewrite <- HSEG in MU, WM.
    pose proof (munch_rel _ _ mem _ mem1 m' MREL HREL HROS MU) as MU1.
    pose proof (wmono_rel _ mem _ mem1 m' MREL HREL HROS WM) as WM1.
    pose proof (ro_agree_same _ mem mem1 RA HROS) as RA1.
    pose proof (@lb_inv_munch fx rc B API HSEG FA F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A
      mem md [(q, wcap t p)] Lam peak (cnt0 + wcalls t p) (rtt_bt F b0 cnt0 t p) mem1 [] 0 ENT INV MU1 WM1 RA1
      ltac:(lia) ltac:(lia) ltac:(intros lo hi x [])) as INV1.
    pose proof INV1 as (RS1 & _ & INIT1 & RD1 & FRM1 & _ & LED1 & _ & _ & NODE1 & _ & _ & _ & _).
    pose proof RS1 as (MR1 & _ & _ & _ & _ & _ & _ & _ & _ & WRw).
    assert (QB1 : Mem.bytes_at (ms_segs B) mem1 q (map (Z_to_bv 8) (wdoc t p ++ [0])))
      by exact (lb_bytes_munch B API HSEG FA [] mem mem1 q _ QB MU1 (fun _ _ => I)).
    assert (TB1 : Mem.bytes_at (ms_segs B) mem1 q (map (Z_to_bv 8) (wdoc t p))).
    { pose proof QB1 as H. rewrite map_app in H. apply Mem.bytes_at_app in H. exact (proj1 H). }
    assert (GR1 : Mem.bytes_at (ms_segs B) mem1 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0))).
    { rewrite <- HSEG in BRO. exact (lb_bytes_munch B API HSEG FA [] mem mem1 _ _ BRO MU1 (fun _ _ => I)). }
    assert (G1 : getr regs1 1 = Z_to_bv 64 0x14ea0) by (rewrite HGr; reflexivity).
    assert (G2 : getr regs1 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
    assert (G3 : getr regs1 3 = getr regs0 3) by (rewrite HGr; exact F3).
    assert (G4 : getr regs1 4 = getr regs0 4) by (rewrite HGr; exact F4).
    assert (G8 : getr regs1 8 = Z_to_bv 64 copy) by (rewrite HGr; exact F8).
    assert (G9 : getr regs1 9 = getr regs0 10) by (rewrite HGr; exact F9).
    assert (G10 : getr regs1 10 = Z_to_bv 64 q) by (rewrite HGr; reflexivity).
    assert (G11 : getr regs1 11 = Z_to_bv 64 (wlen t p)) by (rewrite HGr, <- LW; reflexivity).
    assert (G12 : getr regs1 12 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite HGr; reflexivity).
    assert (G18 : getr regs1 18 = Z_to_bv 64 q) by (rewrite HGr; reflexivity).
    assert (G19 : getr regs1 19 = Z_to_bv 64 want) by (rewrite HGr; reflexivity).
    assert (G20 : getr regs1 20 = getr regs0 20) by (rewrite HGr; exact F20).
    assert (G21 : getr regs1 21 = Z_to_bv 64 0x34e24) by (rewrite HGr; exact F21).
    assert (G22 : forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
    { intros r Hr. rewrite <- (F22 r Hr). rewrite HGr.
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
    assert (HS1 : spZ regs1 = spZ regs0 - 112) by (unfold spZ at 1; rewrite G2; apply lb_uns; lia).
    assert (HOUT : (spZ regs0 - 112) mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (STK1 : Frame.stk (ms_segs B) mem1 (spZ regs0 - 112) (spZ regs0 - 112 + 56)).
    { assert (HWw : forall a, spZ regs0 - 112 <= a < spZ regs0 - 112 + 56 -> writable_at (ms_segs B) mem1 a)
        by (intros a Ha; apply WRw; unfold rwin; left; lia).
      exact (proj1 (lb_stk_win B API HSEG FA mem1 (spZ regs0 - 112) (spZ regs0 - 112 + 56) ltac:(lia) ltac:(lia) HWw)). }
    destruct (rtt_img_low B API HSEG FA) as [HIL _].
    assert (GRI : in_img B G_RAN_OUT).
    { refine (proj1 (rtt_flag_img B API HSEG FA G_RAN_OUT _)). left. lia. }
    pose proof (HIL _ GRI) as GRL.
    assert (GRQ : ~ (q <= G_RAN_OUT < q + wlen t p)).
    { intros Hq. apply (ledger_block_not_img B L A mem1 Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) q (wcap t p)
        (G_RAN_OUT - q) LED1 QIN); [lia|].
      replace (q + (G_RAN_OUT - q)) with G_RAN_OUT by lia. exact GRI. }
    eapply SR_bind; [apply (PNC fx1 L A regs1 mem1 md Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) (rtt_bt F b0 cnt0 t p) q
      (wlen t p) (spZ regs0 - 112) (map (Z_to_bv 8) (wdoc t p))) |].
    + apply (@reader_env_mid fx1 rc B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem1 md regs1
        PN_K 112 (lb_env_fx B API HSEG FA fx fx1 _ _ _ _ _ _ REN FRM1) RS1 INIT1 RD1 FRM1);
        [exact HS1 | rewrite HS1; Z.div_mod_to_equations; lia | rewrite G4; reflexivity | rewrite G1; lb_ret | lia | lia |
         lia].
    + exact LED1.
    + exact RES.
    + exact G10.
    + exact G11.
    + exact G12.
    + lia.
    + lia.
    + lia.
    + exact LW.
    + exact TB1.
    + rewrite (bytes_zb _ QF). apply rtt_maxrun. lia.
    + split.
      * right. right. right. exists q, (wcap t p). split; [exact QIN | lia].
      * intros i Hi.
        destruct (rg_blk B API HSEG AX FG L A mem1 md (q - 16) (wcap t p + 16) (i + 16) MR1 QBLK ltac:(lia))
          as (_ & _ & _ & HO).
        replace (q - 16 + (i + 16)) with (q + i) in HO by lia.
        assert (HNI : ~ in_img B (q + i)).
        { apply (ledger_block_not_img B L A mem1 Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) q (wcap t p) i LED1 QIN). lia. }
        split; [exact HO|]. split.
        -- intros Hs. apply HNI. exact (proj1 (statics_img B API HSEG AX FG _ Hs)).
        -- intros He. apply HNI. replace (q + i) with (errno_addr B + (q + i - errno_addr B)) by lia.
           apply (errno_img B API HSEG AX FG ERRB). lia.
    + lia.
    + split; [exact HOUT | exact STK1].
    + split; [left; rewrite HS1; lia|].
      split; [intros _ Ei; rewrite INIT1 in Ei; discriminate|].
      intros i Hi. split.
      { intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem1 md _ MR1 Ho). lia. }
      split; [intros Hs; pose proof (HST _ Hs); lia|].
      split; [rewrite HERR; lia|].
      intros Hi'. pose proof (HIL _ Hi'). lia.
    + intros a k Hin. pose proof (ledger_block_range B API L A mem1 md Lam _ _ _ a k MR1 LED1 Hin). lia.
    + cbn [Frame.disjoint_from]. split; [lia | exact I].
    + exact GR1.
    + cbn [Frame.disjoint_from]. split; [lia|]. split; [lia | exact I].
    + cbn [Frame.disjoint_from]. rewrite HS1. split; [lia|]. split; [lia | exact I].
    + lia.
    + rewrite (bytes_zb _ QF), G9b. exact ROOMR.
    + intros c' (fx2 & L' & A' & regs2 & mem2 & md2 & Lam' & peak' & cnt' & fail' & ok & res & tr & -> & FZ2 & FRG2 &
        RP2 & RD2 & GR2 & LG2 & Hrun & Hoks & Hcnt & Hfa & Hpk2 & _ & _ & _ & Hres).
      rewrite (bytes_zb _ QF) in Hrun.
      assert (HLC : cnt0 + wcalls t p + Z.of_nat (calls tr) <= 2 ^ 64 - 1).
      { pose proof LG2 as (_ & _ & Hc' & _). lia. }
      destruct (rf_trace _ _ _ _ _ _ Hrun Hoks HLC) as (Eres & Etr).
      rewrite G9a in Eres. rewrite G9b in Etr. subst res tr.
      destruct Hres as (G10' & RS2 & Dn & PERMn & LSZn & NLn & NEWn & NODEn).
      assert (Hf2 : fail' = 2 ^ 64 - 1) by (apply (proj2 Hfa); lia).
      assert (Hc2 : cnt' = cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) by (rewrite Hcnt, Ecalls; reflexivity).
      rewrite Hc2, Hf2 in LG2.
      pose proof RP2 as (MR2 & _ & _ & _ & _ & _ & _ & UB & PA & RR & _).
      pose proof (rstep_of_rpost B API HSEG AX FG PN_K L A regs1 mem1 md (parse_noting_writes (spZ regs0 - 112))
        (fun _ _ => False) L' A' regs2 mem2 md2 RP2) as ST2.
      rewrite HS1 in ST2.
      pose proof ST2 as (_ & _ & _ & _ & _ & _ & _ & _ & BLK2 & _).
      assert (HBK : forall a k, In (a, k) (blocks L A) -> In (a, k) (blocks L' A')).
      { intros a k Hin. destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
        assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB; [exact Hq0 | intros []]).
        rewrite <- (PA q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1). }
      assert (LL : forall bk, In bk Lam -> In bk Lam').
      { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERMn)). apply in_or_app. right. exact Hb. }
      assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx2 L' A' mem2 md2
        (Dn ++ [(q, wcap t p)]) Lam' peak' (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (rtt_bp F b0 cnt0 t p)).
      { apply (@inv_after fx rc B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem1 md
          [(q, wcap t p)] Lam peak (cnt0 + wcalls t p) (rtt_bt F b0 cnt0 t p) PN_K (parse_noting_writes (spZ regs0 - 112))
          (fun a => exists n : Z, False) fx2 L' A' mem2 md2 (Dn ++ [(q, wcap t p)]) Lam' peak'
          (cnt0 + wcalls t p + Z.of_nat (PjRoundTrip.tcalls t)) (rtt_bp F b0 cnt0 t p) ENT INV1 ST2).
        - lia.
        - lia.
        - intros a [Ha|Ha]; [right; left; lia | left; exact Ha].
        - intros a Ha _. destruct (lb_node_rw _ _ _ _ _ _ NODEn) as (_ & Hstk).
          exact (lb_stk_wr _ _ _ _ a Hstk ltac:(lia)).
        - intros a k _ _ (n & []).
        - intros a k Hin _. exact (HBK a k Hin).
        - exact (proj1 RD2).
        - exact FZ2.
        - exact FRG2.
        - exact LG2.
        - lia.
        - rewrite <- app_assoc. eapply Permutation_trans; [exact PERMn|]. apply Permutation_app_head. exact PERM.
        - apply (pj_node_rstep B API HSEG AX FG PN_K (spZ regs0 - 112) (parse_noting_writes (spZ regs0 - 112))
            (fun a => exists n : Z, False) L A mem1 md L' A' mem2 md2 Lam Lam' peak (cnt0 + wcalls t p) (2 ^ 64 - 1)
            doc t D MR1 LED1 NODE1 DL ST2); [lia | exact DOCT | | | exact LL].
          + intros i Hi. split; [unfold rwin; rewrite HERR; lia|].
            intros [Hw|Hw]; [lia | pose proof (HST _ Hw); lia].
          + intros a k Hin. split; [intros (n & [])|].
            pose proof (ledger_block_range B API L A mem1 md Lam _ _ _ a k MR1 LED1 (DL _ Hin)) as Hr.
            intros i Hi [Hw|Hw]; [lia|].
            apply (ledger_block_not_img B L A mem1 Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) a k i LED1 (DL _ Hin));
              [lia|].
            exact (proj1 (statics_img B API HSEG AX FG _ Hw)).
        - exact RS2. }
      rewrite G1.
      apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D 0 0 fx2 L' A' regs2 mem2 md2 Lam' peak'
        Dn q want (wlen t p) cap ENT FL eq_refl eq_refl INV2).
      all: try fold p.
      * split; [etransitivity; [apply (RR 2); unfold callee_saved; lia | exact G2]|].
        split; [etransitivity; [apply (RR 8); unfold callee_saved; lia | exact G8]|].
        split; [etransitivity; [apply (RR 9); unfold callee_saved; lia | exact G9]|].
        split; [etransitivity; [apply (RR 18); unfold callee_saved; lia | exact G18]|].
        split; [etransitivity; [apply (RR 19); unfold callee_saved; lia | exact G19]|].
        split; [etransitivity; [apply (RR 20); unfold callee_saved; lia | exact G20]|].
        split; [etransitivity; [apply (RR 21); unfold callee_saved; lia | exact G21]|].
        split; [etransitivity; [apply (RR 3); unfold callee_saved; lia | exact G3]|].
        split; [etransitivity; [apply (RR 4); unfold callee_saved; lia | exact G4]|].
        intros r Hr. etransitivity; [apply (RR r); unfold callee_saved; lia | exact (G22 r Hr)].
      * exact G10'.
      * split; [exact Q0|]. split; [exact (LL _ QIN)|]. split; [exact QNB|]. split; [exact QF|].
        apply (lb_bytes_keep B API HSEG FA mem1 mem2 q _ QB1). intros i Hi.
        rewrite length_map, length_app in Hi. cbn [length] in Hi. unfold wlen in QT5.
        replace (q + i) with (q - 16 + (i + 16)) by lia.
        apply (BLK2 (q - 16) (wcap t p + 16) (i + 16) QBLK); [intros (n & []) | lia |].
        intros [Hw|Hw]; [lia|].
        apply (ledger_block_not_img B L A mem1 Lam peak (cnt0 + wcalls t p) (2 ^ 64 - 1) q (wcap t p) i LED1 QIN); [lia|].
        replace (q + i) with (q - 16 + (i + 16)) by lia. exact (proj1 (statics_img B API HSEG AX FG _ Hw)).
      * exact W0.
      * exact CP1.
      * exact (HBK _ _ WBLK).
      * exact WLT.
      * exact HCAPF.
      * exact WIMG.
      * exact WNB.
      * intros a n Hin Ea. destruct (lb_perm_in2 _ _ _ _ PERMn Hin) as [HD|HD]; [|exact (WNL a n HD Ea)].
        pose proof LG2 as (_ & _ & _ & _ & _ & FB2). rewrite Forall_forall in FB2.
        destruct (FB2 _ Hin) as (Hn0 & Hblk & _ & _). cbn [fst snd] in Hn0, Hblk.
        rewrite Ea in Hblk.
        pose proof (blocks_same_addr B API HSEG AX FG L' A' mem2 md2 want (n + 16) cap MR2 Hblk (HBK _ _ WBLK)
          ltac:(lia) CP1) as En.
        apply (NEWn a n HD). rewrite Ea, En. exact WBLK.
      * exact NODEn.
      * intros a k Hin Hb0. apply (NEWn a k Hin).
        destruct (Z_lt_le_dec 0 (k + 16)) as [Hk|Hk]; [exact (PSc _ _ Hb0 Hk (fun h => h)) | exact (Z0 _ _ Hb0 Hk)].
      * intros bk Hb. apply (Permutation_in _ (Permutation_sym PERMn)). apply in_or_app. left. exact Hb.
      * exact LSZn.
      * exact NLn.
Qed.

End S.
