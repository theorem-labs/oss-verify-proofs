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
Ledger PjStruct ReaderRes tx_put_c TxCalls TvSpec TxRet TxGlue TxCompose WriterSpec WriterValue PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase RttA_Lib.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require RttRunsA strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Section NP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.

Definition nl_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (t b0 len0 cap0 : Z) (txt src : list byte) (n : Z) (bnd : rf_R F) (c' : config) : Prop :=
  exists L' A' regs' mem' md' b1 cap1,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    regs_preserved regs regs' /\
    tx_relx B API F TX_STACK regs t b0 len0 cap0 txt src bnd L A mem md L' A' mem' md' b1 cap1 [n] /\
    (forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (blocks L' A')).

Lemma nl_kA : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  ms_segs B = rsegs -> m_halted md1 = None -> m_vm_lazy md1 = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P HSEG Hh Hz HE HS HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite HSEG. eapply Exec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma nl_put_ret : tx_put_contract B API F ->
  forall L A regs mem md (t s n b0 len0 cap0 : Z) (txt src : list byte) (bnd : rf_R F),
    call_pre_k B (aa_MR API) TX_STACK L A regs mem md -> st_init_done A = true -> ro_agree (ms_segs B) mem ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    spZ regs <= t -> t + 24 <= 2 ^ 64 -> t mod 8 = 0 ->
    (forall i, 0 <= i < 24 -> writable_at (ms_segs B) mem (t + i)) ->
    0 <= b0 < 2 ^ 64 -> 0 <= len0 < 2 ^ 64 -> 0 <= cap0 < 2 ^ 64 ->
    text_rec B mem t b0 len0 cap0 ->
    tx_inv B L A mem b0 len0 cap0 txt ->
    0 <= s < 2 ^ 64 -> 0 <= n -> s + n <= 2 ^ 64 ->
    mbytes B mem s src -> Z.of_nat (length src) = n ->
    (forall i, 0 <= i < n ->
       ~ (t <= s + i < t + 24) /\ ~ (spZ regs - TX_STACK <= s + i < spZ regs) /\ ~ (b0 <= s + i < b0 + cap0) /\
       (len0 + n + 1 <= cap0 \/ spZ regs <= s + i \/ Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
        exists a k, In (a, k) (blocks L A) /\ a <> b0 /\ a <= s + i < a + k)) ->
    len0 + n + 1 <= 2 ^ 28 ->
    rf_ok F A bnd -> (cap0 < len0 + n + 1 -> rf_room F bnd (2 * (len0 + n + 1))) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 TX_PUT) mem (seg_rom (ms_segs B))) md)
      (nl_ret L A regs mem md t b0 len0 cap0 txt src n bnd).
Proof.
  intros TXP0 L A regs mem md t s n b0 len0 cap0 txt src bnd PRE INIT RA R10 R11 R12 Tlo Thi Tal TW Rb Rl Rc REC INV
    Sr Sn Shi SRC SL SP NEED RES ROOM.
  eapply SR_mono;
    [exact (TXP0 L A regs mem md t s n b0 len0 cap0 txt src bnd PRE INIT RA R10 R11 R12 Tlo Thi Tal TW Rb Rl Rc REC INV
              Sr Sn Shi SRC SL SP NEED RES ROOM)|].
  intros c' (L' & A' & regs' & mem' & md' & b1 & cap1 & bnd' & -> & FR & RP & BK & TR & TW' & INV' & _ & RA' & GK & IN &
             LEN & RES' & ARMS).
  destruct ARMS as [(FIT & -> & -> & -> & -> & -> & ->) | (GROW & EC & AL & EB & bl1 & bl2 & bm1 & bm2 & E1 & E2 & E3)].
  - exists L, A, regs', mem', md, b0, cap0. split; [reflexivity|]. split; [exact RP|].
    split; [|intros a k Hin _; exact Hin].
    unfold tx_relx. rewrite SL.
    split; [exact FR|]. split; [exact LEN|]. split; [exact BK|].
    split; [intros a k Hin Hne; split; assumption|].
    split; [intros a k Hin Hk Hne; exact Hne|].
    split; [exact TR|]. split; [exact TW'|]. split; [exact INV'|]. split; [exact RA'|]. split; [exact GK|].
    split; [exact IN|]. split; [cbn [zsum]; lia|].
    split; [cbn [tx_capf]; unfold tx_cap1; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity|].
    cbn [tx_fold]. unfold tx_next. rewrite (proj2 (Z.leb_le _ _)) by lia. exact RES'.
  - exists L', A', regs', mem', md', b1, cap1. split; [reflexivity|]. split; [exact RP|].
    pose proof FR as (M' & _).
    pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M') as PW. rewrite E1 in PW.
    assert (PC : 0 < cap1) by lia.
    assert (OLD : forall a k, In (a, k) (blocks L A) -> (a, k) <> (b0, cap0) -> In (a, k) (bm1 ++ bm2)).
    { intros a k Hin Hne. rewrite E2. destruct E3 as [(C0 & E3)|(C0 & E3)]; rewrite E3 in Hin; [exact Hin|].
      apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|[H|H]]; [left; exact H | | right; exact H].
      exfalso. apply Hne. symmetry. exact H. }
    assert (OLD0 : forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (bm1 ++ bm2)).
    { intros a k Hin Hk. rewrite E2. destruct E3 as [(C0 & E3)|(C0 & E3)]; rewrite E3 in Hin; [exact Hin|].
      apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|[H|H]]; [left; exact H | | right; exact H].
      exfalso. injection H as Ha Hk'. lia. }
    assert (NEWB : forall a k, In (a, k) (bm1 ++ bm2) -> In (a, k) (blocks L' A')).
    { intros a k H. rewrite E1. apply in_app_or in H. apply in_or_app.
      destruct H as [H|H]; [left; exact H | right; right; exact H]. }
    split; [|intros a k Hin Hk; exact (NEWB a k (OLD0 a k Hin Hk))].
    unfold tx_relx. rewrite SL.
    split; [exact FR|]. split; [exact LEN|]. split; [exact BK|].
    split.
    { intros a k Hin Hne. pose proof (OLD a k Hin Hne) as Hin'.
      split; [exact (NEWB a k Hin')|].
      intros X. injection X as Xa Xk. subst a k.
      destruct (pairwise_mid _ _ _ _ _ PW Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split.
    { intros a k Hin Hk Hne X. subst a.
      assert (Hin' : In (b1, k) (bm1 ++ bm2)).
      { apply OLD; [exact Hin|]. intros X. apply Hne. congruence. }
      destruct (pairwise_mid _ _ _ _ _ PW Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split; [exact TR|]. split; [exact TW'|]. split; [exact INV'|]. split; [exact RA'|]. split; [exact GK|].
    split; [exact IN|]. split; [cbn [zsum]; lia|].
    split; [cbn [tx_capf]; unfold tx_cap1; rewrite (proj2 (Z.leb_gt _ _)) by lia; lia|].
    subst bnd'. cbn [tx_fold]. unfold tx_next. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite <- EC. exact RES'.
Qed.

End NP.

(* round_trip_text of the #102 plain twin c8f4d6b8, stage stg_nl_st (RttBase.v) at 0x14df4, tx_value's return:
   RttRunsA.rtt_seg3 (beqz s3; when pretty, jal tx_put(&t, "\n" = 0x10392, 1)); returning to 0x14e0c = stg_cmp_st.
   tx_put's contract (tx_put_c.v) takes text_rec with the record's int failed = 0 at offset 24. *)
Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Hypothesis TXP : forall fx' : YK11.FPState, @tx_put_contract fx' rc B API F.
Hypothesis NEXT : stg_cmp_st B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma nl_ctx : ctx_owned B API.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Theorem stg_nl_holds : stg_nl_st B API F.
Proof.
  unfold stg_nl_st. cbv zeta.
  intros L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc pretty copy t D ro oo fx' L A regs mem md Lam peak q want cap
    ENT FL INV RG RT RH HCAP.
  pose proof ENT as (REN & INIT0 & LED0 & CNT0 & RES0 & R10 & R11 & R12 & PR & NODE0 & DIN & DOC0 & DOCS & PWF & DEP &
    WL & COPY & ROOM).
  pose proof REN as (SEGB & TPB & ERRB0 & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & FREG & LED & PK & PERM & NODE & RES & CP & SL8 & SL16 &
    SL24 & SL32 & SL40 & SL48 & SL56 & WR56).
  pose proof RS as (MRc & WFc & BDc & INc & KBc & MDc & ACc & IMc & BKc & WRc).
  pose proof RG as (G2 & G8 & G9 & G18 & G19 & G20 & G21 & G3 & G4 & G22).
  pose proof RT as (Q0 & QIN & QNB & QF & QB).
  pose proof RH as (Wr & Lr & Cr & TREC & TW & TINV & WNB & WNL).
  pose proof alloc_ceiling_val as HCV.
  assert (HRK : RTT_K = 13808) by (vm_compute; reflexivity).
  assert (HTX : TX_STACK = 8288) by (vm_compute; reflexivity).
  assert (HERR : errno_addr B = strtod_c.STRTOD_ERRNO) by exact ERRB0. unfold strtod_c.STRTOD_ERRNO in HERR.
  assert (ERRB : errno_addr B + 4 <= alloc_ceiling) by lia.
  assert (HST : forall a, alloc_statics a -> GL_FAIL <= a < GL_COUNT + 8).
  { intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold GL_FAIL, GL_COUNT. lia. }
  unfold GL_FAIL, GL_COUNT in HST.
  set (S := spZ regs0) in *.
  assert (HSP : spZ regs = S - 112) by (unfold spZ; rewrite G2; apply ra_uns; lia).
  destruct (kb_md B API L A mem md MRc) as (Hh & Hz).
  eapply (nl_kA B fx' regs _ mem md _ _ HSEG Hh Hz).
  { unfold rmk. rewrite G2.
    apply (RttRunsA.rtt_seg3 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem (S - 112)). }
  { intros ms' [(_ & E) | (_ & E)]; eexists _, _, _; exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as [(HS3 & E) | (HS3 & E)]; ra_inj E R pc' mem1.
  - assert (HP0 : pretty = 0).
    { destruct PR as [P0 | P1]; [exact P0|]. exfalso. subst pretty. rewrite G19 in HS3.
      apply (f_equal bv_unsigned) in HS3. rewrite !ra_uns in HS3 by lia. lia. }
    subst pretty.
    assert (EP : negb (0 =? 0) = false) by reflexivity.
    assert (WD : wdoc t false = concat (wvpieces t false 0)) by (rewrite wdoc_split; apply app_nil_r).
    assert (EB : tx_fold F (rtt_bw F bb0 cnt0 t false) 0 0 ([0] ++ tv_calls t false 0) = rtt_bt F bb0 cnt0 t false).
    { unfold rtt_bt, rtt_ns. change (if false then [1] else []) with (@nil Z). rewrite app_nil_r. reflexivity. }
    assert (EC : tx_capf 0 0 ([0] ++ tv_calls t false 0) = tx_capf 0 0 (rtt_ns t false)).
    { unfold rtt_ns. change (if false then [1] else []) with (@nil Z). rewrite app_nil_r. reflexivity. }
    change (negb (0 =? 0)) with false in INV, HCAP. rewrite EB in INV. rewrite EC in HCAP.
    apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc 0 copy t D ro oo fx' L A regs1 mem md Lam peak q want
      cap (Z_to_bv 64 0) ENT FL INV).
    + split; [rewrite HGr; reflexivity|]. split; [rewrite HGr; exact G8|]. split; [rewrite HGr; exact G9|].
      split; [rewrite HGr; exact G18|]. split; [rewrite HGr; exact G19|]. split; [rewrite HGr; exact G20|].
      split; [rewrite HGr; exact G21|]. split; [rewrite HGr; exact G3|]. split; [rewrite HGr; exact G4|].
      intros r Hr. rewrite HGr, <- (G22 r Hr).
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity.
    + exact RT.
    + rewrite EP in RH |- *. unfold wlen. rewrite WD. exact RH.
    + exact HCAP.
  - assert (HP1 : pretty = 1).
    { destruct PR as [P0 | P1]; [|exact P1]. exfalso. subst pretty. apply HS3. rewrite G19. reflexivity. }
    subst pretty.
    assert (EP : negb (1 =? 0) = true) by reflexivity.
    rewrite EP in RT, RH, QIN, QF, QB, WL, ROOM, INV, HCAP.
    set (txt := map (Z_to_bv 8) (concat (wvpieces t true 0))) in *.
    set (len := Z.of_nat (length (concat (wvpieces t true 0)))) in *.
    assert (WDT : wdoc t true = concat (wvpieces t true 0) ++ [10]) by (rewrite wdoc_split; reflexivity).
    assert (EWL : wlen t true = len + 1) by (unfold wlen, len; rewrite WDT, length_app; cbn [length]; lia).
    assert (HWC : 1 <= wcalls t true) by apply wcalls_pos.
    assert (HWCAP : wlen t true + 1 <= wcap t true) by (apply wcap_ge; lia).
    assert (K1 : getr regs1 1 = Z_to_bv 64 0x14e0c) by (rewrite HGr; reflexivity).
    assert (K2 : getr regs1 2 = Z_to_bv 64 (S - 112)) by (rewrite HGr; reflexivity).
    assert (K3 : getr regs1 3 = getr regs 3) by (rewrite HGr; reflexivity).
    assert (K4 : getr regs1 4 = getr regs 4) by (rewrite HGr; reflexivity).
    assert (K8 : getr regs1 8 = getr regs 8) by (rewrite HGr; reflexivity).
    assert (K9 : getr regs1 9 = getr regs 9) by (rewrite HGr; reflexivity).
    assert (K10 : getr regs1 10 = Z_to_bv 64 (S - 112)) by (rewrite HGr; reflexivity).
    assert (K11 : getr regs1 11 = Z_to_bv 64 0x10392) by (rewrite HGr; reflexivity).
    assert (K12 : getr regs1 12 = Z_to_bv 64 1) by (rewrite HGr; reflexivity).
    assert (K18 : getr regs1 18 = getr regs 18) by (rewrite HGr; reflexivity).
    assert (K19 : getr regs1 19 = getr regs 19) by (rewrite HGr; reflexivity).
    assert (K20 : getr regs1 20 = getr regs 20) by (rewrite HGr; reflexivity).
    assert (K21 : getr regs1 21 = getr regs 21) by (rewrite HGr; reflexivity).
    assert (K22 : forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite HGr.
      assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
    assert (HS1 : spZ regs1 = S - 112) by (unfold spZ; rewrite K2; apply ra_uns; lia).
    assert (CTX : ctx_owned B API) by exact nl_ctx.
    assert (LB : forall a k, In (a, k) Lam -> 0 <= k /\ In (a - 16, k + 16) (blocks L A)).
    { intros a k Hin. pose proof LED as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB _ Hin) as (Hk & Hb & _ & _). cbn [fst snd] in Hk, Hb. split; [exact Hk | exact Hb]. }
    assert (WANT : cap = 0 \/ (0 < cap /\ In (want, cap) (blocks L A))).
    { destruct TINV as (_ & [(C0 & _) | (Cp & Hwin & _)]); [left; exact C0 | right; split; assumption]. }
    assert (WLOW : forall x, want <= x < want + cap -> 4096 <= x < alloc_ceiling /\ ~ in_img B x).
    { intros x Hx. exact (inv_low B API HSEG ERRB AX CTX L A mem md want len cap txt x MRc TINV Hx). }
    assert (HZS : zsum ([0] ++ tv_calls t true 0) = len).
    { unfold len. rewrite zsum_app. cbn [zsum]. unfold tv_calls. rewrite zsum_plen, tvp_concat. lia. }
    assert (ROOMN : cap < len + 1 + 1 ->
      rf_room F (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0)) (2 * (len + 1 + 1))).
    { destruct ROOM as (_ & RTX & _). unfold rtt_ns in RTX. change (if true then [1] else []) with [1] in RTX.
      rewrite app_assoc in RTX. apply tx_rooms_app in RTX. destruct RTX as [_ RTX]. cbn [tx_rooms] in RTX.
      rewrite Z.add_0_l, HZS, <- HCAP in RTX. exact (proj1 RTX). }
    assert (NLI : in_img B 0x10392).
    { apply (rg_img_range B API HSEG AX FG 0x10392 (0x10392 + 1)); [vm_compute; reflexivity | lia]. }
    eapply SR_bind.
    { change (Z_to_bv 64 0x14f08) with (Z_to_bv 64 TX_PUT).
      apply (nl_put_ret B API F (TXP fx') L A regs1 mem md (S - 112) 0x10392 1 want len cap txt [Z_to_bv 8 10]
        (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0))).
      - apply (call_pre_k_mid B API HSEG AX FG RTT_K L0 A0 regs0 mem0 md0 (rtt_writes 0) L A mem md regs1 TX_STACK 112
          PRE0 RS INIT); [exact HS1 | rewrite HS1; lia | rewrite K4; exact G4 | rewrite K1; ra_ret | lia | lia | lia].
      - exact INIT.
      - exact (proj1 RD).
      - exact K10.
      - exact K11.
      - exact K12.
      - lia.
      - lia.
      - lia.
      - exact TW.
      - exact Wr.
      - exact Lr.
      - exact Cr.
      - exact TREC.
      - exact TINV.
      - lia.
      - lia.
      - lia.
      - intros i Hi. cbn [length Z.of_nat] in Hi. assert (i = 0) as -> by lia.
        destruct (img_nl (ms_segs B) mem HSEG (proj1 RD)) as [_ E]. exact E.
      - reflexivity.
      - intros i Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r.
        split; [lia|]. split; [rewrite HS1; lia|]. split.
        { intros Hx. destruct WANT as [C0 | (Cp & Hwin)]; [lia|]. exact (proj2 (WLOW _ Hx) NLI). }
        right. right. left. destruct (img_nl (ms_segs B) mem HSEG (proj1 RD)) as [E _]. exact E.
      - rewrite EWL in WL. lia.
      - exact RES.
      - exact ROOMN. }
    intros c' (L' & A' & regs' & mem' & md' & b1 & cap1 & -> & RP & RX & KZ).
    rewrite K1.
    pose proof RX as (FR & LENR & BK & OLD & NB1 & TR' & TW' & TINV' & RA' & GK & IN' & ZS & CAPF & RES').
    pose proof FR as (MR' & WF' & BD' & LL' & PA' & MD' & HI' & UB' & SW').
    assert (B1 : cap1 = 0 \/ (0 < cap1 /\ In (b1, cap1) (blocks L' A'))).
    { destruct TINV' as (_ & [(C0 & _) | (Cp & Hwin & _)]); [left; exact C0 | right; split; assumption]. }
    assert (B1LOW : forall x, b1 <= x < b1 + cap1 -> 4096 <= x < alloc_ceiling /\ ~ in_img B x).
    { intros x Hx. exact (inv_low B API HSEG ERRB AX CTX L' A' mem' md' b1 _ cap1 _ x MR' TINV' Hx). }
    assert (STEP0 : rstep B API TX_STACK (spZ regs1) (tx_writes (S - 112) want cap b1 cap1) (fun a => a = want)
      L A mem md L' A' mem' md').
    { apply (rstep_of_tx_frame B API HSEG AX FG TX_STACK regs1 _ (fun a => a = want) L A mem md L' A' mem' md' MRc FR).
      - intros _. exact IN'.
      - intros a k Hin Hk Hne. refine (proj1 (OLD a k Hin _)). intros X. injection X as X1 X2. exact (Hne X1).
      - intros a k i Hin Hne Hi _. exact (BK a k i Hin Hne Hi). }
    assert (STEP : rstep B API TX_STACK (S - 112) (tx_writes (S - 112) want cap b1 cap1) (fun a => a = want)
      L A mem md L' A' mem' md') by (rewrite HS1 in STEP0; exact STEP0).
    assert (LAMW : forall a k, In (a, k) Lam -> ~ (a - 16 = want) /\
      forall i, - 16 <= i < k -> ~ tx_writes (S - 112) want cap b1 cap1 (a + i)).
    { intros a k Hin. destruct (LB a k Hin) as (Hk & Hb). pose proof (WNL a k Hin) as Hw.
      destruct (rg_blk B API HSEG AX FG L A mem md (a - 16) (k + 16) 0 MRc Hb ltac:(lia)) as (_ & Hb1 & Hb2 & _).
      split; [exact Hw|]. intros i Hi [Hx|[Hx|Hx]].
      - lia.
      - destruct WANT as [C0 | (Cp & Hwin)]; [lia|].
        apply (blocks_apart B API HSEG AX FG L A mem md want cap (a - 16) (k + 16) (a + i) MRc Hwin Hb
          (fun e => Hw (eq_sym e)) Hx). lia.
      - destruct B1 as [C0 | (Cp & Hwin)]; [lia|].
        destruct (OLD (a - 16) (k + 16) Hb) as [Hb' _]. { intros X. injection X as X1 X2. exact (Hw X1). }
        pose proof (NB1 (a - 16) (k + 16) Hb ltac:(lia) Hw) as Hn1.
        apply (blocks_apart B API HSEG AX FG L' A' mem' md' b1 cap1 (a - 16) (k + 16) (a + i) MR' Hwin Hb'
          (fun e => Hn1 (eq_sym e)) Hx). lia. }
    assert (DINL : forall bk, In bk D -> In bk Lam).
    { intros bk Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact (DIN bk Hb). }
    pose proof (ra_node_top _ _ _ _ _ _ NODE) as DOCT.
    assert (EBT : rtt_bt F bb0 cnt0 t true =
      tx_fold F (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0)) len cap [1]).
    { unfold rtt_bt, rtt_ns. change (if true then [1] else []) with [1].
      rewrite app_assoc, tx_fold_app, Z.add_0_l, HZS, <- HCAP. reflexivity. }
    assert (INV2 : @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx' L' A' mem' md'
      [(q, wcap t true)] Lam peak (cnt0 + wcalls t true) (rtt_bt F bb0 cnt0 t true)).
    { apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc 1 copy t D fx' L A mem md
        [(q, wcap t true)] Lam peak (cnt0 + wcalls t true) (tx_fold F (rtt_bw F bb0 cnt0 t true) 0 0 ([0] ++ tv_calls t true 0))
        TX_STACK (tx_writes (S - 112) want cap b1 cap1)
        (fun a => a = want) fx' L' A' mem' md' [(q, wcap t true)] Lam peak (cnt0 + wcalls t true) (rtt_bt F bb0 cnt0 t true)
        ENT INV STEP); try lia.
      - intros a [Hx|[Hx|Hx]].
        + right. left. lia.
        + right. right. destruct (WLOW a Hx) as [Hlo Hni]. split; [lia|]. split; [exact Hni|].
          intros b k Hin Hb Hy. destruct WANT as [C0 | (Cp & Hwin)]; [lia|].
          exact (blocks_apart B API HSEG AX FG L A mem md want cap b k a MRc Hwin Hin (fun e => Hb (eq_sym e)) Hx Hy).
        + right. right. destruct (B1LOW a Hx) as [Hlo Hni]. split; [lia|]. split; [exact Hni|].
          intros b k Hin Hb Hy. destruct B1 as [C0 | (Cp & Hwin)]; [lia|].
          destruct (Z_lt_le_dec 0 k) as [Hk|Hk]; [|lia].
          destruct (OLD b k Hin) as [Hin' _]. { intros X. injection X as X1 X2. exact (Hb X1). }
          pose proof (NB1 b k Hin Hk Hb) as Hn1.
          exact (blocks_apart B API HSEG AX FG L' A' mem' md' b1 cap1 b k a MR' Hwin Hin' (fun e => Hn1 (eq_sym e)) Hx Hy).
      - intros a Ha [Hx|[Hx|Hx]].
        + replace a with (S - 112 + (a - (S - 112))) by lia. apply TW'. lia.
        + destruct (WLOW a Hx). lia.
        + destruct (B1LOW a Hx). lia.
      - intros a k Hin Hk E. exact (WNB a k Hin Hk E).
      - exact KZ.
      - exact RA'.
      - exact FRM.
      - intros r Hr. reflexivity.
      - apply (ledger_rstep B API HSEG AX FG TX_STACK (S - 112) _ (fun a => a = want) L A mem md L' A' mem' md' Lam peak
          (cnt0 + wcalls t true) (2 ^ 64 - 1) MRc LED STEP).
        + intros a Ha. pose proof (HST a Ha). split; [unfold rwin; rewrite HERR; lia|].
          destruct (statics_img B API HSEG AX FG a Ha) as [Hi _].
          intros [Hx|[Hx|Hx]]; [lia | exact (proj2 (WLOW a Hx) Hi) | exact (proj2 (B1LOW a Hx) Hi)].
        + exact LAMW.
      - exact PERM.
      - apply (pj_node_rstep B API HSEG AX FG TX_STACK (S - 112) _ (fun a => a = want) L A mem md L' A' mem' md' Lam Lam
          peak (cnt0 + wcalls t true) (2 ^ 64 - 1) doc t D MRc LED NODE DINL STEP); [lia | exact DOCT | | |
          exact (fun bk h => h)].
        + intros i Hi. split; [unfold rwin; rewrite HERR; lia|].
          intros [Hx|[Hx|Hx]]; [lia | destruct (WLOW _ Hx); lia | destruct (B1LOW _ Hx); lia].
        + intros a k Hin. destruct (LAMW a k (DINL _ Hin)) as [H1 H2]. split; [exact H1|].
          intros i Hi. apply H2. lia.
      - rewrite EBT. exact RES'. }
    assert (ET : map (Z_to_bv 8) (wdoc t true) = txt ++ [Z_to_bv 8 10]) by (unfold txt; rewrite WDT, map_app; reflexivity).
    apply (NEXT L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 bb0 doc 1 copy t D ro oo fx' L' A' regs' mem' md' Lam peak
      q b1 cap1 (Z_to_bv 64 1) ENT FL INV2).
    + split; [etransitivity; [apply (RP 2); unfold callee_saved; lia | exact K2]|].
      split; [etransitivity; [apply (RP 8); unfold callee_saved; lia | etransitivity; [exact K8 | exact G8]]|].
      split; [etransitivity; [apply (RP 9); unfold callee_saved; lia | etransitivity; [exact K9 | exact G9]]|].
      split; [etransitivity; [apply (RP 18); unfold callee_saved; lia | etransitivity; [exact K18 | exact G18]]|].
      split; [etransitivity; [apply (RP 19); unfold callee_saved; lia | etransitivity; [exact K19 | exact G19]]|].
      split; [etransitivity; [apply (RP 20); unfold callee_saved; lia | etransitivity; [exact K20 | exact G20]]|].
      split; [etransitivity; [apply (RP 21); unfold callee_saved; lia | etransitivity; [exact K21 | exact G21]]|].
      split; [etransitivity; [apply (RP 3); unfold callee_saved; lia | etransitivity; [exact K3 | exact G3]]|].
      split; [etransitivity; [apply (RP 4); unfold callee_saved; lia | etransitivity; [exact K4 | exact G4]]|].
      intros r Hr. etransitivity; [apply (RP r); unfold callee_saved; lia |
        etransitivity; [exact (K22 r Hr) | exact (G22 r Hr)]].
    + rewrite EP. split; [exact Q0|]. split; [exact QIN|]. split; [exact QNB|]. split; [exact QF|].
      apply (ia_bytes B mem mem' q _ QB). intros i Hi.
      rewrite length_map, length_app in Hi. cbn [length] in Hi. unfold wlen in HWCAP.
      destruct (LB q (wcap t true) QIN) as (_ & Hb).
      pose proof (BK (q - 16) (wcap t true + 16) (i + 16) Hb (WNL q (wcap t true) QIN) ltac:(lia)) as E.
      replace (q - 16 + (i + 16)) with (q + i) in E by lia. exact E.
    + rewrite EP, EWL, ET.
      destruct (inv_range B API HSEG ERRB AX CTX L' A' mem' md' b1 _ cap1 _ MR' TINV') as (Rb1 & _ & Rc1 & _).
      cbn [length Z.of_nat] in TR', TINV'.
      split; [exact Rb1|]. split; [unfold len; lia|]. split; [exact Rc1|].
      split; [exact TR'|]. split; [exact TW'|]. split; [exact TINV'|].
      split.
      { intros a k Hin Hk. pose proof (KBc a k Hin Hk ltac:(intros [])) as Hin1.
        exact (NB1 a k Hin1 Hk (WNB a k Hin Hk)). }
      intros a n Hin. destruct (LB a n Hin) as (Hn & Hb).
      exact (NB1 (a - 16) (n + 16) Hb ltac:(lia) (WNL a n Hin)).
    + rewrite CAPF. unfold rtt_ns. change (negb (1 =? 0)) with true. change (if true then [1] else []) with [1].
      rewrite app_assoc, tx_capf_app, Z.add_0_l, HZS, <- HCAP. reflexivity.
Qed.

End S.
