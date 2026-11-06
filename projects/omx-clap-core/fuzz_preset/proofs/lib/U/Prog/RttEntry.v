From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterValue WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import WriterRet PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls RttGlue RttModel RttBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require RttRunsA strtod_c parse_noting_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rte_stk_sub : forall s m lo hi lo' hi', Frame.stk s m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  Frame.stk s m lo' hi'.
Proof. intros s m lo hi lo' hi' (H1 & H2 & H) Hl Hh Hlh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma rte_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

Lemma rte_node_top : forall segs m lb p u Du, pj_node segs m lb p u Du -> p + 56 <= 2 ^ 64.
Proof.
  intros segs m lb p u Du H. destruct u; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & ((_ & _ & Htop & _) & _) & _); exact Htop.
Qed.

Lemma rte_depth : forall t : jv, (depth t <= 32)%nat -> (depth t <= 2 ^ 31 - 1)%nat.
Proof.
  intros t H. assert (H6 : (2 ^ 6 <= 2 ^ 31)%nat) by (apply Nat.pow_le_mono_r; lia).
  change (2 ^ 6)%nat with 64%nat in H6. lia.
Qed.

(* the number of pj_write's buffer growths, bounded by its final size (the same proof as the cmp stage's rf_wcalls) *)
Lemma rte_dbl_ge : forall f c need, 0 <= c -> c <= dbl f c need.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (Z.leb_spec need c) as [H|H]; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma rte_dbl_le : forall f c need, 0 < c -> dbl f c need <= Z.max c (2 * need).
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [dbl]; [lia|].
  destruct (Z.leb_spec need c) as [H|H]; [lia|]. pose proof (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma rte_dbl_S : forall f c need, c < need -> dbl (S f) c need = dbl f (2 * c) need.
Proof. intros f c need H. cbn [dbl]. destruct (Z.leb_spec need c) as [H'|H']; [lia | reflexivity]. Qed.

Lemma rte_newcap : forall c need, (c = 0 \/ 4096 <= c) -> c < need ->
  c + 4096 <= newcap c need /\ newcap c need <= Z.max 4096 (2 * need).
Proof.
  intros c need Hc Hn. unfold newcap.
  destruct (Z.eqb_spec c 0) as [->|H0]; cbv beta iota.
  - pose proof (rte_dbl_ge 64 4096 need ltac:(lia)). pose proof (rte_dbl_le 64 4096 need ltac:(lia)). lia.
  - destruct Hc as [Hc|Hc]; [contradiction|]. rewrite (rte_dbl_S 63 c need Hn).
    pose proof (rte_dbl_ge 63 (2 * c) need ltac:(lia)). pose proof (rte_dbl_le 63 (2 * c) need ltac:(lia)). lia.
Qed.

Lemma rte_zsum_nn : forall ls, Forall (fun l => 0 <= l) ls -> 0 <= zsum ls.
Proof. intros ls H. induction H as [|l ls Hl _ IH]; cbn [zsum]; lia. Qed.

Lemma rte_gc : forall ls x c M, (c = 0 \/ 4096 <= c) -> Forall (fun l => 0 <= l) ls -> x + zsum ls + 1 <= M ->
  c + 4096 * Z.of_nat (length (grow_calls x c ls)) <= Z.max c (Z.max 4096 (2 * M)).
Proof.
  induction ls as [|l ls IH]; intros x c M Hc Hl HM; cbn [grow_calls length zsum] in *.
  - lia.
  - apply Forall_cons_iff in Hl. destruct Hl as [Hl0 Hls]. pose proof (rte_zsum_nn ls Hls) as Z0.
    destruct (Z.ltb_spec c (x + l + 1)) as [H|H]; cbn [length].
    + destruct (rte_newcap c (x + l + 1) Hc H) as [N1 N2].
      pose proof (IH (x + l) (newcap c (x + l + 1)) M ltac:(right; lia) Hls ltac:(lia)) as IH'. lia.
    + pose proof (IH (x + l) c M Hc Hls ltac:(lia)) as IH'. lia.
Qed.

Lemma rte_wcalls : forall t p, 4096 * wcalls t p <= Z.max 4096 (2 * (wlen t p + 1)).
Proof.
  intros t p. unfold wcalls.
  assert (HF : Forall (fun l => 0 <= l) (piece_lens (wdpieces t p))).
  { apply Forall_forall. intros l Hl. unfold piece_lens in Hl. apply in_map_iff in Hl. destruct Hl as (b & <- & _). lia. }
  assert (HZ : zsum (piece_lens (wdpieces t p)) = wlen t p).
  { change (piece_lens (wdpieces t p)) with (plen (wdpieces t p)). rewrite zsum_plen. reflexivity. }
  pose proof (rte_gc (piece_lens (wdpieces t p)) 0 0 (wlen t p + 1) (or_introl eq_refl) HF ltac:(lia)) as H.
  lia.
Qed.

Ltac rte_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM;
  subst R pc m; clear E.

Ltac rte_ret := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
Variable kw : jv -> Z.
Hypothesis KW : forall t, (depth t <= 32)%nat -> 0 <= kw t <= PJ_PARSE_K.
Hypothesis PJW : @pj_write_hyp fx rc B API F kw.
Hypothesis NEXT : stg_tx1_st B API F.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma rte_kA : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz HE HS HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite HSEG. eapply Exec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma rte_ro_munch : forall m m' lo hi, MemNorm.ro_agree (ms_segs B) m -> Frame.munch [(lo, hi)] m m' ->
  alloc_ceiling <= lo -> MemNorm.ro_agree (ms_segs B) m'.
Proof.
  intros m m' lo hi Hro HM Hlo a Ha.
  assert (Hlt : bv_unsigned a < alloc_ceiling).
  { unfold MemNorm.ro_agree, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr in Ha.
    destruct (find_segment (ms_segs B) (bv_unsigned a) 1) as [seg|] eqn:Ef; [|discriminate].
    destruct (rtt_img_low B API HSEG FA) as [_ HI]. exact (proj2 (HI _ _ Ef)). }
  assert (E : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd (ms_segs B) m' a =
              OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd (ms_segs B) m a).
  { unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.mrd. rewrite (HM a); [reflexivity|].
    apply outside_one. lia. }
  rewrite E. exact (Hro a Ha).
Qed.

Theorem rtt_entry_holds : round_trip_text_contract B API F.
Proof.
  unfold round_trip_text_contract.
  intros L A regs mem md Lam peak cnt b doc pretty copy t D ro oo REN INIT LED CNT RES R10 R11 R12 PR NODE DIN DOC0
    DOCS PWF DEP WL COPY ROOM RO1 OO1 BRO BOO.
  set (p := negb (pretty =? 0)) in *.
  assert (ENT : rtt_ent B API F L A regs mem md Lam peak cnt b doc pretty copy t D).
  { exact (conj REN (conj INIT (conj LED (conj CNT (conj RES (conj R10 (conj R11 (conj R12 (conj PR (conj NODE
      (conj DIN (conj DOC0 (conj DOCS (conj PWF (conj DEP (conj WL (conj COPY ROOM))))))))))))))))). }
  pose proof (conj RO1 (conj OO1 (conj BRO BOO))) as FL.
  pose proof REN as (SEGB & TPB & ERRB & GOTB & GUARDB & PRE0 & SP47 & GT & FRM0 & RD0).
  pose proof PRE0 as (MR0 & WF0 & BD0 & RA0 & SP16 & SPC & SP63 & WIN0 & TP0 & ERRW0 & AUX0).
  pose proof alloc_ceiling_val as HCV.
  pose proof (KW t DEP) as HKW.
  assert (HRK : RTT_K = 112 + parse_noting_c.PN_K) by (unfold RTT_K, RTT_F; reflexivity).
  assert (HPN : PJ_PARSE_K <= parse_noting_c.PN_K) by (unfold parse_noting_c.PN_K, parse_noting_c.PN_F; lia).
  assert (HERR : errno_addr B = strtod_c.STRTOD_ERRNO) by exact ERRB.
  unfold strtod_c.STRTOD_ERRNO in HERR.
  set (S := spZ regs) in *.
  assert (HSP : Z_to_bv 64 S = getr regs 2).
  { unfold S, spZ. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. }
  assert (HST : forall a, alloc_statics a -> GL_FAIL <= a < GL_COUNT + 8).
  { intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL, GL_FAIL, GL_COUNT in *. lia. }
  unfold GL_FAIL, GL_COUNT in HST.
  destruct (kb_md B API L A mem md MR0) as (Hh & Hz).
  pose proof (kb_stk B API (rtt_img_low B API HSEG FA) RTT_K L A regs mem md PRE0 ltac:(lia)) as Hstk.
  pose proof (rte_stk_sub _ mem _ _ (S - 56) S Hstk ltac:(lia) ltac:(lia) ltac:(lia)) as Hstk1.
  rewrite HSEG in Hstk1.
  eapply (rte_kA fx regs _ mem md _ _ Hh Hz).
  { unfold rmk. rewrite <- HSP.
    apply (RttRunsA.rtt_seg0 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem S); [lia | exact Hstk1]. }
  { intros ms' (m' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E). eexists _, _, _. exact E. }
  intros R pc' mem1 regs1 HQ HGr.
  destruct HQ as (m1 & MU & WM & B8 & B16 & B24 & B32 & B40 & B48 & B56 & WR & E).
  rte_inj E R pc' mem1.
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x15364) by (rewrite HGr; reflexivity).
  assert (G2 : getr regs1 2 = Z_to_bv 64 (S - 112)) by (rewrite HGr; reflexivity).
  assert (G3 : getr regs1 3 = getr regs 3) by (rewrite HGr; reflexivity).
  assert (G4 : getr regs1 4 = getr regs 4) by (rewrite HGr; reflexivity).
  assert (G8 : getr regs1 8 = Z_to_bv 64 copy) by (rewrite HGr; exact R12).
  assert (G9 : getr regs1 9 = getr regs 10) by (rewrite HGr; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 doc) by (rewrite HGr; exact R10).
  assert (G11 : getr regs1 11 = Z_to_bv 64 pretty) by (rewrite HGr; exact R11).
  assert (G18 : getr regs1 18 = getr regs 18) by (rewrite HGr; reflexivity).
  assert (G19 : getr regs1 19 = Z_to_bv 64 pretty) by (rewrite HGr; exact R11).
  assert (G20 : getr regs1 20 = getr regs 20) by (rewrite HGr; reflexivity).
  assert (G21 : getr regs1 21 = getr regs 21) by (rewrite HGr; reflexivity).
  assert (G22 : forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite HGr.
    assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->| ->]]]]]; reflexivity. }
  assert (HS1 : spZ regs1 = S - 112) by (unfold spZ; rewrite G2; apply rte_uns; lia).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 56 <= a < S) ->
    mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)).
  { intros a Ha Hn. assert (Ho : Frame.outside [(S - 56, S)] a) by (apply outside_one; lia).
    split; [exact (mbyte_munch (ms_segs B) _ mem m1 a MU Ha Ho) | exact (writable_munch (ms_segs B) _ mem m1 a MU Ha Ho)]. }
  assert (ST0e : rstep B API RTT_K S (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (rstep_of_munch B API HSEG AX FG RTT_K S (fun _ => False) (fun _ => False) L A mem m1 md [(S - 56, S)]
      MR0 WF0 BD0).
    - intros a [Ha|Ha]; [apply WIN0; exact Ha | apply ERRW0; exact Ha].
    - exact MU.
    - rewrite HSEG. exact WM.
    - intros x Hx Hn. left. unfold rwin. left.
      destruct (Z_lt_le_dec x (S - 56)) as [H1|H1]; [exfalso; apply Hn; apply outside_one; lia|].
      destruct (Z_lt_le_dec x S) as [H2|H2]; [lia | exfalso; apply Hn; apply outside_one; lia].
    - intros x Hx _. apply outside_one. lia. }
  pose proof ST0e as (MR1 & _).
  assert (RA1 : MemNorm.ro_agree (ms_segs B) m1).
  { apply (rte_ro_munch mem m1 (S - 56) S); [exact (proj1 RD0) | exact MU | lia]. }
  assert (RD1 : rd_cells B m1) by exact (rd_cells_of_MR B API HSEG AX FG L A m1 md MR1 RA1).
  assert (LED1 : ledger B L A m1 Lam peak cnt (2 ^ 64 - 1)).
  { apply (ledger_rstep B API HSEG AX FG RTT_K S (fun _ => False) (fun _ => False) L A mem md L A m1 md Lam peak cnt
      (2 ^ 64 - 1) MR0 LED ST0e).
    - intros a Ha. pose proof (HST a Ha). split; [unfold rwin; rewrite HERR; lia | intros []].
    - intros a k _. split; [intros [] | intros i _ []]. }
  pose proof (rte_node_top _ _ _ _ _ _ NODE) as DOCT.
  assert (NODE1 : pj_node (ms_segs B) m1 (lin Lam) doc t D).
  { apply (pj_node_rstep B API HSEG AX FG RTT_K S (fun _ => False) (fun _ => False) L A mem md L A m1 md Lam Lam peak cnt
      (2 ^ 64 - 1) doc t D MR0 LED NODE DIN ST0e); [lia | exact DOCT | | | exact (fun bk h => h)].
    - intros i Hi. split; [unfold rwin; rewrite HERR; lia | intros []].
    - intros a k _. split; [intros [] | intros i _ []]. }
  assert (ST0 : rstep B API RTT_K S (rtt_writes 0) (fun _ => False) L A mem md L A m1 md).
  { apply (rstep_E B API HSEG AX FG RTT_K S (fun _ => False) (rtt_writes 0) (fun _ => False) (fun _ => False)
      L A mem md L A m1 md ST0e); intros a []. }
  assert (INV0 : @rtt_inv fx rc B API F L A regs mem md Lam peak doc copy t D fx L A m1 md [] Lam peak cnt b).
  { unfold rtt_inv. fold S.
    split; [exact ST0|].
    split; [intros a k Hin _; exact Hin|].
    split; [exact INIT|].
    split; [exact RD1|].
    split; [exact FRM0|].
    split; [intros r Hr; reflexivity|].
    split; [exact LED1|].
    split; [lia|].
    split; [apply Permutation_refl|].
    split; [exact NODE1|].
    split; [exact RES|].
    split.
    { intros Hc. destruct COPY as [C0|(_ & (Hal & Hstk2) & Hs & _)]; [contradiction|].
      split; [exact Hal|]. apply (ia_stk B mem); [exact Hstk2|]. intros a Ha.
      destruct Hstk2 as (Hc1 & Hc2 & _). apply KEEP; lia. }
    rewrite HSEG.
    split; [exact B8|]. split; [exact B16|]. split; [exact B24|]. split; [exact B32|]. split; [exact B40|].
    split; [exact B48|]. split; [exact B56|].
    exact WR. }
  pose proof ROOM as (RMW & RMT & RMP).
  assert (HWC : 1 <= wcalls t p) by apply wcalls_pos.
  assert (HTC : 0 <= Z.of_nat (PjRoundTrip.tcalls t)) by lia.
  assert (HWL : 0 <= wlen t p) by (unfold wlen; lia).
  assert (HWCAP : wlen t p + 1 <= wcap t p) by (apply wcap_ge; lia).
  eapply SR_bind; [apply (PJW L A regs1 m1 md doc pretty t D Lam peak cnt (2 ^ 64 - 1) b) |].
  all: try fold p.
  - apply (reader_env_mid B API HSEG AX FG RTT_K L A regs mem md (fun _ => False) L A m1 md regs1 (kw t) 112 REN ST0e
      INIT RD1 FRM0); [exact HS1 | rewrite HS1; lia | exact G4 | rewrite G1; rte_ret | lia | lia | lia].
  - exact INIT.
  - exact LED1.
  - exact RES.
  - exact G10.
  - exact G11.
  - lia.
  - exact NODE1.
  - exact DIN.
  - left. lia.
  - exact WL.
  - exact (rte_depth t DEP).
  - exact RMW.
  - pose proof (rte_wcalls t p) as HWB. lia.
  - intros c' (fx1 & L1 & A1 & regs2 & m2 & md1 & Lam1 & peak1 & cnt1 & fail1 & q & b1 & -> & FRM1 & FRG1 & RP1 & RD2 &
      LED2 & PK1 & RES1 & R10' & NODE2 & OK & FAIL).
    assert (HCW : cnt + wcalls t p <= 2 ^ 64 - 1).
    { destruct (Z_le_gt_dec (cnt + wcalls t p) (2 ^ 64 - 1)) as [H|H]; [exact H|].
      destruct (FAIL ltac:(lia)) as (_ & Ec & _). pose proof LED2 as (_ & _ & Hc & _). lia. }
    destruct (OK ltac:(right; lia)) as (Hq & Ecnt & Efail & Eb & PERM & NEW & FWD & TXT).
    subst cnt1 fail1 b1.
    pose proof RP1 as (MR2 & _ & _ & _ & _ & _ & _ & UB & PA & RR & _).
    pose proof (rstep_of_rpost B API HSEG AX FG (kw t) L A regs1 m1 md alloc_statics (fun _ _ => False)
      L1 A1 regs2 m2 md1 RP1) as STEP.
    rewrite HS1 in STEP.
    rewrite G1.
    assert (HZ : forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (blocks L1 A1)).
    { intros a k Hin _. destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
      assert (Hq1 : In (q0, k) (user_blocks A1)) by (apply UB; [exact Hq0 | intros []]).
      rewrite <- (PA q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L1 A1 q0 k Hq1). }
    assert (INV1 : @rtt_inv fx rc B API F L A regs mem md Lam peak doc copy t D fx1 L1 A1 m2 md1 [(q, wcap t p)] Lam1 peak1
      (cnt + wcalls t p) (rtt_bw F b cnt t p)).
    { apply (inv_after B API F HSEG FA L A regs mem md Lam peak cnt b doc pretty copy t D fx L A m1 md [] Lam peak cnt b
        (kw t) alloc_statics (fun a => exists n : Z, False) fx1 L1 A1 m2 md1 [(q, wcap t p)] Lam1 peak1
        (cnt + wcalls t p) (rtt_bw F b cnt t p) ENT INV0 STEP); try lia.
      - intros a Ha. left. exact Ha.
      - intros a Ha Hs. pose proof (HST a Hs). lia.
      - intros a k _ _ (n & []).
      - exact HZ.
      - exact (proj1 RD2).
      - exact FRM1.
      - exact FRG1.
      - exact LED2.
      - exact PERM.
      - exact NODE2.
      - exact RES1. }
    pose proof LED2 as (_ & _ & _ & _ & _ & FB).
    rewrite Forall_forall in FB.
    assert (HQin : In (q, wcap t p) Lam1) by (apply (Permutation_in _ (Permutation_sym PERM)); left; reflexivity).
    destruct (FB _ HQin) as (Hk & Hblk & _ & _). cbn [fst snd] in Hk, Hblk.
    destruct (rg_blk B API HSEG AX FG L1 A1 m2 md1 (q - 16) (wcap t p + 16) 0 MR2 Hblk ltac:(lia)) as (_ & Hq4 & _).
    apply (NEXT L A regs mem md Lam peak cnt b doc pretty copy t D ro oo fx1 L1 A1 regs2 m2 md1 Lam1 peak1 q ENT FL INV1).
    + split; [etransitivity; [apply (RR 2); unfold callee_saved; lia | exact G2]|].
      split; [etransitivity; [apply (RR 8); unfold callee_saved; lia | exact G8]|].
      split; [etransitivity; [apply (RR 9); unfold callee_saved; lia | exact G9]|].
      split; [etransitivity; [apply (RR 18); unfold callee_saved; lia | exact G18]|].
      split; [etransitivity; [apply (RR 19); unfold callee_saved; lia | exact G19]|].
      split; [etransitivity; [apply (RR 20); unfold callee_saved; lia | exact G20]|].
      split; [etransitivity; [apply (RR 21); unfold callee_saved; lia | exact G21]|].
      split; [etransitivity; [apply (RR 3); unfold callee_saved; lia | exact G3]|].
      split; [etransitivity; [apply (RR 4); unfold callee_saved; lia | exact G4]|].
      intros r Hr. etransitivity; [apply (RR r); unfold callee_saved; lia | exact (G22 r Hr)].
    + exact R10'.
    + split; [lia|].
      split; [exact HQin|].
      split.
      { intros a k Hin Hk0 Ea. subst a.
        pose proof STEP as (_ & _ & _ & _ & KB & _).
        assert (NG : ~ (exists n : Z, (fun _ _ => False) (q - 16) n)) by (intros (n & [])).
        pose proof (KB (q - 16) k Hin Hk0 NG) as Hin1.
        pose proof (blocks_same_addr B API HSEG AX FG L1 A1 m2 md1 (q - 16) k (wcap t p + 16) MR2 Hin1 Hblk Hk0
          ltac:(lia)) as Ek.
        subst k. apply (NEW q (wcap t p)); [left; reflexivity | exact Hin]. }
      split; [exact FWD | exact TXT].
Qed.

End E.
