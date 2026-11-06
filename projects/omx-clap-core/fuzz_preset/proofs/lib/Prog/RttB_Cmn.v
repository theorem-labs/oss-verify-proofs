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
Ledger PjStruct ReaderRes tx_put_c TxRet WriterSpec WriterValue PjWriteHyp round_trip_text_c RttDefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import RttGlue RttModel RttBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require tx_put strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lb_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. exact (Mem.wa_unsigned z Hz). Qed.

Lemma lb_json_nil : json_read jr_strtod [] = None.
Proof. vm_compute. reflexivity. Qed.

Lemma lb_wdoc_ne : forall t p, PjRoundTrip.pj_wf jr_strtod t -> wdoc t p <> [].
Proof.
  intros t p H E. destruct (rtt_G9 t p H) as (H1 & _). rewrite E, lb_json_nil in H1. discriminate.
Qed.

Lemma lb_wlen_pos : forall t p, PjRoundTrip.pj_wf jr_strtod t -> 1 <= wlen t p.
Proof.
  intros t p H. unfold wlen. destruct (wdoc t p) as [|c l] eqn:E; [exfalso; exact (lb_wdoc_ne t p H E)|].
  cbn [length]. lia.
Qed.

Lemma lb_not_outside : forall W x, ~ Frame.outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [Frame.outside] in H.
  - exfalso. exact (H I).
  - destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
    + exists lo, hi. split; [left; reflexivity | lia].
    + destruct (IH x) as (l & h & Hin & Hx); [intros Ho; apply H; split; [lia | exact Ho]|].
      exists l, h. split; [right; exact Hin | exact Hx].
    + destruct (IH x) as (l & h & Hin & Hx); [intros Ho; apply H; split; [lia | exact Ho]|].
      exists l, h. split; [right; exact Hin | exact Hx].
Qed.

Lemma lb_node_top : forall segs m lb p t D, pj_node segs m lb p t D -> p + 56 <= 2 ^ 64.
Proof.
  intros segs m lb p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & ((_ & _ & Htop & _) & _) & _); exact Htop.
Qed.

Lemma lb_node_rw : forall segs m lb p t D, pj_node segs m lb p t D -> pj_rw segs m p.
Proof.
  intros segs m lb p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & (Hrw & _) & _); exact Hrw.
Qed.

Lemma lb_stk_present : forall segs m lo hi, 0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> present m a) ->
  Frame.stk segs m lo hi.
Proof.
  intros segs m lo hi H1 H2 HP. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (HP a Ha) as [b Hb]. split.
  - change (wview segs m (Z_to_bv 64 a) <> None). unfold wview. rewrite Hb. discriminate.
  - exists b. change (Mem.mrd segs m (Z_to_bv 64 a) = Some b). unfold Mem.mrd. rewrite Hb. reflexivity.
Qed.

Lemma lb_stk_wr : forall segs m lo hi a, Frame.stk segs m lo hi -> lo <= a < hi -> writable_at segs m a.
Proof. intros segs m lo hi a (_ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma lb_bytes_some : forall segs m a n, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> present m (a + i)) ->
  exists bs, length bs = n /\ Mem.bytes_at segs m a bs.
Proof.
  intros segs m a n. induction n as [|n IH]; intros H0 H1 HP.
  - exists []. split; [reflexivity|]. apply Mem.bytes_at_nil. lia.
  - destruct IH as (bs & Hl & Hb); [lia | lia | intros i Hi; apply HP; lia|].
    destruct (HP (Z.of_nat n) ltac:(lia)) as [b Hb'].
    exists (bs ++ [b]). split; [rewrite length_app, Hl; cbn [length]; lia|].
    apply Mem.bytes_at_app. split; [exact Hb|]. rewrite Hl.
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
    assert (i = 0%nat) by lia. subst i. cbn [nth_error].
    replace (a + Z.of_nat n + Z.of_nat 0) with (a + Z.of_nat n) by lia.
    unfold Mem.mrd, Mem.wa. rewrite Hb'. reflexivity.
Qed.

Lemma lb_perm_in : forall (X Lam Lam0 : list (Z * Z)) bk, Permutation Lam (X ++ Lam0) ->
  In bk X \/ In bk Lam0 -> In bk Lam.
Proof.
  intros X Lam Lam0 bk HP H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. exact H.
Qed.

Lemma lb_perm_in2 : forall (X Lam Lam0 : list (Z * Z)) bk, Permutation Lam (X ++ Lam0) ->
  In bk Lam -> In bk X \/ In bk Lam0.
Proof. intros X Lam Lam0 bk HP H. apply in_app_or. exact (Permutation_in _ HP H). Qed.

Ltac lb_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM;
  subst R pc m; clear E.

Ltac lb_ret := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.
#[local] Set Default Proof Using "All".

Let AX : AllocExtra B (aa_MR API) := rtt_AX B API HSEG FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a :=
  rtt_FG B API HSEG FA.

Lemma lb_run : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> ro_agree (ms_segs B) mem1 ->
  Exec.evt rsegs Q (MState.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' m0 mem' regs', Q (MState.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom rsegs)) ->
     mem_rel (ms_segs B) mem' m0 -> ro_same (ms_segs B) mem1 mem' -> (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz RA HE HS HK.
  apply (run_N B fx1 regs1 pc mem1 md1 Q P HSEG Hh Hz RA).
  - rewrite HSEG. exact HE.
  - intros ms HQ. rewrite HSEG. exact (HS ms HQ).
  - intros R pc' m0 mem' regs' HQ HR HO HG. rewrite HSEG in HQ. exact (HK R pc' m0 mem' regs' HQ HR HO HG).
Qed.

Lemma lb_env_fx : forall (f1 f2 : YK11.FPState) K L A regs mem md,
  @reader_env f1 rc B API K L A regs mem md -> frm_zero (@fp_csr f2) -> @reader_env f2 rc B API K L A regs mem md.
Proof.
  intros f1 f2 K L A regs mem md (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & H10) Hz.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj Hz H10))))))))).
Qed.

Lemma lb_mbytes : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> mbytes B m a bs ->
  Mem.bytes_at (ms_segs B) m a bs.
Proof.
  intros m a bs H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in H. exact H.
Qed.

Lemma lb_ro_false : forall a, 0 <= a < 2 ^ 64 -> (alloc_ceiling <= a \/ ~ in_img B a) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hc. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.ro_addr. rewrite (lb_uns a Ha).
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
  destruct Hc as [Hc|Hc].
  - destruct (rtt_img_low B API HSEG FA) as [_ HL]. pose proof (HL a seg F). lia.
  - apply Hc. rewrite HSEG in F. exact (tx_put.find_img B HSEG a seg (proj1 Ha) F).
Qed.

Lemma lb_present_norm : forall m a, 0 <= a < 2 ^ 64 -> (alloc_ceiling <= a \/ ~ in_img B a) ->
  present m a -> present (normalize (ms_segs B) m) a.
Proof.
  intros m a Ha Hc [b Hb]. exists b. unfold normalize. cbv beta. rewrite (lb_ro_false a Ha Hc). exact Hb.
Qed.

Lemma lb_stk_win : forall m lo hi, alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) m a) ->
  Frame.stk (ms_segs B) m lo hi /\ Frame.stk (ms_segs B) (normalize (ms_segs B) m) lo hi.
Proof.
  intros m lo hi H1 H2 HW. pose proof alloc_ceiling_val as HCV.
  assert (HP : forall a, lo <= a < hi -> present m a).
  { intros a Ha. apply (tx_put.present_of_writable B HSEG m a); [lia | left; lia | exact (HW a Ha)]. }
  split.
  - apply lb_stk_present; [lia | lia | exact HP].
  - apply lb_stk_present; [lia | lia |]. intros a Ha. apply lb_present_norm; [lia | left; lia | exact (HP a Ha)].
Qed.

Lemma lb_bytes_munch : forall W m m' a bs, Mem.bytes_at (ms_segs B) m a bs -> Frame.munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> Frame.outside W (a + i)) -> Mem.bytes_at (ms_segs B) m' a bs.
Proof.
  intros W m m' a bs Hb HM HO. pose proof (Mem.bytes_at_bound _ _ _ _ Hb) as Hr.
  apply (ia_bytes B m m' a bs Hb). intros i Hi.
  apply (mbyte_munch (ms_segs B) W m m'); [exact HM | lia | exact (HO i Hi)].
Qed.

Lemma lb_bytes_keep : forall m m' a bs, Mem.bytes_at (ms_segs B) m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  Mem.bytes_at (ms_segs B) m' a bs.
Proof. intros m m' a bs Hb HE. exact (ia_bytes B m m' a bs Hb HE). Qed.

Lemma lb_foot : forall L A mem md Lam peak cnt fail p (D : list (Z * Z)) x,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> (forall bk, In bk D -> In bk Lam) ->
  pj_foot p D x -> p <= x < p + 56 \/ (4112 <= x < alloc_ceiling /\ ~ in_img B x).
Proof.
  intros L A mem md Lam peak cnt fail p D x HM HL HD [Hx|((a & k) & Hb & Hx)]; [left; exact Hx|].
  right. unfold pj_holds in Hx. cbn [fst snd] in Hx.
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL (HD _ Hb)) as (R1 & R2 & _).
  split; [lia|]. replace x with (a + (x - a)) by lia.
  apply (ledger_block_not_img B L A mem Lam peak cnt fail a k (x - a) HL (HD _ Hb)). lia.
Qed.

Lemma lb_node_norm : forall L A mem md Lam peak cnt fail p t D,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> (forall bk, In bk D -> In bk Lam) ->
  ro_agree (ms_segs B) mem -> alloc_ceiling <= p -> pj_node (ms_segs B) mem (lin Lam) p t D ->
  pj_node (ms_segs B) (normalize (ms_segs B) mem) (lin Lam) p t D.
Proof.
  intros L A mem md Lam peak cnt fail p t D HM HL HD RA Hp HN.
  pose proof (lb_node_top _ _ _ _ _ _ HN) as Ht.
  apply (pj_node_normalize B API HSEG AX FG mem (lin Lam) p t D RA HN).
  intros x Hx. destruct (lb_foot L A mem md Lam peak cnt fail p D x HM HL HD Hx) as [H|(H1 & H2)].
  - pose proof alloc_ceiling_val. apply (lb_ro_false x); [lia | left; lia].
  - pose proof alloc_ceiling_val. apply (lb_ro_false x); [lia | right; exact H2].
Qed.

Lemma lb_inv_munch : forall (F : ResForm) L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D
    (fx1 : YK11.FPState) L A mem md X Lam peak cnt bnd mem' W Kc,
  @rtt_ent fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem md X Lam peak cnt bnd ->
  Frame.munch W mem mem' -> Frame.wmono (ms_segs B) mem mem' -> ro_agree (ms_segs B) mem' ->
  0 <= Kc -> 112 + Kc <= RTT_K ->
  (forall lo hi x, In (lo, hi) W -> lo <= x < hi -> spZ regs0 - 112 - Kc <= x < spZ regs0 - 112) ->
  @rtt_inv fx rc B API F L0 A0 regs0 mem0 md0 Lam0 peak0 doc copy t D fx1 L A mem' md X Lam peak cnt bnd.
Proof.
  intros F L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak cnt bnd mem' W Kc
    ENT INV HM HW RA' HK0 HK1 HWin.
  pose proof ENT as (REN & _ & _ & _ & _ & _ & _ & _ & _ & _ & DSUB & _ & DOCS & _ & _ & _ & _ & _).
  pose proof REN as (_ & _ & ERRB & _ & _ & PRE0 & _ & _ & _ & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & SPC & SP63 & _).
  pose proof INV as (RS & _ & _ & _ & FRM & _ & LED & _ & PERM & NODE & RES & _).
  pose proof RS as (MRc & WFc & BDc & _ & _ & _ & _ & _ & _ & WRc).
  pose proof alloc_ceiling_val as HCV.
  assert (HERR : errno_addr B = 0x347f4) by (rewrite ERRB; reflexivity).
  (* #102: the alloc.c words, by LedgerCells' names (Ledger's G_LIVE .. G_FAIL are the GL_ names) *)
  assert (HST : forall a, alloc_statics a -> GL_FAIL <= a < GL_COUNT + 8).
  { intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. unfold GL_FAIL, GL_COUNT. lia. }
  unfold GL_FAIL, GL_COUNT in HST.
  assert (DL : forall bk, In bk D -> In bk Lam).
  { intros bk Hb. apply (lb_perm_in X Lam Lam0 bk PERM). right. exact (DSUB bk Hb). }
  assert (ST : rstep B API Kc (spZ regs0 - 112) (fun _ => False) (fun _ => False) L A mem md L A mem' md).
  { apply (rstep_of_munch B API HSEG AX FG Kc (spZ regs0 - 112) (fun _ => False) (fun _ => False) L A mem mem' md W
      MRc WFc BDc).
    - intros a Ha. apply WRc. unfold rwin in *. lia.
    - exact HM.
    - exact HW.
    - intros x _ Ho. left. destruct (lb_not_outside W x Ho) as (lo & hi & Hin & Hx).
      unfold rwin. left. exact (HWin lo hi x Hin Hx).
    - intros x Hx _. apply kb_outside. intros lo hi Hin Hlh. pose proof (HWin lo hi x Hin Hlh). lia. }
  apply (inv_after B API F HSEG FA L0 A0 regs0 mem0 md0 Lam0 peak0 cnt0 b0 doc pretty copy t D fx1 L A mem md X Lam peak
    cnt bnd Kc (fun _ => False) (fun _ => False) fx1 L A mem' md X Lam peak cnt bnd ENT INV ST HK0 HK1).
  - intros a [].
  - intros a _ [].
  - intros a k _ _ [].
  - intros a k Hin _. exact Hin.
  - exact RA'.
  - exact FRM.
  - intros r _. reflexivity.
  - apply (ledger_rstep B API HSEG AX FG Kc (spZ regs0 - 112) (fun _ => False) (fun _ => False) L A mem md L A mem' md
      Lam peak cnt (2 ^ 64 - 1) MRc LED ST).
    + intros a Ha. pose proof (HST a Ha). split; [unfold rwin; rewrite HERR; lia | intros []].
    + intros a k _. split; [intros [] | intros i _ []].
  - lia.
  - exact PERM.
  - apply (pj_node_rstep B API HSEG AX FG Kc (spZ regs0 - 112) (fun _ => False) (fun _ => False) L A mem md L A mem' md
      Lam Lam peak cnt (2 ^ 64 - 1) doc t D MRc LED NODE DL ST); [lia | exact (lb_node_top _ _ _ _ _ _ NODE) | | |
      exact (fun bk h => h)].
    + intros i Hi. split; [unfold rwin; rewrite HERR; lia | intros []].
    + intros a k _. split; [intros [] | intros i _ []].
  - exact RES.
Qed.

Lemma lb_text : forall L A mem md Lam peak cnt fail t p q,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (q, wcap t p) Lam -> wlen t p + 1 <= 2 ^ 28 ->
  4112 <= q /\ q + wcap t p <= alloc_ceiling /\ q mod 16 = 0 /\ In (q - 16, wcap t p + 16) (blocks L A) /\
  wlen t p + 1 <= wcap t p /\ (exists j, 0 <= j /\ wcap t p = 4096 * 2 ^ j).
Proof.
  intros L A mem md Lam peak cnt fail t p q HM HL Hin HW.
  destruct (ledger_block_range B API L A mem md Lam peak cnt fail q (wcap t p) HM HL Hin) as (R1 & R2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  destruct (FB _ Hin) as (_ & Hblk & _ & _). cbn [fst snd] in Hblk.
  destruct (rg_blk_in B API HSEG AX FG L A (q - 16) (wcap t p + 16) Hblk) as (u & Hu & Eu).
  pose proof (mr_blocks_aligned _ _ (aa_laws API) L A mem md u (wcap t p + 16) HM Hu) as Hal. rewrite Eu in Hal.
  assert (E62 : 2 ^ 28 <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
  split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact Hblk|].
  split; [apply wcap_ge; lia | apply wcap_pow; lia].
Qed.

Lemma lb_slack : forall L A mem md Lam peak cnt fail t p q,
  aa_MR API L A mem md -> ledger B L A mem Lam peak cnt fail -> In (q, wcap t p) Lam -> wlen t p + 1 <= 2 ^ 28 ->
  ro_agree (ms_segs B) mem -> Mem.bytes_at (ms_segs B) mem q (map (Z_to_bv 8) (wdoc t p ++ [0])) ->
  exists slack, Mem.bytes_at rsegs (normalize rsegs mem) q (map (Z_to_bv 8) (wdoc t p) ++ Z_to_bv 8 0 :: slack) /\
    - (q + Z.of_nat (length (map (Z_to_bv 8) (wdoc t p))) + 1) mod 8 <= Z.of_nat (length slack).
Proof.
  intros L A mem md Lam peak cnt fail t p q HM HL Hin HW RA HB.
  destruct (lb_text L A mem md Lam peak cnt fail t p q HM HL Hin HW) as (Q1 & Q2 & Q3 & _ & Q5 & j & Hj & Ecap).
  assert (HWL : wlen t p = Z.of_nat (length (wdoc t p))) by reflexivity.
  destruct (lb_bytes_some (ms_segs B) mem (q + wlen t p + 1) (Z.to_nat (wcap t p - wlen t p - 1))) as (sl & Hsl & Hb2).
  { lia. }
  { pose proof alloc_ceiling_val. lia. }
  { intros i Hi. replace (q + wlen t p + 1 + i) with (q + (wlen t p + 1 + i)) by lia.
    apply (ledger_block_present B API L A mem md Lam peak cnt fail q (wcap t p)); [exact HM | exact HL | exact Hin | lia]. }
  exists sl. rewrite length_map. split.
  - assert (E : map (Z_to_bv 8) (wdoc t p) ++ Z_to_bv 8 0 :: sl = map (Z_to_bv 8) (wdoc t p ++ [0]) ++ sl).
    { rewrite map_app, <- app_assoc. reflexivity. }
    rewrite E. rewrite <- HSEG.
    apply (proj1 (bytes_at_rel (ms_segs B) mem (normalize (ms_segs B) mem) q _ (mem_rel_normalize (ms_segs B) mem RA))).
    apply Mem.bytes_at_app. split; [exact HB|].
    rewrite length_map, length_app. cbn [length].
    replace (q + Z.of_nat (length (wdoc t p) + 1)) with (q + wlen t p + 1) by lia. exact Hb2.
  - rewrite Hsl. rewrite <- HWL. set (v := 2 ^ j) in *.
    assert (Hv : 1 <= v) by (unfold v; pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj); lia).
    rewrite Z2Nat.id by lia. Z.div_mod_to_equations. lia.
Qed.

End C.
