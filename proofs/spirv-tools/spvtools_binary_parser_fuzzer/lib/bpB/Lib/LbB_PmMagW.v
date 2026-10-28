From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma wr_at_sub : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' ->
    wr_at asegs m a' n'.
  Proof.
    intros m a n a' n' (W0 & W1 & W) H1 H2 H3. split; [lia|]. split; [lia|].
    intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply W. lia.
  Qed.

  Lemma blk_range : forall s LB m pid A n, as_RHEAP H s LB m -> In (pid, A, n) LB ->
    0 < A /\ A mod 16 = 0 /\ 0 <= n /\ AIMG_TOP <= A /\ A + n <= aceil
    /\ (A + n + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= A - 16) /\ aapp A n.
  Proof.
    intros s LB m pid A n RH Hin. exact (ah_blocks H HH _ _ _ _ RH Hin).
  Qed.

  Lemma u8arr_keep : forall m m' A bs,
    (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
    u8arr asegs m A bs -> u8arr asegs m' A bs.
  Proof.
    intros m m' A bs K ((B0 & B1 & B) & (W0 & W1 & W)). split; split; try lia.
    - split; [lia|]. intros i Hi. unfold mrd. destruct (K (A + Z.of_nat i)) as [E _]; [lia|]. rewrite E. apply B. exact Hi.
    - split; [lia|]. intros i Hi. destruct (K (A + i)) as [_ V]; [lia|]. apply V, W. exact Hi.
  Qed.

  Lemma words_okA_keep : forall e ff fp XSc sk LBk m,
    wpre H e -> winv H e ff fp XSc sk LBk m -> words_okA (w_LB e) (w_m e) (w_words e) (w_n e) ->
    words_okA (w_LB e) m (w_words e) (w_n e).
  Proof.
    intros e ff fp XSc sk LBk m HP HI (pw & k & Hin & Rg & W0 & W16 & Whi & Wdef & Wsh).
    exists pw, k. split; [exact Hin|]. split; [exact Rg|]. split; [exact W0|]. split; [exact W16|]. split; [exact Whi|].
    split.
    - intros i Hi. destruct (wkeep H HH e ff fp XSc sk LBk m (w_words e + i) HP HI ltac:(lia)) as [E _].
      + left. exists pw, (w_words e), k. split; [exact Hin | left; lia].
      + unfold wa in E. rewrite E. apply Wdef. exact Hi.
    - destruct Wsh as (S0 & S8 & U). split; [lia|]. split; [exact S8|].
      eapply u8arr_keep; [| exact U]. intros a Ha.
      assert (Hl : Z.of_nat (length (cc_gen k (4 * w_n e))) = nsh k).
      { unfold cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
        assert (nsh (4 * w_n e) <= nsh k) by (unfold nsh; apply Z.div_le_mono; lia). lia. }
      rewrite Hl in Ha. unfold sh in Ha. pose proof (Z.div_pos (w_words e) 8 ltac:(lia) ltac:(lia)).
      assert (w_words e / 8 <= w_words e) by (apply Z.div_le_upper_bound; lia).
      apply (wkeep H HH e ff fp XSc sk LBk m a HP HI).
      { rewrite ASHADOW_BASE_val in Ha. unfold nsh in Ha. assert ((k + 7) / 8 <= k + 7) by (apply Z.div_le_upper_bound; lia). lia. }
      left. exists pw, (w_words e), k. split; [exact Hin | right]. exact Ha.
  Qed.
  Lemma bp_piw : forall e ff fp XSc s LB m w LBs c,
    wpre H e -> winv H e ff fp XSc s LB m -> bp_wl H e ff w -> bp_pp H w LB LBs m c -> w_words e <> 0 ->
    piw_ok H w ((6, ff, fp) :: w_LF e) m.
  Proof.
    intros e ff fp XSc s LB m w LBs c HP HI WL PP HW.
    destruct WL as (Wp & Wc & Ww & Wn & WLB & Ws0 & Wlo & WB & Wshi).
    pose proof HP as (FZ & CTX & N24 & WOK & RH0 & MS1 & MS2 & MS3 & RA & SPB & B64 & _).
    destruct WOK as [[E0 _] | WOK]; [contradiction |].
    pose proof HI as (RF & FF & _).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _).
    destruct PP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    assert (DG : 0 <= st_diag (pc_state c) < 2 ^ 64).
    { destruct PR as [_ _ _ _ _ Pst _ _ _ _ _ _]. destruct Pst as [_ _ W2 _ _ _ _ _ _ _ _ _ _ _ _ _]. destruct W2 as [W2 _].
      change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in W2. exact W2. }
    assert (FS6 : fsz 6 = 4096) by reflexivity.
    constructor.
    - rewrite Wp. right. exists (6, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite FS6. unfold PARSER_SIZE. lia.
    - rewrite Wp. exists (6, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite FS6. unfold PARSER_SIZE. lia.
    - rewrite Wp. unfold PARSER_SIZE. split; [eapply aapp_sub; [exact F10 | lia | lia] |].
      split; [lia | clear - F3; Z.div_mod_to_equations; lia].
    - rewrite Wc. right. exists (6, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite FS6. lia.
    - rewrite Wc. split; [eapply aapp_sub; [exact F10 | lia | lia] |].
      split; [lia | clear - F3; Z.div_mod_to_equations; lia].
    - rewrite Wp, Wc. unfold PARSER_SIZE. lia.
    - rewrite Wc. exists (6, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite FS6. lia.
    - rewrite WLB, Wn. split; [exact MS1 | split; [exact MS2 | exact MS3]].
    - rewrite WLB, Ww, Wn. exact (words_okA_keep e ff fp XSc s LB m HP HI WOK).
    - rewrite Wn. exact N24.
    - rewrite WB. exact B64.
    - rewrite <- HD. exact DG.
  Qed.
  Lemma disj_mono : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n n' D Hn; cbn in *; [exact I|].
    destruct D as [D1 D2]. split; [lia | exact (IH a n n' D2 Hn)].
  Qed.

  Lemma stblk_in : forall LB LB0 LBs st b, state_own LB LB0 LBs st -> In b (state_blocks st) ->
    exists pid, In (pid, fst b, snd b) LB.
  Proof.
    intros LB LB0 LBs st b (P1 & P2) Hb.
    apply (Permutation_in _ (Permutation_sym P2)) in Hb. unfold lbl in Hb.
    apply in_map_iff in Hb as ([[pid A] n] & E & Hin). cbn in E. subst b. exists pid. cbn.
    apply (Permutation_in _ (Permutation_sym P1)). apply in_or_app. right. exact Hin.
  Qed.

  Lemma state_sh_keep : forall LBa m m' st c W,
    @state_rep AC_A ASEGS LY_A MI_A LBa m st c -> state_sh m c -> munch W m m' -> wmono asegs m m' ->
    (forall b, In b (state_blocks c) -> disjoint_from W (sh (fst b)) (nsh (snd b))) -> state_sh m' c.
  Proof.
    intros LBa m m' st c W SR SS MU WM DB.
    destruct SR as [_ _ _ _ _ _ _ _ _ _ Sv1 Sv2 Sv3 _ _ _].
    destruct SS as (U1 & U2 & U3 & V1 & V2 & V3).
    assert (UM : forall (V : Type) NS (t : Z * Z * list (Z * (Z * V))),
      (forall b, In b (umap_blocks NS (t3a t) (t3b t) (t3c t)) -> disjoint_from W (sh (fst b)) (nsh (snd b))) ->
      umap_sh m NS t -> umap_sh m' NS t).
    { intros V NS t D (UA & UE). split.
      - intros Hb. eapply addressable_transport; [exact (UA Hb) | exact MU | exact WM |].
        apply (D (t3a t, 8 * t3b t)). unfold umap_blocks. apply in_or_app. left.
        destruct (Z.eqb_spec (t3b t) 0); [contradiction | left; reflexivity].
      - intros p k v Hin. eapply addressable_transport; [exact (UE p k v Hin) | exact MU | exact WM |].
        apply (D (p, NS)). unfold umap_blocks. apply in_or_app. right. apply in_map_iff.
        exists (p, (k, v)). split; [reflexivity | exact Hin]. }
    assert (VK : forall v : Z * Z * Z, t3a v <= t3b v <= t3c v ->
      (forall b, In b (vec_blocks v) -> disjoint_from W (sh (fst b)) (nsh (snd b))) -> vec_sh m v -> vec_sh m' v).
    { intros v Ho D Hv Ha. eapply SHAD_transport; [exact (Hv Ha) | exact MU | exact WM |].
      rewrite cc_gen_length by lia. apply (D (t3a v, t3c v - t3a v)). unfold vec_blocks.
      destruct (Z.eqb_spec (t3a v) 0); [contradiction | left; reflexivity]. }
    unfold state_blocks in DB.
    assert (DBi : forall l, (forall b, In b l -> In b (umap_blocks 24 (t3a (st_m1 c)) (t3b (st_m1 c)) (t3c (st_m1 c))
                 ++ umap_blocks 32 (t3a (st_m2 c)) (t3b (st_m2 c)) (t3c (st_m2 c))
                 ++ umap_blocks 24 (t3a (st_m3 c)) (t3b (st_m3 c)) (t3c (st_m3 c))
                 ++ vec_blocks (st_v1 c) ++ vec_blocks (st_v2 c) ++ vec_blocks (st_v3 c))) ->
                 forall b, In b l -> disjoint_from W (sh (fst b)) (nsh (snd b))).
    { intros l Hl b Hb. apply DB, Hl, Hb. }
    split; [| split; [| split; [| split; [| split]]]].
    - apply UM; [| exact U1]. apply DBi. intros b Hb. rewrite !in_app_iff. tauto.
    - apply UM; [| exact U2]. apply DBi. intros b Hb. rewrite !in_app_iff. tauto.
    - apply UM; [| exact U3]. apply DBi. intros b Hb. rewrite !in_app_iff. tauto.
    - apply VK; [exact (vord_of_vraw _ _ _ _ _ _ Sv1) | | exact V1]. apply DBi. intros b Hb. rewrite !in_app_iff. tauto.
    - apply VK; [exact (vord_of_vraw _ _ _ _ _ _ Sv2) | | exact V2]. apply DBi. intros b Hb. rewrite !in_app_iff. tauto.
    - apply VK; [exact (vord_of_vraw _ _ _ _ _ _ Sv3) | | exact V3]. apply DBi. intros b Hb. rewrite !in_app_iff. tauto.
  Qed.

  Lemma parser_sh_keep : forall LB m m' p c W,
    parser_repA LB m p c -> parser_sh m p c -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W (sh p) (nsh PARSER_SIZE) -> disjoint_from W (sh (pc_cons c)) (nsh 48) ->
    (forall b, In b (state_blocks (pc_state c)) -> disjoint_from W (sh (fst b)) (nsh (snd b))) ->
    parser_sh m' p c.
  Proof.
    intros LB m m' p c W PR (A1 & A2 & SS) MU WM D1 D2 D3.
    split; [eapply addressable_transport; [exact A1 | exact MU | exact WM | exact D1] |].
    split; [eapply addressable_transport; [exact A2 | exact MU | exact WM | exact D2] |].
    destruct PR as [_ _ _ _ _ Pst _ _ _ _ _ _].
    exact (state_sh_keep _ m m' _ _ W Pst SS MU WM D3).
  Qed.

  Lemma bp_pp_keep : forall w LB LBs m m' c W,
    bp_pp H w LB LBs m c -> munch W m m' -> wmono asegs m m' -> 0 <= pc_cons c -> pc_cons c + 48 < 2 ^ 64 ->
    (forall a, parser_foot (pw_p H w) c a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall a, pc_cons c + 32 <= a < pc_cons c + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    disjoint_from W (sh (pw_p H w)) (nsh PARSER_SIZE) -> disjoint_from W (sh (pc_cons c)) (nsh 48) ->
    (forall b, In b (state_blocks (pc_state c)) -> disjoint_from W (sh (fst b)) (nsh (snd b))) ->
    bp_pp H w LB LBs m' c.
  Proof.
    intros w LB LBs m m' c W (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR) MU WM Hc0 Hc1 HM HCm D1 D2 D3.
    split; [exact (parser_repA_keep LB m m' (pw_p H w) c PR Hc0 Hc1 HM HCm) |].
    split; [exact (parser_sh_keep LB m m' (pw_p H w) c W PR PSH MU WM D1 D2 D3) |].
    split; [exact HC |]. split; [exact HU |]. split; [exact HD |]. split; [exact SOWN |].
    split; [unfold lb_own in *; eapply Forall_impl; [| exact LBOWN]; intros b Hb; exact (wr_at_wmono _ _ _ _ Hb WM) |].
    exact (wr_at_wmono _ _ _ _ CWR WM).
  Qed.

  Lemma bp_pp_endian : forall w LB LBs m m' c W e,
    bp_pp H w LB LBs m c -> munch W m m' -> wmono asegs m m' -> AIMG_TOP <= pw_p H w ->
    0 <= pc_cons c -> pc_cons c + 48 < 2 ^ 64 ->
    (st_flags (pc_state c) = 0 \/ st_flags (pc_state c) = 1) -> (e = 0 \/ e = 1) ->
    (forall a, pw_p H w <= a < pw_p H w + PARSER_SIZE -> ~ (pw_p H w + 88 <= a < pw_p H w + 93) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall a b, In b (state_blocks (pc_state c)) -> fst b <= a < fst b + snd b -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall a, pc_cons c + 32 <= a < pc_cons c + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    fld ASEGS m' (pw_p H w + 88) 4 e -> fld ASEGS m' (pw_p H w + 92) 1 e ->
    disjoint_from W (sh (pw_p H w)) (nsh PARSER_SIZE) -> disjoint_from W (sh (pc_cons c)) (nsh 48) ->
    (forall b, In b (state_blocks (pc_state c)) -> disjoint_from W (sh (fst b)) (nsh (snd b))) ->
    bp_pp H w LB LBs m' (pc_e c e).
  Proof.
    intros w LB LBs m m' c W e (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR) MU WM HP Hc0 Hc1 HF He HMo HMb HCm F5 F6 D1 D2 D3.
    split; [exact (parser_repA_endian LB m m' (pw_p H w) c e PR HP Hc0 Hc1 HF He HMo HMb HCm F5 F6) |].
    split; [exact (parser_sh_keep LB m m' (pw_p H w) c W PR PSH MU WM D1 D2 D3) |].
    split; [exact HC |]. split; [exact HU |]. split; [exact HD |]. split; [exact SOWN |].
    split; [unfold lb_own in *; eapply Forall_impl; [| exact LBOWN]; intros b Hb; exact (wr_at_wmono _ _ _ _ Hb WM) |].
    exact (wr_at_wmono _ _ _ _ CWR WM).
  Qed.
  Lemma outside_of_all : forall W a, (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a K; cbn; [exact I|].
    split; [exact (K (lo, hi) (or_introl eq_refl)) | apply IH; intros iv Hi; exact (K iv (or_intror Hi))].
  Qed.

  Lemma disj_of_all : forall W a n, (forall iv, In iv W -> a + n <= fst iv \/ snd iv <= a) -> disjoint_from W a n.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n K; cbn; [exact I|].
    split; [exact (K (lo, hi) (or_introl eq_refl)) | apply IH; intros iv Hi; exact (K iv (or_intror Hi))].
  Qed.

  Lemma munch_at : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 ->
    (forall iv, In iv W -> ~ (fst iv <= a < snd iv)) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
  Proof.
    intros W m m' a MU Ha K. apply MU. rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
    apply outside_of_all. exact K.
  Qed.

  Lemma sh_add8 : forall a k, 0 <= a -> a mod 8 = 0 -> 0 <= k -> sh (a + 8 * k) = sh a + k.
  Proof.
    intros a k H0 H8 Hk. unfold sh. rewrite (Z.div_mod a 8) at 1 by lia. rewrite H8, Z.add_0_r.
    replace (8 * (a / 8) + 8 * k) with ((a / 8 + k) * 8) by ring. rewrite Z.div_mul by lia. lia.
  Qed.

  Lemma hdr_geo : forall e ff fp XSc s LB m, wpre H e -> winv H e ff fp XSc s LB m ->
    ff mod 64 = 0 /\ 0x6e8000 + 0x9000 <= ff /\ ff + 4096 <= aceil
    /\ as_FSB H + 0x9000 <= ff /\ ff + 4096 <= as_FSB H + AFS_SIZE /\ aapp (as_FSB H) AFS_SIZE
    /\ 0x7fff8000 <= sh ff /\ sh ff + 512 <= 0x10007fff8000 /\ (sh ff + 512 <= ff \/ ff + 4096 <= sh ff)
    /\ aceil <= w_lo e /\ w_lo e + 32768 <= wS1 e /\ wS1 e + 192 <= wSP e /\ wSP e <= 2 ^ 47 /\ wS1 e mod 32 = 0
    /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
  Proof.
    intros e ff fp XSc s LB m HP HI.
    pose proof HI as (RF & FF & _).
    pose proof (wframe_facts H _ _ _ FF) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    pose proof (wframe_bounds H e ff fp XSc s LB m HP HI) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & _).
    pose proof (wS1_facts H e HP) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & _).
    repeat split; first [assumption | lia].
  Qed.

  Lemma blk_disj : forall e ff fp XSc s LB m iv pid A n, wpre H e -> winv H e ff fp XSc s LB m -> bp_flw H e ff iv ->
    In (pid, A, n) LB -> (snd iv <= A \/ A + n <= fst iv) /\ (snd iv <= sh A \/ sh A + nsh n <= fst iv).
  Proof.
    intros e ff fp XSc s LB m iv pid A n HP HI FL Hin.
    pose proof HI as (_ & _ & RH & _).
    destruct (blk_range s LB m pid A n RH Hin) as (A0 & A16 & N0 & AT & AC & AF & AA).
    pose proof (hdr_geo e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    assert (SHA : 0x7fff8000 <= sh A /\ sh A + nsh n <= 0x10007fff8000).
    { unfold sh, nsh. rewrite ASHADOW_BASE_val. clear - A0 N0 AC G16.
      split; [pose proof (Z.div_pos A 8); lia |].
      assert (A / 8 + (n + 7) / 8 <= (A + n + 7) / 8 + 1).
      { pose proof (Z.div_mod A 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (A + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound A 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (A + n + 7) 8 ltac:(lia)). lia. }
      assert ((A + n + 7) / 8 <= 17592186044415) by (apply Z.div_le_upper_bound; lia). lia. }
    assert (FSH : sh A + nsh n <= sh ff \/ sh ff + 512 <= sh A).
    { destruct AF as [AF|AF].
      - left. assert (E : A + 8 * nsh n <= ff) by (unfold nsh; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
        rewrite <- sh_add8 by (first [lia | (clear - A16; Z.div_mod_to_equations; lia) | (unfold nsh; apply Z.div_pos; lia)]). apply sh_mono. exact E.
      - right. replace (sh ff + 512) with (sh (ff + 8 * 512)) by (rewrite sh_add8 by (first [lia | (clear - G1; Z.div_mod_to_equations; lia)]); lia).
        apply sh_mono. lia. }
    destruct AA as [AA|AA]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AA;
    destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in G6;
    destruct FL as ([F|[F|F]] & C1 & C2 & C3 & C4); unfold WO_FLAGP in F; split; lia.
  Qed.

  Lemma blk_disj_reg : forall e ff fp XSc s LB m iv pid A n, wpre H e -> winv H e ff fp XSc s LB m ->
    ((ff <= fst iv /\ snd iv <= ff + WO_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512) \/ (w_lo e <= fst iv /\ snd iv <= wS1 e)) ->
    In (pid, A, n) LB -> (snd iv <= A \/ A + n <= fst iv) /\ (snd iv <= sh A \/ sh A + nsh n <= fst iv).
  Proof.
    intros e ff fp XSc s LB m iv pid A n HP HI FL Hin.
    pose proof HI as (_ & _ & RH & _).
    destruct (blk_range s LB m pid A n RH Hin) as (A0 & A16 & N0 & AT & AC & AF & AA).
    pose proof (hdr_geo e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    assert (SHA : 0x7fff8000 <= sh A /\ sh A + nsh n <= 0x10007fff8000).
    { unfold sh, nsh. rewrite ASHADOW_BASE_val. clear - A0 N0 AC G16.
      split; [pose proof (Z.div_pos A 8); lia |].
      assert (A / 8 + (n + 7) / 8 <= (A + n + 7) / 8 + 1).
      { pose proof (Z.div_mod A 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)).
        pose proof (Z.div_mod (A + n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound A 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (A + n + 7) 8 ltac:(lia)). lia. }
      assert ((A + n + 7) / 8 <= 17592186044415) by (apply Z.div_le_upper_bound; lia). lia. }
    assert (FSH : sh A + nsh n <= sh ff \/ sh ff + 512 <= sh A).
    { destruct AF as [AF|AF].
      - left. assert (E : A + 8 * nsh n <= ff) by (unfold nsh; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
        rewrite <- sh_add8 by (first [lia | (clear - A16; Z.div_mod_to_equations; lia) | (unfold nsh; apply Z.div_pos; lia)]). apply sh_mono. exact E.
      - right. replace (sh ff + 512) with (sh (ff + 8 * 512)) by (rewrite sh_add8 by (first [lia | (clear - G1; Z.div_mod_to_equations; lia)]); lia).
        apply sh_mono. lia. }
    destruct AA as [AA|AA]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AA;
    destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in G6;
    destruct FL as [F|[F|F]]; unfold WO_FLAGP in F; split; lia.
  Qed.
  Lemma stk_keepW : forall W m m' lo hi, stk asegs m lo hi -> munch W m m' -> wmono asegs m m' -> AIMG_TOP <= lo ->
    stk asegs m' lo hi.
  Proof.
    intros W m m' lo hi (S0 & S1 & S) MU WM HL. split; [exact S0|]. split; [exact S1|].
    intros a Ha. destruct (S a Ha) as [V _]. pose proof (WM _ V) as V'. split; [exact V'|].
    rewrite (BakeStackRep.wview_high m' (wa a)) in V' by (unfold wa; rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia; lia).
    destruct (m' (wa a)) as [b|] eqn:E; [|contradiction]. exists b. unfold mrd. rewrite E. reflexivity.
  Qed.
  Lemma flw_parser_repA : forall e ff fp XSc s LB LB0 LBs m m' c W,
    wpre H e -> winv H e ff fp XSc s LB m -> parser_repA LB m (ff + 3456) c -> pc_cons c = ff + 3376 ->
    state_own LB LB0 LBs (pc_state c) -> munch W m m' -> Forall (bp_flw H e ff) W -> parser_repA LB m' (ff + 3456) c.
  Proof.
    intros e ff fp XSc s LB LB0 LBs m m' c W HP HI PR HC SO MU FW.
    pose proof (hdr_geo e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & _).
    pose proof aceil_facts as ((AC1 & AC2) & _).
    rewrite Forall_forall in FW.
    apply (parser_repA_keep LB m m' (ff + 3456) c PR); [rewrite HC; lia | rewrite HC; lia | |].
    - intros a Hf. destruct Hf as [Hp | [Hs | (b & Hb & Hab)]].
      + unfold PARSER_SIZE in Hp. apply (munch_at W m m' a MU); [lia |].
        intros iv Hiv. destruct (FW iv Hiv) as (_ & _ & C2 & _). lia.
      + unfold ST_OFF in Hs. apply (munch_at W m m' a MU); [lia |].
        intros iv Hiv. destruct (FW iv Hiv) as (_ & _ & C2 & _). lia.
      + destruct (stblk_in LB LB0 LBs _ b SO Hb) as (pid & Hin). pose proof HI as (_ & _ & RH & _).
        destruct (blk_range s LB m pid (fst b) (snd b) RH Hin) as (A0 & _ & N0 & _ & AC & _).
        apply (munch_at W m m' a MU); [lia |].
        intros iv Hiv. destruct (blk_disj e ff fp XSc s LB m iv pid (fst b) (snd b) HP HI (FW iv Hiv) Hin) as [D _]. lia.
    - intros a Ha. rewrite HC in Ha. apply (munch_at W m m' a MU); [lia |].
      intros iv Hiv. destruct (FW iv Hiv) as (_ & C1 & _). lia.
  Qed.

  Lemma flw_parser_sh : forall e ff fp XSc s LB LB0 LBs m m' c W,
    wpre H e -> winv H e ff fp XSc s LB m -> parser_repA LB m (ff + 3456) c -> parser_sh m (ff + 3456) c ->
    pc_cons c = ff + 3376 -> state_own LB LB0 LBs (pc_state c) -> munch W m m' -> wmono asegs m m' ->
    Forall (bp_flw H e ff) W -> parser_sh m' (ff + 3456) c.
  Proof.
    intros e ff fp XSc s LB LB0 LBs m m' c W HP HI PR PSH HC SO MU WM FW.
    pose proof (hdr_geo e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & _).
    rewrite Forall_forall in FW.
    assert (F8 : ff mod 8 = 0) by (clear - G1; Z.div_mod_to_equations; lia).
    assert (SP : sh (ff + 3456) = sh ff + 432) by (replace (ff + 3456) with (ff + 8 * 432) by lia; apply sh_add8; lia).
    assert (SC : sh (ff + 3376) = sh ff + 422) by (replace (ff + 3376) with (ff + 8 * 422) by lia; apply sh_add8; lia).
    apply (parser_sh_keep LB m m' (ff + 3456) c W PR PSH MU WM).
    - apply disj_of_all. intros iv Hiv. destruct (FW iv Hiv) as (_ & _ & _ & _ & C4).
      rewrite SP. unfold PARSER_SIZE. change (nsh 288) with 36. lia.
    - rewrite HC. apply disj_of_all. intros iv Hiv. destruct (FW iv Hiv) as (_ & _ & _ & C3 & _).
      rewrite SC. change (nsh 48) with 6. lia.
    - intros b Hb. destruct (stblk_in LB LB0 LBs _ b SO Hb) as (pid & Hin).
      apply disj_of_all. intros iv Hiv.
      destruct (blk_disj e ff fp XSc s LB m iv pid (fst b) (snd b) HP HI (FW iv Hiv) Hin) as [_ D]. lia.
  Qed.

  Lemma bp_pp_keepW : forall e ff fp XSc (w : piw H) s LB LBs m m' c W,
    wpre H e -> winv H e ff fp XSc s LB m -> bp_wl H e ff w -> bp_pp H w LB LBs m c ->
    munch W m m' -> wmono asegs m m' -> Forall (bp_flw H e ff) W -> bp_pp H w LB LBs m' c.
  Proof.
    intros e ff fp XSc w s LB LBs m m' c W HP HI WL PP MU WM FW.
    destruct WL as (Wp & Wc & _).
    destruct PP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    rewrite Wp in PR, PSH. rewrite Wc in HC.
    split; [rewrite Wp; exact (flw_parser_repA e ff fp XSc s LB (pw_LB0 H w) LBs m m' c W HP HI PR HC SOWN MU FW) |].
    split; [rewrite Wp; exact (flw_parser_sh e ff fp XSc s LB (pw_LB0 H w) LBs m m' c W HP HI PR PSH HC SOWN MU WM FW) |].
    split; [rewrite Wc; exact HC |]. split; [exact HU |]. split; [exact HD |]. split; [exact SOWN |].
    split; [unfold lb_own in *; eapply Forall_impl; [| exact LBOWN]; intros b Hb; exact (wr_at_wmono _ _ _ _ Hb WM) |].
    exact (wr_at_wmono _ _ _ _ CWR WM).
  Qed.
End W.
