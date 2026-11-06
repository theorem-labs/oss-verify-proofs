From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Cells
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel libreac_fuzz_fopen_c
  pcap_source_next_lib pcap_source_next_c pcap_source_open_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require memcpy rd32f memmove.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PGlue PSteps PImg UCut URec
  USegE UGlueT UGlueR7 UBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USROcf PInvCF UContractCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

Lemma uf_un_le : forall g, un g <= g_n g.
Proof. intros g. unfold un, uF, zlen, g_n. destruct (g_in g) as [|d l]; cbn [tl length]; lia. Qed.

Lemma uf_ud : forall g, 0 <= ud g < 256.
Proof. intros g. unfold ud. destruct (g_in g) as [|d l]; [lia|]. apply ss_bz_range. Qed.

Lemma uf_swz : forall g, uswz g = 0 \/ uswz g = 1.
Proof.
  intros g. unfold uswz, PS.pcap_sw. destruct (PS.pcap_magic (uF g) =? 0xD4C3B2A1); [right | left]; reflexivity.
Qed.

Lemma uf_ps_sz : forall f s o v i pad, Z.of_nat (cells_size (PS.ps_cells f s o v i pad)) = 24.
Proof. reflexivity. Qed.

Lemma uf_rw_rel : forall m m0 a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

Lemma uf_retype : forall m a cs cs', rw_cells rsegs m a cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells rsegs m a cs'.
Proof.
  intros m a cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf' | rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.

Lemma uf_cb8 : forall m a bs, rw_cells rsegs m a [CB 8 bs] -> exists v, rw_cells rsegs m a [C8 v].
Proof.
  intros m a bs H. pose proof H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  destruct (U.Prog.memmove.le8_surj bs Hl) as (v & ->). exists v.
  apply (uf_retype m a _ _ H); [cbn; repeat split | reflexivity].
Qed.

Lemma uf_stk8 : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi -> exists v, rw_cells rsegs m a [C8 v].
Proof.
  intros m lo hi a ST H1 H2.
  destruct (ss_rw_of_stk m lo hi a 8 ST H1 ltac:(lia)) as (bs & H).
  exact (uf_cb8 m a bs H).
Qed.

Lemma uf_dj_lo : forall W a n L, (forall lo hi, In (lo, hi) W -> L <= lo) -> a + n <= L -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n L H Ha; cbn [disjoint_from]; [exact I|].
  split; [left; specialize (H lo hi (or_introl eq_refl)); lia|].
  apply (IH a n L); [intros lo' hi' Hin; exact (H lo' hi' (or_intror Hin)) | exact Ha].
Qed.

Lemma uf_out_good : forall g, g_n g < 2 ^ 26 -> ugood g = true -> PW.OUT (g_in g) = uwalk g 24 ++ uC0 g.
Proof.
  intros g Hn Hg. unfold ugood, uwalk, uC0, uout1, usw, uswz, ucap, ud, uF, g_n in *.
  destruct (g_in g) as [|d F]; cbn [tl] in *.
  - vm_compute in Hg. discriminate Hg.
  - rewrite (PW.OUT_cons d F Hn), Hg. reflexivity.
Qed.

Lemma uf_out_ref : forall g, ugood g = false -> PW.OUT (g_in g) = [].
Proof.
  intros g Hg. unfold ugood, uF in Hg. destruct (g_in g) as [|d F]; [reflexivity|]. cbn [tl] in Hg.
  destruct (Z_lt_le_dec (Z.of_nat (length (d :: F))) (2 ^ 26)) as [Hl|Hl].
  - rewrite (PW.OUT_cons d F Hl), Hg. reflexivity.
  - exact (PW.OUT_big _ Hl).
Qed.

Lemma uf_psc_sw : forall m a f sw o v i pad, rw_cells rsegs m a (PS.ps_cells f sw o v i pad) ->
  bytes_at rsegs m (a + 8) (le4 sw).
Proof.
  intros m a f sw o v i pad [[_ Hb] _]. unfold PS.ps_cells in Hb. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb as [Hb _]. exact Hb.
Qed.

Lemma uf_blk_cb : forall m a k, 0 <= a -> a + k <= 2 ^ 64 -> 0 <= k ->
  (forall i, 0 <= i < k -> writable_at rsegs m (a + i) /\ present m (a + i)) ->
  rw_cells rsegs m a [CB (Z.to_nat k) (ss_rd_list m a (Z.to_nat k))].
Proof.
  intros m a k H0 H1 Hk H. split; [split|].
  - cbn [cells_wf cell_wf]. rewrite ss_rd_list_len. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [rewrite ss_rd_list_len; lia|].
    intros j Hj. rewrite ss_rd_list_len in Hj. rewrite ss_rd_list_nth by exact Hj.
    destruct (H (Z.of_nat j) ltac:(lia)) as (_ & bb & Hb).
    unfold mrd, wa. rewrite Hb. reflexivity.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (H i ltac:(lia))).
Qed.

Section R0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma uf_run : forall g km hb L A regs mem md pc W (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g hb y) ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
      (Q R pc' m' /\ munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4))
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' ->
     munch W mem mem' -> wmono rsegs mem mem' -> FR B APIf ra empty g km hb L A regs' mem' md ->
     SRO (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) o P) ->
  SRO (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb L A regs mem md pc W Q o P HF HP HW HE HK.
  pose proof (ss_fr_bnd B APIf ra empty FF g km hb L A regs mem md HF) as (_ & _ & _ & _ & HRO).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km hb L A regs mem md HF)) as (Hh & Hl).
  apply (ss_kA_run_o B APIf ra empty FF regs pc mem md
    (fun R pc' m' => Q R pc' m' /\ munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) o P Hh Hl).
  - rewrite (sg_segs B APIf ra empty FF). exact HRO.
  - exact HE.
  - intros R pc' m' regs' mem' (HQ & MU & WM & E2 & E3 & E4) XR HR HS.
    pose proof (mem_rel_normalize rsegs mem HRO) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) mem' m' HR0 HR HS MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m' HR0 HR HS WM) as WM'.
    apply (HK R pc' m' regs' mem' HQ XR HR MU' WM').
    apply (ss_FR_munch B APIf ra empty FF g km hb L A regs mem md regs' mem' W HF HP).
    + rewrite (ss_getr_eqv _ _ 2 XR). exact E2.
    + rewrite (ss_getr_eqv _ _ 3 XR). exact E3.
    + rewrite (ss_getr_eqv _ _ 4 XR). exact E4.
    + exact MU'.
    + exact WM'.
    + exact HW.
Qed.

(* The cut-free twin of uf_run. *)
Lemma uf_run_cf : forall g km hb L A regs mem md pc W (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop)
    o P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g hb y) ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
      (Q R pc' m' /\ munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4))
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' ->
     munch W mem mem' -> wmono rsegs mem mem' -> FR B APIf ra empty g km hb L A regs' mem' md ->
     SROcf (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) o P) ->
  SROcf (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) o P.
Proof.
  intros g km hb L A regs mem md pc W Q o P HF HP HW HE HK.
  pose proof (ss_fr_bnd B APIf ra empty FF g km hb L A regs mem md HF) as (_ & _ & _ & _ & HRO).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km hb L A regs mem md HF)) as (Hh & Hl).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs pc mem md
    (fun R pc' m' => Q R pc' m' /\ munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) o P Hh Hl).
  - rewrite (sg_segs B APIf ra empty FF). exact HRO.
  - exact HE.
  - intros R pc' m' regs' mem' (HQ & MU & WM & E2 & E3 & E4) XR HR HS.
    pose proof (mem_rel_normalize rsegs mem HRO) as HR0.
    pose proof (munch_rel rsegs W mem (normalize rsegs mem) mem' m' HR0 HR HS MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m' HR0 HR HS WM) as WM'.
    apply (HK R pc' m' regs' mem' HQ XR HR MU' WM').
    apply (ss_FR_munch B APIf ra empty FF g km hb L A regs mem md regs' mem' W HF HP).
    + rewrite (ss_getr_eqv _ _ 2 XR). exact E2.
    + rewrite (ss_getr_eqv _ _ 3 XR). exact E3.
    + rewrite (ss_getr_eqv _ _ 4 XR). exact E4.
    + exact MU'.
    + exact WM'.
    + exact HW.
Qed.

End R0.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HOPEN : forall fx0 : YK11.FPState, @pcap_source_open_contract fx0 rc B (APIf rc).
Hypothesis HNEXT : forall fx0 : YK11.FPState, @pcap_source_next_contract fx0.

Lemma ug_C : Hcut_o B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24) ->
  Hcut_o B APIf ra (Inv_K12e14 B APIf ra empty) (fun g => uwalk g 24 ++ uC0 g).
Proof.
  intros HX g c (b & h & buf & Hgood & HC). cbv beta.
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) 3 [(b, un g); (h, 1304); (buf, ubn g)] _ c _ (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H9 & H26 & (Hstd & Hgd & (fl & mdv & Herr) & Q0 & QL) & QG & HBF
    & (pad & HPS) & HMS & HOO & (bj & HU & HL)).
  pose proof HF as (HGV & _).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  pose proof HGV as (Hgn & _ & _ & _ & HSc & _).
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md b (un g) HF HP
    ltac:(cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md h 1304 HF HP
    ltac:(cbn [In]; right; left; reflexivity)) as (_ & Hh1 & Hh2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md buf (ubn g) HF HP
    ltac:(cbn [In]; right; right; left; reflexivity)) as (_ & Hu1 & Hu2 & _).
  pose proof (uf_un_le g) as Hun. pose proof (uf_ud g) as Hud.
  assert (Hcap : 0 <= ucap g <= 2040) by (unfold ucap; lia).
  assert (Hbn : ubn g = Z.max (ucap g) 1) by reflexivity.
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  assert (EO : uwalk g 24 ++ uC0 g = UN.psn_out h (uswz g =? 1) (uF g) (ucap g) 24 ++ uafter g 24).
  { rewrite (uwalk_unfold g 24 ltac:(lia)), psn_out_UP. unfold PN.psn_out, uout1, usw.
    destruct (Z.eqb_spec h 0); [lia | reflexivity]. }
  rewrite EO.
  set (W := [(fsp g + 24, fsp g + 32); (fsp g + 40, fsp g + 48)]).
  assert (HSTK : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)).
  { replace (fsp g + 176) with (g_S g) by (unfold fsp, SLOT_FRAME; lia).
    exact (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF). }
  destruct (uf_stk8 _ _ _ (fsp g + 24) HSTK ltac:(unfold fsp, SLOT_FRAME in *; lia) ltac:(lia)) as (v24 & C24).
  destruct (uf_stk8 _ _ _ (fsp g + 40) HSTK ltac:(unfold fsp, SLOT_FRAME in *; lia) ltac:(lia)) as (v40 & C40).
  apply (uf_run B APIf ra empty FF g 3 _ L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) W
    (fun R pc' m' => pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z) /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 10 = wz (fsp g + 48) /\ getr R 11 = wz buf /\ getr R 12 = wz (ucap g) /\
       getr R 13 = wz (fsp g + 40) /\ getr R 18 = wz buf /\ getr R 26 = getr regs 26 /\
       rw_cells rsegs m' (fsp g + 24) [C8 (wz buf)] /\ rw_cells rsegs m' (fsp g + 40) [C8 (wz (-1))])
    _ _ HF HP).
  - intros lo hi y Hin Hy. left. unfold W in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fsp, SLOT_FRAME in *; lia.
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_C_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (g_S g - SLOT_K) (fsp g) buf (ucap g) v24 v40 USP H10 ltac:(lia) H9
      (mem_inv_normalize rsegs mem) HSTK ltac:(unfold fsp, SLOT_FRAME in *; lia) C24 C40)|].
    intros ms (m' & -> & MU & WM & _ & _ & C24' & C40').
    do 3 eexists. split; [reflexivity|].
    split; [do 10 (split; [reflexivity|]); split; [exact C24' | exact C40']|].
    split; [exact MU|]. split; [exact WM|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & G1 & G8 & G9 & G10 & G11 & G12 & G13 & G18 & G26 & C24' & C40') XR HR MU WM HF'.
    assert (HWL : forall lo hi, In (lo, hi) W -> fsp g + 24 <= lo).
    { intros lo hi Hin. unfold W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
    assert (HL0 : forall a n, a + n <= fsp g + 24 -> disjoint_from W a n)
      by (intros a n Ha; exact (uf_dj_lo W a n _ HWL Ha)).
    assert (HIMG : forall a, a <= (symaddr ImgPages.Ubsan.top) -> a <= fsp g + 24)
      by (intros a Ha; unfold fsp, SLOT_FRAME, SS_TOP in *; lia).
    destruct Hstd as (S1 & S2 & S3).
    assert (Hstd' : stdio_ok mem').
    { split; [|split]; (eapply bytes_at_transport; [eassumption | exact MU | apply HL0]);
        cbn [length]; rewrite ?length_le4; apply HIMG; unfold A_LIBC, A_OFL_LOCK; lia. }
    assert (Herr' : errf mem' fl mdv).
    { destruct Herr as (E1 & E2 & E3). split; [|split; assumption].
      apply (rw_cells_transport rsegs W mem mem' _ _ E1 MU WM). apply HL0.
      change (Z.of_nat (cells_size (stderr_cells fl mdv))) with 232. apply HIMG. unfold A_STDERR. lia. }
    pose proof (bytes_at_transport rsegs W mem mem' _ _ Q0 MU) as Q0'.
    specialize (Q0' ltac:(rewrite length_le8; apply HL0; unfold spk; lia)).
    pose proof (bytes_at_transport rsegs W mem mem' _ _ QL MU) as QL'.
    specialize (QL' ltac:(rewrite length_le8; apply HL0; apply HIMG; unfold G_FILE_LEN; lia)).
    pose proof (bytes_at_transport rsegs W mem mem' _ _ QG MU) as QG'.
    specialize (QG' ltac:(rewrite length_le8; apply HL0; apply HIMG; unfold G_FILE_LEN; lia)).
    pose proof (rw_cells_transport rsegs W mem mem' _ _ HPS MU WM) as HPS'.
    specialize (HPS' ltac:(rewrite uf_ps_sz; unfold W, spk; cbn [disjoint_from]; repeat split; lia)).
    pose proof (rw_cells_transport rsegs W mem mem' _ _ HOO MU WM) as HOO'.
    specialize (HOO' ltac:(apply HL0; change (Z.of_nat (cells_size [C8 (wz h)])) with 8; apply HIMG;
      unfold A_OFL_HEAD; lia)).
    pose proof (mstl_transport W mem mem' h b (uF g) 24 (wz 0) (wz 0) HMS MU WM) as HMS'.
    specialize (HMS' ltac:(apply HL0; unfold fsp, SLOT_FRAME in *; lia)
      ltac:(apply HL0; unfold un, zlen, fsp, SLOT_FRAME in *; lia)).
    pose proof (Arr.u8arr_transport rsegs W mem mem' buf bj HU MU WM) as HU'.
    specialize (HU' ltac:(apply HL0; rewrite HL; unfold fsp, SLOT_FRAME in *; lia)).
    assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    assert (K8 : getr regs' 8 = wz b) by (rewrite (ss_getr_eqv _ _ 8 XR); rewrite G8; exact H8).
    assert (K9 : getr regs' 9 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 9 XR); rewrite G9; exact H9).
    assert (K10 : getr regs' 10 = wz (fsp g + 48)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
    assert (K11 : getr regs' 11 = wz buf) by (rewrite (ss_getr_eqv _ _ 11 XR); exact G11).
    assert (K12 : getr regs' 12 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 12 XR); exact G12).
    assert (K13 : getr regs' 13 = wz (fsp g + 40)) by (rewrite (ss_getr_eqv _ _ 13 XR); exact G13).
    assert (K18 : getr regs' 18 = wz buf) by (rewrite (ss_getr_eqv _ _ 18 XR); exact G18).
    assert (K26 : getr regs' 26 = wz G_FILE_LEN) by (rewrite (ss_getr_eqv _ _ 26 XR); rewrite G26; exact H26).
    pose proof (uf_rw_rel mem' m' _ _ HR C24') as C24n.
    pose proof (uf_rw_rel mem' m' _ _ HR C40') as C40n.
    change (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) with (Z_to_bv 64 PCAP_SOURCE_NEXT).
    apply (ps_next_step B APIf ra empty FF (HNEXT _) g 3 _ [(b, un g); (h, 1304)] L A regs' mem' md (fsp g + 48) buf
      (ucap g) (fsp g + 40) h (uswz g) b 24 fl mdv (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz (-1)) pad bj (uF g)
      (uafter g 24) (Post_o B APIf ra g) HF' HP Hfrm).
    + rewrite K1. apply ug_ret_ok; lia.
    + exact K10.
    + exact K11.
    + exact K12.
    + exact K13.
    + lia.
    + unfold fsp, SLOT_FRAME; lia.
    + Z.div_mod_to_equations. lia.
    + exact HPS'.
    + exact (Permutation_sym (Permutation_cons_append [(b, un g); (h, 1304)] (buf, ubn g))).
    + exact HU'.
    + exact HL.
    + lia.
    + intros _. split; [lia|]. split; [unfold fsp, SLOT_FRAME; lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [lia | exact C40n].
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|]. split; [exact HMS'|].
      split; [exact (uf_swz g)|]. unfold un, zlen in *; lia.
    + exact Herr'.
    + intros regs2 mem2 Ft fc' mdv' Hfc HFt HF2 RP2 KF KB KI KS Herr2 Hgd2 _ HPO.
      destruct (HPO ltac:(lia)) as (R10 & HMS2 & HPS2 & (bj2 & HU2 & HL2 & HFT2) & HTS2).
      rewrite (sg_segs B APIf ra empty FF) in KF, KB, KI.
      rewrite K1. apply HX. exists b, h, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z) 3 _ _ L A regs2 mem2 md Hfc HF2 HP).
      split; [rewrite R10, res_of_UP, psn_q_UP; reflexivity|].
      split; [transitivity (getr regs' 18); [exact (RP2 18 ltac:(unfold callee_saved; lia)) | exact K18]|].
      split.
      { split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact K8]|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact K9]|].
        split; [transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia)) | exact K26]|].
        split.
        { split; [exact (KS Hstd')|]. split; [exact Hgd2|]. split; [exists fl, mdv'; exact Herr2|].
          split.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact Q0']. intros i Hi. rewrite length_le8 in Hi.
            apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact QL']. intros i Hi. rewrite length_le8 in Hi.
            apply KI; [apply (proj2 (img_w_iff _)); right; left; unfold G_FILE_LEN in *; lia
                      | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split.
        { apply (tr_mb_bytes mem' mem2 _ _); [|exact QG']. intros i Hi. rewrite length_le8 in Hi.
          apply KI; [apply (proj2 (img_w_iff _)); right; left; unfold G_FILE_LEN in *; lia
                    | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split; [destruct (mstl_frame _ _ _ _ _ _ _ HMS2) as (_ & _ & _ & HB2 & _); exact HB2|].
        pose proof (ss_cells_bytes _ _ _ C24n) as B24. cbn [cells_bytes cbytes] in B24. rewrite app_nil_r in B24.
        apply (tr_mb_bytes mem' mem2 _ _); [|exact B24]. intros i Hi. rewrite length_le8 in Hi.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      rewrite pos_of_UP, psn_q_UP in HMS2.
      split; [exact HMS2|].
      split.
      { apply (tr_img_rw mem' mem2 A_OFL_HEAD _); [|exact HOO']. intros i Hi.
        change (Z.of_nat (cells_size [C8 (wz h)])) with 8 in Hi.
        assert (W' : img_w (A_OFL_HEAD + i)) by (right; left; lia).
        split; [exact W' | apply KI; [exact W' | unfold A_OFL_HEAD, A_STDERR; lia]]. }
      split.
      { rewrite lol_of_UP, psn_lh_UP, vt_of_UP, vid_of_UP, psn_q_UP in HPS2.
        exists (wz 0), (wz 0), (wz 0), pad. exact HPS2. }
      split.
      { specialize (HTS2 ltac:(unfold fsp, SLOT_FRAME in *; lia)). rewrite ts_of_UP, psn_q_UP in HTS2. exact HTS2. }
      exists bj2. split; [exact HU2|]. split; [rewrite HL2; exact HL|].
      rewrite is_fit_kind_UP, incl_UP, rec_bytes_UP, !psn_q_UP in HFT2. exact HFT2.
Qed.

Lemma uf_frw : forall g km hb L A regs mem md (m0 : word -> option byte) a cs,
  FR B APIf ra empty g km hb L A regs mem md -> g_S g - SLOT_K <= a -> a + Z.of_nat (cells_size cs) <= g_S g ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte rsegs mem (a + i) = mbyte rsegs m0 (a + i)) ->
  rw_cells rsegs m0 a cs -> rw_cells rsegs mem a cs.
Proof.
  intros g km hb L A regs mem md m0 a cs HF H1 H2 HE [[Hwf Hb] (W1 & W2 & W3)].
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HW).
  split; [split; [exact Hwf|]|].
  - apply (tr_mb_bytes m0 mem a _); [|exact Hb]. intros i Hi.
    rewrite cells_bytes_length in Hi by exact Hwf. exact (HE i Hi).
  - split; [exact W1|]. split; [exact W2|]. intros i Hi.
    pose proof (HW (a + i) ltac:(lia)) as Wi. rewrite (sg_segs B APIf ra empty FF) in Wi. exact Wi.
Qed.

Lemma uf_hbw : forall g km hb L A regs mem md (m0 : word -> option byte) a k cs,
  FR B APIf ra empty g km hb L A regs mem md -> Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  In (a, k) hb -> Z.of_nat (cells_size cs) <= k ->
  (forall i, 0 <= i < k -> mbyte rsegs mem (a + i) = mbyte rsegs m0 (a + i)) ->
  rw_cells rsegs m0 a cs -> rw_cells rsegs mem a cs.
Proof.
  intros g km hb L A regs mem md m0 a k cs HF HP Hin Hk HE [[Hwf Hb] (W1 & W2 & W3)].
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HW & _).
  split; [split; [exact Hwf|]|].
  - apply (tr_mb_bytes m0 mem a _); [|exact Hb]. intros i Hi.
    rewrite cells_bytes_length in Hi by exact Hwf. apply HE. lia.
  - split; [exact W1|]. split; [exact W2|]. intros i Hi.
    pose proof (proj1 (HW i ltac:(lia))) as Wi. rewrite (sg_segs B APIf ra empty FF) in Wi. exact Wi.
Qed.

Lemma ug_B : Hcut_o B APIf ra (Inv_K12e14 B APIf ra empty) (fun g => uwalk g 24 ++ uC0 g) ->
  HCT B APIf ra (Inv_K1310c B APIf ra empty) ->
  Hcut_o B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof.
  intros HX HR7 g c (b & [(Hgood & h & HC) | (Hgood & HC)]); cbv beta.
  - apply (cut_open B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 2 [(b, un g); (h, 1304)] _ c _ (Post_o B APIf ra g) HC).
    intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H26 & (Hstd & Hgd & (fl & mdv & Herr) & Q0 & QL) & QG & HBF
      & (pad & HPS) & HMS & HOO).
    pose proof HF as (HGV & _). pose proof HGV as (Hgn & _ & _ & _ & HSc & _ & Hroom & _).
    rewrite (uf_out_good g ltac:(lia) Hgood).
    pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
    pose proof (@YM05.alloc_ceiling_val rc) as HAC.
    assert (HK0 : SLOT_K = 65536) by reflexivity.
    destruct (ss_hb_blk B APIf ra empty FF g 2 _ L A regs mem md b (un g) HF HP
      ltac:(cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
    pose proof (uf_un_le g) as Hun. pose proof (uf_ud g) as Hud.
    assert (USP : bv_unsigned (getr regs 2) = fsp g)
      by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
    destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g _ _ L A regs mem md HF)) as (Hh & Hl).
    assert (Q0' : bytes_at rsegs mem (fsp g) (le8 (wz (ud g))))
      by (unfold q64, spk in Q0; rewrite Z.add_0_r in Q0; exact Q0).
    pose proof (uf_psc_sw _ _ _ _ _ _ _ _ HPS) as HSW.
    replace (spk g 48 + 8) with (fsp g + 56) in HSW by (unfold spk; lia).
    apply (ss_kA_run0_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) mem md
      (fun R pc' m' => m' = mem /\ pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) /\ getr R 9 = wz (ucap g) /\
         getr R 10 = wz (ubn g) /\ KP [2; 3; 4; 8; 26] regs R)
      _ (Post_o B APIf ra g) Hh Hl).
    + rewrite ss_mkR_of. eapply evt_mono.
      * exact (ubs_B_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
          (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
          (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
          (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem (fsp g) b (un g) (ud g)
          (ucap g) 0 (uF g) U.Prog.rd32f.rd32f_holds USP H10 H8 H26 QL eq_refl HBF ltac:(lia) ltac:(lia) Q0' Hud
          eq_refl ltac:(unfold ugood in Hgood; rewrite Hgood; reflexivity) (fun _ => HSW)
          ltac:(intros HG'; unfold ugood in Hgood; rewrite Hgood in HG'; discriminate HG')).
      * intros ms' [(_ & a1' & a2' & a3' & a4' & a5' & ->) | (HG' & _)].
        -- do 3 eexists. split; [reflexivity|]. cbv beta.
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [reflexivity|].
           intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
        -- exfalso. unfold ugood in Hgood. rewrite Hgood in HG'. discriminate HG'.
    + intros R pc' m' regs' (-> & -> & G1 & G9 & G10 & GK) XR.
      assert (KR : forall r, In r [2; 3; 4; 8; 26] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
      { intros r Hr. rewrite (ss_getr_eqv _ _ _ XR). exact (GK r Hr). }
      assert (HF' : FR B APIf ra empty g 2 [(b, un g); (h, 1304)] L A regs' mem md).
      { apply (ss_FR_hb B APIf ra empty FF g 2 _ L A regs mem md regs' mem HF HP);
          [| intros x _ _; reflexivity | apply wmono_refl].
        intros k Hk. apply KR. cbn [In] in Hk |- *. tauto. }
      assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
      assert (K9 : getr regs' 9 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
      assert (K10 : getr regs' 10 = wz (ubn g)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
      assert (K8 : getr regs' 8 = wz b) by (transitivity (getr regs 8); [exact (KR 8 ltac:(ss_in)) | exact H8]).
      assert (K26 : getr regs' 26 = wz G_FILE_LEN)
        by (transitivity (getr regs 26); [exact (KR 26 ltac:(ss_in)) | exact H26]).
      rewrite <- (ss_malloc_pc B APIf ra empty FF).
      apply (ss_malloc_step B APIf ra empty FF g 2 [(b, un g); (h, 1304)] L A regs' mem md (ubn g) _
        (Post_o B APIf ra g) HF' HP).
      * cbn [length]. lia.
      * unfold hb_bytes. cbn [map fold_right snd]. unfold un, zlen in *. lia.
      * unfold ubn, ucap. lia.
      * rewrite K1. apply ug_ret_ok; lia.
      * exact K10.
      * exact Hstd.
      * intros L' A' regs2 mem2 md2 buf HF2 HP2 RP2 H10b Hbuf KF KB KI HSTD2 HGRD2.
        rewrite K1. apply HX. exists b, h, buf. split; [exact Hgood|].
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) 3 _ _ L' A' regs2 mem2 md2 Hfrm HF2 HP2).
        rewrite (sg_segs B APIf ra empty FF) in KF, KB, KI.
        split; [exact H10b|].
        split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact K8]|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact K9]|].
        split; [transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia)) | exact K26]|].
        split.
        { split; [exact HSTD2|]. split; [exact HGRD2|].
          split; [apply (tr_errf mem mem2 KI); exists fl, mdv; exact Herr|].
          split.
          - apply (tr_mb_bytes mem mem2 _ _); [|exact Q0]. intros i Hi. rewrite length_le8 in Hi.
            apply KF. unfold spk, fsp, SLOT_FRAME in *. lia.
          - apply (tr_mb_bytes mem mem2 _ _); [|exact QL]. intros i Hi. rewrite length_le8 in Hi.
            apply KI. apply (proj2 (img_w_iff _)). right. left. unfold G_FILE_LEN. lia. }
        split.
        { apply (tr_mb_bytes mem mem2 _ _); [|exact QG]. intros i Hi. rewrite length_le8 in Hi.
          apply KI. apply (proj2 (img_w_iff _)). right. left. unfold G_FILE_LEN. lia. }
        split.
        { apply (tr_mb_bytes mem mem2 _ _); [|exact HBF]. intros i Hi.
          apply (KB b (un g) i); [cbn [In]; left; reflexivity | unfold un, zlen; lia]. }
        split.
        { exists pad. apply (uf_frw g _ _ L' A' regs2 mem2 md2 mem _ _ HF2);
            [unfold spk, fsp, SLOT_FRAME in *; lia | rewrite uf_ps_sz; unfold spk, fsp, SLOT_FRAME in *; lia
            | | exact HPS].
          intros i Hi. rewrite uf_ps_sz in Hi. apply KF. unfold spk, fsp, SLOT_FRAME in *. lia. }
        split.
        { destruct (mstl_frame _ _ _ _ _ _ _ HMS) as (cs & Hcs & HCS & HBF0 & _ & _ & K).
          apply K.
          - apply (uf_hbw g _ _ L' A' regs2 mem2 md2 mem h 1304 cs HF2 HP2);
              [cbn [In app]; right; left; reflexivity | rewrite Hcs; lia | | exact HCS].
            intros i Hi. apply (KB h 1304 i); [cbn [In]; right; left; reflexivity | exact Hi].
          - apply (tr_mb_bytes mem mem2 _ _); [|exact HBF]. intros i Hi.
            apply (KB b (un g) i); [cbn [In]; left; reflexivity | unfold un, zlen; lia]. }
        split.
        { apply (tr_img_rw mem mem2 A_OFL_HEAD _); [|exact HOO]. intros i Hi.
          change (Z.of_nat (cells_size [C8 (wz h)])) with 8 in Hi.
          assert (W' : img_w (A_OFL_HEAD + i)) by (right; left; lia).
          split; [exact W' | exact (KI _ W')]. }
        destruct (ss_hb_blk B APIf ra empty FF g _ _ L' A' regs2 mem2 md2 buf (ubn g) HF2 HP2
          ltac:(cbn [In app]; right; right; left; reflexivity)) as (HWb & Hbu1 & Hbu2 & _).
        rewrite (sg_segs B APIf ra empty FF) in HWb.
        exists (ss_rd_list mem2 buf (Z.to_nat (ubn g))). split.
        { apply (Arr.u8arr_of_rw_cells rsegs mem2 buf (Z.to_nat (ubn g))).
          apply uf_blk_cb; [lia | lia | unfold ubn; lia |].
          intros i Hi. destruct (HWb i Hi) as (W1 & W2 & _). split; assumption. }
        rewrite ss_rd_list_len. unfold ubn. lia.
  - apply (cut_open B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 1 [(b, un g)] _ c _ (Post_o B APIf ra g) HC).
    intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q48 & HOE).
    rewrite (uf_out_ref g Hgood).
    pose proof HF as (HGV & _).
    pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
    pose proof (@YM05.alloc_ceiling_val rc) as HAC.
    destruct (ss_hb_blk B APIf ra empty FF g 1 _ L A regs mem md b (un g) HF HP
      ltac:(cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
    pose proof (uf_ud g) as Hud.
    assert (USP : bv_unsigned (getr regs 2) = fsp g)
      by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
    destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g _ _ L A regs mem md HF)) as (Hh & Hl).
    assert (Q0' : bytes_at rsegs mem (fsp g) (le8 (wz (ud g))))
      by (unfold q64, spk in Q0; rewrite Z.add_0_r in Q0; exact Q0).
    apply (ss_kA_run0_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) mem md
      (fun R pc' m' => m' = mem /\ pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_free) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) /\ getr R 10 = wz b /\
         KP [2; 3; 4] regs R)
      _ (Post_o B APIf ra g) Hh Hl).
    + rewrite ss_mkR_of. eapply evt_mono.
      * exact (ubs_B_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
          (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
          (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
          (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem (fsp g) b (un g) (ud g)
          (ucap g) (-1) (uF g) U.Prog.rd32f.rd32f_holds USP H10 H8 H26 QL eq_refl HBF ltac:(lia) ltac:(lia) Q0' Hud
          eq_refl ltac:(unfold ugood in Hgood; rewrite Hgood; reflexivity)
          ltac:(intros HG'; unfold ugood in Hgood; rewrite Hgood in HG'; discriminate HG') (fun _ => Q48)).
      * intros ms' [(HG' & _) | (_ & a1' & a2' & a3' & a4' & a5' & ->)].
        -- exfalso. unfold ugood in Hgood. rewrite Hgood in HG'. discriminate HG'.
        -- do 3 eexists. split; [reflexivity|]. cbv beta.
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[]]]]; reflexivity.
    + intros R pc' m' regs' (-> & -> & G1 & G10 & GK) XR.
      assert (HF' : FR B APIf ra empty g 1 [(b, un g)] L A regs' mem md).
      { apply (ss_FR_hb B APIf ra empty FF g 1 _ L A regs mem md regs' mem HF HP);
          [| intros x _ _; reflexivity | apply wmono_refl].
        intros k Hk. rewrite (ss_getr_eqv _ _ _ XR). exact (GK k Hk). }
      assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
      rewrite <- (ss_free_pc B APIf ra empty FF).
      apply (ss_free_step B APIf ra empty FF g 1 [] b (un g) [] L A regs' mem md _ (Post_o B APIf ra g) HF' HP).
      * rewrite K1. apply ug_ret_ok; lia.
      * rewrite (ss_getr_eqv _ _ 10 XR). exact G10.
      * exact Hstd.
      * intros L' A' regs2 mem2 md2 HF2 HP2 _ _ KI HSTD2 HGRD2.
        rewrite K1. apply HR7. exists 1.
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) 1 [] _ L' A' regs2 mem2 md2 Hfrm HF2 HP2).
        rewrite (sg_segs B APIf ra empty FF) in KI.
        split; [exact HSTD2|]. split; [exact HGRD2|].
        split; [exact (tr_errf mem mem2 KI Herr) | exact (tr_ofl_empty mem mem2 KI HOE)].
Qed.

(* The cut-free twins of ug_C and ug_B: the reader's next, malloc and free through their cut-free contracts. *)
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis HFREECF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis HNEXTCF : forall fx0 : YK11.FPState, @pcap_source_next_contract_cf fx0.

Lemma ug_C_cf : Hcut_cf B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24) ->
  Hcut_cf B APIf ra (Inv_K12e14 B APIf ra empty) (fun g => uwalk g 24 ++ uC0 g).
Proof.
  intros HX g c HCAP (b & h & buf & Hgood & HC). cbv beta.
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) 3 [(b, un g); (h, 1304); (buf, ubn g)] _ c _ (Post_o B APIf ra g)
    HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H9 & H26 & (Hstd & Hgd & (fl & mdv & Herr) & Q0 & QL) & QG & HBF
    & (pad & HPS) & HMS & HOO & (bj & HU & HL)).
  pose proof HF as (HGV & _).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HK0 : SLOT_K = 65536) by reflexivity.
  pose proof HGV as (Hgn & _ & _ & _ & HSc & _).
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md b (un g) HF HP
    ltac:(cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md h 1304 HF HP
    ltac:(cbn [In]; right; left; reflexivity)) as (_ & Hh1 & Hh2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md buf (ubn g) HF HP
    ltac:(cbn [In]; right; right; left; reflexivity)) as (_ & Hu1 & Hu2 & _).
  pose proof (uf_un_le g) as Hun. pose proof (uf_ud g) as Hud.
  assert (Hcap : 0 <= ucap g <= 2040) by (unfold ucap; lia).
  assert (Hbn : ubn g = Z.max (ucap g) 1) by reflexivity.
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  assert (EO : uwalk g 24 ++ uC0 g = UN.psn_out h (uswz g =? 1) (uF g) (ucap g) 24 ++ uafter g 24).
  { rewrite (uwalk_unfold g 24 ltac:(lia)), psn_out_UP. unfold PN.psn_out, uout1, usw.
    destruct (Z.eqb_spec h 0); [lia | reflexivity]. }
  rewrite EO.
  set (W := [(fsp g + 24, fsp g + 32); (fsp g + 40, fsp g + 48)]).
  assert (HSTK : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)).
  { replace (fsp g + 176) with (g_S g) by (unfold fsp, SLOT_FRAME; lia).
    exact (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF). }
  destruct (uf_stk8 _ _ _ (fsp g + 24) HSTK ltac:(unfold fsp, SLOT_FRAME in *; lia) ltac:(lia)) as (v24 & C24).
  destruct (uf_stk8 _ _ _ (fsp g + 40) HSTK ltac:(unfold fsp, SLOT_FRAME in *; lia) ltac:(lia)) as (v40 & C40).
  apply (uf_run_cf B APIf ra empty FF g 3 _ L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) W
    (fun R pc' m' => pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z) /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 10 = wz (fsp g + 48) /\ getr R 11 = wz buf /\ getr R 12 = wz (ucap g) /\
       getr R 13 = wz (fsp g + 40) /\ getr R 18 = wz buf /\ getr R 26 = getr regs 26 /\
       rw_cells rsegs m' (fsp g + 24) [C8 (wz buf)] /\ rw_cells rsegs m' (fsp g + 40) [C8 (wz (-1))])
    _ _ HF HP).
  - intros lo hi y Hin Hy. left. unfold W in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fsp, SLOT_FRAME in *; lia.
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_C_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (g_S g - SLOT_K) (fsp g) buf (ucap g) v24 v40 USP H10 ltac:(lia) H9
      (mem_inv_normalize rsegs mem) HSTK ltac:(unfold fsp, SLOT_FRAME in *; lia) C24 C40)|].
    intros ms (m' & -> & MU & WM & _ & _ & C24' & C40').
    do 3 eexists. split; [reflexivity|].
    split; [do 10 (split; [reflexivity|]); split; [exact C24' | exact C40']|].
    split; [exact MU|]. split; [exact WM|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & G1 & G8 & G9 & G10 & G11 & G12 & G13 & G18 & G26 & C24' & C40') XR HR MU WM HF'.
    assert (HWL : forall lo hi, In (lo, hi) W -> fsp g + 24 <= lo).
    { intros lo hi Hin. unfold W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
    assert (HL0 : forall a n, a + n <= fsp g + 24 -> disjoint_from W a n)
      by (intros a n Ha; exact (uf_dj_lo W a n _ HWL Ha)).
    assert (HIMG : forall a, a <= (symaddr ImgPages.Ubsan.top) -> a <= fsp g + 24)
      by (intros a Ha; unfold fsp, SLOT_FRAME, SS_TOP in *; lia).
    destruct Hstd as (S1 & S2 & S3).
    assert (Hstd' : stdio_ok mem').
    { split; [|split]; (eapply bytes_at_transport; [eassumption | exact MU | apply HL0]);
        cbn [length]; rewrite ?length_le4; apply HIMG; unfold A_LIBC, A_OFL_LOCK; lia. }
    assert (Herr' : errf mem' fl mdv).
    { destruct Herr as (E1 & E2 & E3). split; [|split; assumption].
      apply (rw_cells_transport rsegs W mem mem' _ _ E1 MU WM). apply HL0.
      change (Z.of_nat (cells_size (stderr_cells fl mdv))) with 232. apply HIMG. unfold A_STDERR. lia. }
    pose proof (bytes_at_transport rsegs W mem mem' _ _ Q0 MU) as Q0'.
    specialize (Q0' ltac:(rewrite length_le8; apply HL0; unfold spk; lia)).
    pose proof (bytes_at_transport rsegs W mem mem' _ _ QL MU) as QL'.
    specialize (QL' ltac:(rewrite length_le8; apply HL0; apply HIMG; unfold G_FILE_LEN; lia)).
    pose proof (bytes_at_transport rsegs W mem mem' _ _ QG MU) as QG'.
    specialize (QG' ltac:(rewrite length_le8; apply HL0; apply HIMG; unfold G_FILE_LEN; lia)).
    pose proof (rw_cells_transport rsegs W mem mem' _ _ HPS MU WM) as HPS'.
    specialize (HPS' ltac:(rewrite uf_ps_sz; unfold W, spk; cbn [disjoint_from]; repeat split; lia)).
    pose proof (rw_cells_transport rsegs W mem mem' _ _ HOO MU WM) as HOO'.
    specialize (HOO' ltac:(apply HL0; change (Z.of_nat (cells_size [C8 (wz h)])) with 8; apply HIMG;
      unfold A_OFL_HEAD; lia)).
    pose proof (mstl_transport W mem mem' h b (uF g) 24 (wz 0) (wz 0) HMS MU WM) as HMS'.
    specialize (HMS' ltac:(apply HL0; unfold fsp, SLOT_FRAME in *; lia)
      ltac:(apply HL0; unfold un, zlen, fsp, SLOT_FRAME in *; lia)).
    pose proof (Arr.u8arr_transport rsegs W mem mem' buf bj HU MU WM) as HU'.
    specialize (HU' ltac:(apply HL0; rewrite HL; unfold fsp, SLOT_FRAME in *; lia)).
    assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    assert (K8 : getr regs' 8 = wz b) by (rewrite (ss_getr_eqv _ _ 8 XR); rewrite G8; exact H8).
    assert (K9 : getr regs' 9 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 9 XR); rewrite G9; exact H9).
    assert (K10 : getr regs' 10 = wz (fsp g + 48)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
    assert (K11 : getr regs' 11 = wz buf) by (rewrite (ss_getr_eqv _ _ 11 XR); exact G11).
    assert (K12 : getr regs' 12 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 12 XR); exact G12).
    assert (K13 : getr regs' 13 = wz (fsp g + 40)) by (rewrite (ss_getr_eqv _ _ 13 XR); exact G13).
    assert (K18 : getr regs' 18 = wz buf) by (rewrite (ss_getr_eqv _ _ 18 XR); exact G18).
    assert (K26 : getr regs' 26 = wz G_FILE_LEN) by (rewrite (ss_getr_eqv _ _ 26 XR); rewrite G26; exact H26).
    pose proof (uf_rw_rel mem' m' _ _ HR C24') as C24n.
    pose proof (uf_rw_rel mem' m' _ _ HR C40') as C40n.
    change (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next)) with (Z_to_bv 64 PCAP_SOURCE_NEXT).
    apply (ps_next_step_cf B APIf ra empty FF (HNEXTCF _) g 3 _ [(b, un g); (h, 1304)] L A regs' mem' md
      (fsp g + 48) buf (ucap g) (fsp g + 40) h (uswz g) b 24 fl mdv (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz (-1))
      pad bj (uF g) (uafter g 24) (Post_o B APIf ra g) HF' HP Hfrm).
    + rewrite K1. apply ug_ret_ok; lia.
    + exact K10.
    + exact K11.
    + exact K12.
    + exact K13.
    + lia.
    + unfold fsp, SLOT_FRAME; lia.
    + Z.div_mod_to_equations. lia.
    + exact HPS'.
    + exact (Permutation_sym (Permutation_cons_append [(b, un g); (h, 1304)] (buf, ubn g))).
    + exact HU'.
    + exact HL.
    + lia.
    + intros _. split; [lia|]. split; [unfold fsp, SLOT_FRAME; lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [lia | exact C40n].
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|]. split; [exact HMS'|].
      split; [exact (uf_swz g)|]. unfold un, zlen in *; lia.
    + exact Herr'.
    + intros regs2 mem2 Ft fc' mdv' Hfc HFt HF2 RP2 KF KB KI KS Herr2 Hgd2 _ HPO.
      destruct (HPO ltac:(lia)) as (R10 & HMS2 & HPS2 & (bj2 & HU2 & HL2 & HFT2) & HTS2).
      rewrite (sg_segs B APIf ra empty FF) in KF, KB, KI.
      rewrite K1. apply (HX g _ HCAP). exists b, h, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z) 3 _ _ L A regs2 mem2 md Hfc HF2 HP).
      split; [rewrite R10, res_of_UP, psn_q_UP; reflexivity|].
      split; [transitivity (getr regs' 18); [exact (RP2 18 ltac:(unfold callee_saved; lia)) | exact K18]|].
      split.
      { split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact K8]|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact K9]|].
        split; [transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia)) | exact K26]|].
        split.
        { split; [exact (KS Hstd')|]. split; [exact Hgd2|]. split; [exists fl, mdv'; exact Herr2|].
          split.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact Q0']. intros i Hi. rewrite length_le8 in Hi.
            apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact QL']. intros i Hi. rewrite length_le8 in Hi.
            apply KI; [apply (proj2 (img_w_iff _)); right; left; unfold G_FILE_LEN in *; lia
                      | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split.
        { apply (tr_mb_bytes mem' mem2 _ _); [|exact QG']. intros i Hi. rewrite length_le8 in Hi.
          apply KI; [apply (proj2 (img_w_iff _)); right; left; unfold G_FILE_LEN in *; lia
                    | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split; [destruct (mstl_frame _ _ _ _ _ _ _ HMS2) as (_ & _ & _ & HB2 & _); exact HB2|].
        pose proof (ss_cells_bytes _ _ _ C24n) as B24. cbn [cells_bytes cbytes] in B24. rewrite app_nil_r in B24.
        apply (tr_mb_bytes mem' mem2 _ _); [|exact B24]. intros i Hi. rewrite length_le8 in Hi.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      rewrite pos_of_UP, psn_q_UP in HMS2.
      split; [exact HMS2|].
      split.
      { apply (tr_img_rw mem' mem2 A_OFL_HEAD _); [|exact HOO']. intros i Hi.
        change (Z.of_nat (cells_size [C8 (wz h)])) with 8 in Hi.
        assert (W' : img_w (A_OFL_HEAD + i)) by (right; left; lia).
        split; [exact W' | apply KI; [exact W' | unfold A_OFL_HEAD, A_STDERR; lia]]. }
      split.
      { rewrite lol_of_UP, psn_lh_UP, vt_of_UP, vid_of_UP, psn_q_UP in HPS2.
        exists (wz 0), (wz 0), (wz 0), pad. exact HPS2. }
      split.
      { specialize (HTS2 ltac:(unfold fsp, SLOT_FRAME in *; lia)). rewrite ts_of_UP, psn_q_UP in HTS2. exact HTS2. }
      exists bj2. split; [exact HU2|]. split; [rewrite HL2; exact HL|].
      rewrite is_fit_kind_UP, incl_UP, rec_bytes_UP, !psn_q_UP in HFT2. exact HFT2.
Qed.

Lemma ug_B_cf : Hcut_cf B APIf ra (Inv_K12e14 B APIf ra empty) (fun g => uwalk g 24 ++ uC0 g) ->
  Hcut_cf B APIf ra (Inv_K1310c B APIf ra empty) (fun _ => []) ->
  Hcut_cf B APIf ra (Inv_K12d70 B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof.
  intros HX HR7 g c HCAP (b & [(Hgood & h & HC) | (Hgood & HC)]); cbv beta.
  - apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 2 [(b, un g); (h, 1304)] _ c _ (Post_o B APIf ra g) HC).
    intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H26 & (Hstd & Hgd & (fl & mdv & Herr) & Q0 & QL) & QG & HBF
      & (pad & HPS) & HMS & HOO).
    pose proof HF as (HGV & _). pose proof HGV as (Hgn & _ & _ & _ & HSc & _ & Hroom & _).
    rewrite (uf_out_good g ltac:(lia) Hgood).
    pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
    pose proof (@YM05.alloc_ceiling_val rc) as HAC.
    assert (HK0 : SLOT_K = 65536) by reflexivity.
    destruct (ss_hb_blk B APIf ra empty FF g 2 _ L A regs mem md b (un g) HF HP
      ltac:(cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
    pose proof (uf_un_le g) as Hun. pose proof (uf_ud g) as Hud.
    assert (USP : bv_unsigned (getr regs 2) = fsp g)
      by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
    destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g _ _ L A regs mem md HF)) as (Hh & Hl).
    assert (Q0' : bytes_at rsegs mem (fsp g) (le8 (wz (ud g))))
      by (unfold q64, spk in Q0; rewrite Z.add_0_r in Q0; exact Q0).
    pose proof (uf_psc_sw _ _ _ _ _ _ _ _ HPS) as HSW.
    replace (spk g 48 + 8) with (fsp g + 56) in HSW by (unfold spk; lia).
    apply (ss_kA_run0_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) mem md
      (fun R pc' m' => m' = mem /\ pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) /\ getr R 9 = wz (ucap g) /\
         getr R 10 = wz (ubn g) /\ KP [2; 3; 4; 8; 26] regs R)
      _ (Post_o B APIf ra g) Hh Hl).
    + rewrite ss_mkR_of. eapply evt_mono.
      * exact (ubs_B_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
          (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
          (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
          (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem (fsp g) b (un g) (ud g)
          (ucap g) 0 (uF g) U.Prog.rd32f.rd32f_holds USP H10 H8 H26 QL eq_refl HBF ltac:(lia) ltac:(lia) Q0' Hud
          eq_refl ltac:(unfold ugood in Hgood; rewrite Hgood; reflexivity) (fun _ => HSW)
          ltac:(intros HG'; unfold ugood in Hgood; rewrite Hgood in HG'; discriminate HG')).
      * intros ms' [(_ & a1' & a2' & a3' & a4' & a5' & ->) | (HG' & _)].
        -- do 3 eexists. split; [reflexivity|]. cbv beta.
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [reflexivity|].
           intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
        -- exfalso. unfold ugood in Hgood. rewrite Hgood in HG'. discriminate HG'.
    + intros R pc' m' regs' (-> & -> & G1 & G9 & G10 & GK) XR.
      assert (KR : forall r, In r [2; 3; 4; 8; 26] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
      { intros r Hr. rewrite (ss_getr_eqv _ _ _ XR). exact (GK r Hr). }
      assert (HF' : FR B APIf ra empty g 2 [(b, un g); (h, 1304)] L A regs' mem md).
      { apply (ss_FR_hb B APIf ra empty FF g 2 _ L A regs mem md regs' mem HF HP);
          [| intros x _ _; reflexivity | apply wmono_refl].
        intros k Hk. apply KR. cbn [In] in Hk |- *. tauto. }
      assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
      assert (K9 : getr regs' 9 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
      assert (K10 : getr regs' 10 = wz (ubn g)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
      assert (K8 : getr regs' 8 = wz b) by (transitivity (getr regs 8); [exact (KR 8 ltac:(ss_in)) | exact H8]).
      assert (K26 : getr regs' 26 = wz G_FILE_LEN)
        by (transitivity (getr regs 26); [exact (KR 26 ltac:(ss_in)) | exact H26]).
      rewrite <- (ss_malloc_pc B APIf ra empty FF).
      apply (ss_malloc_step_cf B APIf ra empty FF HMALCF LIMLAW g 2 [(b, un g); (h, 1304)] L A regs' mem md
        (ubn g) _ (Post_o B APIf ra g) HCAP HF' HP).
      * cbn [length]. lia.
      * unfold hb_bytes. cbn [map fold_right snd]. unfold un, zlen in *. lia.
      * unfold ubn, ucap. lia.
      * rewrite K1. apply ug_ret_ok; lia.
      * exact K10.
      * exact Hstd.
      * intros L' A' regs2 mem2 md2 buf HF2 HP2 RP2 H10b Hbuf KF KB KI HSTD2 HGRD2.
        rewrite K1. apply (HX g _ HCAP). exists b, h, buf. split; [exact Hgood|].
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x190)%Z) 3 _ _ L' A' regs2 mem2 md2 Hfrm HF2 HP2).
        rewrite (sg_segs B APIf ra empty FF) in KF, KB, KI.
        split; [exact H10b|].
        split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact K8]|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact K9]|].
        split; [transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia)) | exact K26]|].
        split.
        { split; [exact HSTD2|]. split; [exact HGRD2|].
          split; [apply (tr_errf mem mem2 KI); exists fl, mdv; exact Herr|].
          split.
          - apply (tr_mb_bytes mem mem2 _ _); [|exact Q0]. intros i Hi. rewrite length_le8 in Hi.
            apply KF. unfold spk, fsp, SLOT_FRAME in *. lia.
          - apply (tr_mb_bytes mem mem2 _ _); [|exact QL]. intros i Hi. rewrite length_le8 in Hi.
            apply KI. apply (proj2 (img_w_iff _)). right. left. unfold G_FILE_LEN. lia. }
        split.
        { apply (tr_mb_bytes mem mem2 _ _); [|exact QG]. intros i Hi. rewrite length_le8 in Hi.
          apply KI. apply (proj2 (img_w_iff _)). right. left. unfold G_FILE_LEN. lia. }
        split.
        { apply (tr_mb_bytes mem mem2 _ _); [|exact HBF]. intros i Hi.
          apply (KB b (un g) i); [cbn [In]; left; reflexivity | unfold un, zlen; lia]. }
        split.
        { exists pad. apply (uf_frw g _ _ L' A' regs2 mem2 md2 mem _ _ HF2);
            [unfold spk, fsp, SLOT_FRAME in *; lia | rewrite uf_ps_sz; unfold spk, fsp, SLOT_FRAME in *; lia
            | | exact HPS].
          intros i Hi. rewrite uf_ps_sz in Hi. apply KF. unfold spk, fsp, SLOT_FRAME in *. lia. }
        split.
        { destruct (mstl_frame _ _ _ _ _ _ _ HMS) as (cs & Hcs & HCS & HBF0 & _ & _ & K).
          apply K.
          - apply (uf_hbw g _ _ L' A' regs2 mem2 md2 mem h 1304 cs HF2 HP2);
              [cbn [In app]; right; left; reflexivity | rewrite Hcs; lia | | exact HCS].
            intros i Hi. apply (KB h 1304 i); [cbn [In]; right; left; reflexivity | exact Hi].
          - apply (tr_mb_bytes mem mem2 _ _); [|exact HBF]. intros i Hi.
            apply (KB b (un g) i); [cbn [In]; left; reflexivity | unfold un, zlen; lia]. }
        split.
        { apply (tr_img_rw mem mem2 A_OFL_HEAD _); [|exact HOO]. intros i Hi.
          change (Z.of_nat (cells_size [C8 (wz h)])) with 8 in Hi.
          assert (W' : img_w (A_OFL_HEAD + i)) by (right; left; lia).
          split; [exact W' | exact (KI _ W')]. }
        destruct (ss_hb_blk B APIf ra empty FF g _ _ L' A' regs2 mem2 md2 buf (ubn g) HF2 HP2
          ltac:(cbn [In app]; right; right; left; reflexivity)) as (HWb & Hbu1 & Hbu2 & _).
        rewrite (sg_segs B APIf ra empty FF) in HWb.
        exists (ss_rd_list mem2 buf (Z.to_nat (ubn g))). split.
        { apply (Arr.u8arr_of_rw_cells rsegs mem2 buf (Z.to_nat (ubn g))).
          apply uf_blk_cb; [lia | lia | unfold ubn; lia |].
          intros i Hi. destruct (HWb i Hi) as (W1 & W2 & _). split; assumption. }
        rewrite ss_rd_list_len. unfold ubn. lia.
  - apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z) 1 [(b, un g)] _ c _ (Post_o B APIf ra g) HC).
    intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q48 & HOE).
    rewrite (uf_out_ref g Hgood).
    pose proof HF as (HGV & _).
    pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
    pose proof (@YM05.alloc_ceiling_val rc) as HAC.
    destruct (ss_hb_blk B APIf ra empty FF g 1 _ L A regs mem md b (un g) HF HP
      ltac:(cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
    pose proof (uf_ud g) as Hud.
    assert (USP : bv_unsigned (getr regs 2) = fsp g)
      by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
    destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g _ _ L A regs mem md HF)) as (Hh & Hl).
    assert (Q0' : bytes_at rsegs mem (fsp g) (le8 (wz (ud g))))
      by (unfold q64, spk in Q0; rewrite Z.add_0_r in Q0; exact Q0).
    apply (ss_kA_run0_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xec)%Z)) mem md
      (fun R pc' m' => m' = mem /\ pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_free) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) /\ getr R 10 = wz b /\
         KP [2; 3; 4] regs R)
      _ (Post_o B APIf ra g) Hh Hl).
    + rewrite ss_mkR_of. eapply evt_mono.
      * exact (ubs_B_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
          (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
          (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
          (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
          (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem (fsp g) b (un g) (ud g)
          (ucap g) (-1) (uF g) U.Prog.rd32f.rd32f_holds USP H10 H8 H26 QL eq_refl HBF ltac:(lia) ltac:(lia) Q0' Hud
          eq_refl ltac:(unfold ugood in Hgood; rewrite Hgood; reflexivity)
          ltac:(intros HG'; unfold ugood in Hgood; rewrite Hgood in HG'; discriminate HG') (fun _ => Q48)).
      * intros ms' [(HG' & _) | (_ & a1' & a2' & a3' & a4' & a5' & ->)].
        -- exfalso. unfold ugood in Hgood. rewrite Hgood in HG'. discriminate HG'.
        -- do 3 eexists. split; [reflexivity|]. cbv beta.
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[]]]]; reflexivity.
    + intros R pc' m' regs' (-> & -> & G1 & G10 & GK) XR.
      assert (HF' : FR B APIf ra empty g 1 [(b, un g)] L A regs' mem md).
      { apply (ss_FR_hb B APIf ra empty FF g 1 _ L A regs mem md regs' mem HF HP);
          [| intros x _ _; reflexivity | apply wmono_refl].
        intros k Hk. rewrite (ss_getr_eqv _ _ _ XR). exact (GK k Hk). }
      assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
      rewrite <- (ss_free_pc B APIf ra empty FF).
      apply (ss_free_step_cf B APIf ra empty FF HFREECF g 1 [] b (un g) [] L A regs' mem md _ (Post_o B APIf ra g)
        HF' HP).
      * rewrite K1. apply ug_ret_ok; lia.
      * rewrite (ss_getr_eqv _ _ 10 XR). exact G10.
      * exact Hstd.
      * intros L' A' regs2 mem2 md2 HF2 HP2 _ _ KI HSTD2 HGRD2.
        rewrite K1. apply (HR7 g _ HCAP). exists 1.
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) 1 [] _ L' A' regs2 mem2 md2 Hfrm HF2 HP2).
        rewrite (sg_segs B APIf ra empty FF) in KI.
        split; [exact HSTD2|]. split; [exact HGRD2|].
        split; [exact (tr_errf mem mem2 KI Herr) | exact (tr_ofl_empty mem mem2 KI HOE)].
Qed.

End F.
