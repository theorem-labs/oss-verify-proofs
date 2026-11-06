From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel libreac_fuzz_fopen_c
  pcap_source_struct pcap_source_struct_next pcap_source_open_c pcap_source_close_c pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require memcpy pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PCut PImg PSteps
  PSegE PSegB.
Import ListNotations.
Open Scope Z_scope.

Ltac ac_keep regs1 regs0 k HRP Hx HK H :=
  transitivity (getr regs1 (Z_to_bv 5 k)); [exact (HRP k ltac:(unfold callee_saved; lia))|];
  rewrite (ss_getr_eqv _ _ _ Hx); transitivity (getr regs0 (Z_to_bv 5 k)); [exact (HK k ltac:(ss_in)) | exact H].

Lemma ac_gn : forall g, 0 <= gn g <= g_n g.
Proof. intros g. unfold gn, gF, g_n. destruct (g_in g) as [|d l]; cbn [tl length]; lia. Qed.

Lemma ac_src : forall g, gn g <> 0 -> gsrc g = g_p g + 1 /\ g_n g = gn g + 1.
Proof.
  intros g. unfold gn, gF, gsrc, g_n. destruct (g_in g) as [|d l]; cbn [tl length]; intros H;
    [lia | split; [reflexivity | lia]].
Qed.

Lemma ac_rw_norm : forall m a cs, MemNorm.ro_agree rsegs m -> rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Mem.ro_addr rsegs (wa (a + i)) = false) ->
  rw_cells rsegs (MemNorm.normalize rsegs m) a cs.
Proof.
  intros m a cs HR [[Hwf HB] HW] Hro. split; [split; [exact Hwf|]|].
  - exact (MemNorm.bytes_at_normalize rsegs m a _ HR HB).
  - exact (MemNorm.wr_at_norm rsegs m (MemNorm.normalize rsegs m) a _ (MemNorm.mem_rel_normalize rsegs m HR) HW Hro).
Qed.

Lemma ac_rw_back : forall m m0 a cs, MemNorm.mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
  - exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 a _ HR) HB).
  - exact (MemNorm.wr_at_rel rsegs m m0 a _ HR HW).
Qed.

Lemma ac_mb : forall segs W (m m' : word -> option byte) x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mbyte segs m' x = mbyte segs m x.
Proof.
  intros segs W m m' x MU Hx Ho. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite MState.unsigned_lit by exact Hx. exact Ho.
Qed.

Section AC.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HCLOSE : forall fx : YK11.FPState, @pcap_source_close_contract fx rc B (APIf rc).
Hypothesis HOPEN : forall fx : YK11.FPState, @pcap_source_open_contract fx rc B (APIf rc).
Hypothesis HNEXT : forall fx : YK11.FPState, @pcap_source_next_contract fx.

Lemma ac_u8arr : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb -> 0 <= k ->
  exists bj, Arr.u8arr rsegs mem a bj /\ Z.of_nat (length bj) = k.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin Hk.
  destruct (ss_hb_blk (fx:=fx0) B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HB & H4 & Hc & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  exists (ss_rd_list mem a (Z.to_nat k)). rewrite ss_rd_list_len. split; [|lia].
  split.
  - split; [lia|]. split; [rewrite ss_rd_list_len; lia|].
    intros i Hi. rewrite ss_rd_list_len in Hi. rewrite ss_rd_list_nth by exact Hi.
    destruct (HB (Z.of_nat i) ltac:(lia)) as (_ & (v & Hv) & _).
    unfold mrd, wa. rewrite Hv. reflexivity.
  - split; [lia|]. split; [rewrite ss_rd_list_len; lia|].
    intros i Hi. rewrite ss_rd_list_len in Hi.
    destruct (HB i ltac:(lia)) as (W & _). rewrite (ss_segs B APIf ra empty FF) in W. exact W.
Qed.

Lemma ac_by : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs HB HK. apply (ss_bytes_mbyte rsegs m m'); [|exact HB].
  intros i Hi. rewrite <- (ss_segs B APIf ra empty FF). exact (HK i Hi).
Qed.

Lemma ac_img : forall m m' a cs, rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     img_w (a + i) /\ mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf HB] HW] HK. split; [split; [exact Hwf|]|].
  - apply (ac_by m m' a _ HB). intros i Hi. rewrite (cells_bytes_length cs Hwf) in Hi. exact (proj2 (HK i Hi)).
  - destruct HW as (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros i Hi.
    exact (proj1 (img_w_wr m' (a + i) (proj1 (HK i Hi)))).
Qed.

Lemma ac_ofl : forall m m' v, rw_cells rsegs m A_OFL_HEAD [C8 (wz v)] ->
  (forall x, A_OFL_HEAD <= x < A_OFL_HEAD + 8 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  rw_cells rsegs m' A_OFL_HEAD [C8 (wz v)].
Proof.
  intros m m' v H HK. apply (ac_img m m' _ _ H). intros i Hi.
  change (Z.of_nat (cells_size [C8 (wz v)])) with 8 in Hi.
  split; [apply (proj2 (img_w_iff _)); right; right; lia | apply HK; lia].
Qed.

Lemma ac_stdio : forall m m', stdio_ok m ->
  (forall x, 0x10000 <= x < (symaddr ImgPages.Plain.top) -> ~ ((symaddr Symbols.Plain.s_g_file_len) <= x < (symaddr Symbols.Plain.s_environ)) ->
     mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> stdio_ok m'.
Proof.
  intros m m' (S1 & S2 & S3) HK. split; [|split].
  - apply (ac_by m m' _ _ S1). intros i Hi. cbn [length] in Hi. apply HK; unfold A_LIBC; lia.
  - apply (ac_by m m' _ _ S2). intros i Hi. cbn [length] in Hi. apply HK; unfold A_LIBC; lia.
  - apply (ac_by m m' _ _ S3). intros i Hi. rewrite length_le4 in Hi. apply HK; unfold A_OFL_LOCK; lia.
Qed.

Lemma ac_err : forall m m', err_ok m ->
  (forall x, A_STDERR <= x < A_STDERR + 232 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> err_ok m'.
Proof.
  intros m m' (fl & md & HE) HK. exists fl, md.
  apply (errf_keep B APIf ra empty FF m m' fl md HE). intros i Hi. apply HK. lia.
Qed.

Lemma ac_gfile : forall m m' a bs, (symaddr Symbols.Plain.s_g_file_len) <= a -> a + Z.of_nat (length bs) <= (symaddr Symbols.Plain.s_environ) -> bytes_at rsegs m a bs ->
  (forall x, (symaddr Symbols.Plain.s_g_file_len) <= x < (symaddr Symbols.Plain.s_environ) -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> bytes_at rsegs m' a bs.
Proof. intros m m' a bs H1 H2 HB HK. apply (ac_by m m' a bs HB). intros i Hi. apply HK. lia. Qed.

Lemma seg_A : Hcut_o B APIf ra (Inv_K2g B APIf ra empty) oOUT ->
  Hcut_o B APIf ra (Inv_K2r B APIf ra empty) oOUT ->
  Hcut_o B APIf ra (Inv_K1 B APIf ra empty) oOUT.
Proof.
  intros HG HR g c (b & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z) km (hb_b g b) (P_K1 g b) c (oOUT g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP
    (H10 & Hb0 & H8 & H9 & H18 & H22 & (HSTD & HGRD & HERR) & HOFL & Hq0 & Hq8 & HSRC).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
  pose proof HGV as (Hgn & Hnp & _ & _ & _ & _ & Hroom & _).
  pose proof (ss_stk_fsp B APIf ra empty g km _ L A regs mem md HF) as (_ & HIL & H8192 & HfS & HSc & HS47 & HK & Hsp).
  pose proof (ss_fr_bnd B APIf ra empty FF g km _ L A regs mem md HF) as (_ & Hf16 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as HAC.
  pose proof (ac_gn g) as Hgnle.
  unfold IMG_HI in HIL.
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md b (gn g) HF HP
    ltac:(unfold hb_b; left; reflexivity)) as (HBK & Hb1 & Hb2 & _).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  assert (HMIr : MemNorm.ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEG in HMI; exact HMI).
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite Hsp; apply MState.unsigned_lit; lia).
  assert (Hp8 : (fsp g + 32) mod 8 = 0) by (clear - Hf16; Z.div_mod_to_equations; lia).
  assert (HBA : gn g = 0 \/ img_apart b (gn g)).
  { destruct (Z.eq_dec (gn g) 0) as [E|E]; [left; exact E | right].
    apply (ps_blk_apart B APIf ra empty FF L A mem md b (gn g) HMR); [|lia].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. unfold hb_b. left. reflexivity. }
  destruct (ac_u8arr g km _ L A regs mem md b (gn g) HF HP ltac:(unfold hb_b; left; reflexivity) ltac:(lia))
    as (jb & HJ & HJn).
  assert (EJ : length jb = length (gF g)) by (unfold gn in HJn; lia).
  assert (HBn : gn g <> 0 -> b <> 0 /\
      rw_cells rsegs (MemNorm.normalize rsegs mem) b [CB (length (gF g)) jb] /\
      (b + gn g <= gsrc g \/ gsrc g + gn g <= b) /\
      (b + gn g <= g_S g - SLOT_K \/ fsp g + 160 <= b) /\ (b + gn g <= (symaddr Symbols.Plain.s_g_file_len) \/ (symaddr Symbols.Plain.s_environ) <= b)).
  { intros Hn0. split; [exact Hb0|].
    split.
    { rewrite <- EJ. apply ac_rw_norm; [exact HMIr | exact (Arr.rw_cells_of_u8arr rsegs mem b jb HJ) |].
      intros i Hi. cbn [cells_size csize] in Hi.
      destruct (Mem.ro_addr rsegs (wa (b + i))) eqn:E; [|reflexivity]. exfalso.
      pose proof (ss_ro_img B APIf ra empty FF _ E) as Hi'. rewrite wa_unsigned in Hi' by lia.
      exact (proj2 (proj2 (HBK i ltac:(lia))) Hi'). }
    split.
    { destruct (ac_src g Hn0) as (Es & En).
      assert (Hin0 : In (g_p g, g_n g) (blocks (g_L g) (g_A g)))
        by (destruct Hnp as [[E _]|[_ H]]; [lia | exact H]).
      destruct (Z_le_gt_dec (b + gn g) (gsrc g)) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (gsrc g + gn g) b) as [D'|D']; [right; exact D'|].
      exfalso.
      destruct (ss_b0_facts B APIf ra empty FF L A mem md (hb_b g b) _ (g_p g) (g_n g) (Z.max b (gsrc g) - g_p g)
        HMR HP Hin0 ltac:(lia)) as (_ & _ & Hnh & _).
      apply Hnh. exists b, (gn g). split; [unfold hb_b; left; reflexivity | lia]. }
    split.
    { left. destruct (ss_hb_low B APIf ra empty FF g km _ L A regs mem md (b + gn g - 1) HF HP
        ltac:(exists b, (gn g); split; [unfold hb_b; left; reflexivity | lia])) as (_ & Hlow). lia. }
    destruct HBA as [E|E]; [lia | unfold img_apart in E; lia]. }
  assert (HGC : rw_cells rsegs mem (symaddr Symbols.Plain.s_g_file_len) [C8 (wz (gn g)); C8 (wz (gsrc g))]).
  { split; [split; [cbn [cells_wf cell_wf]; tauto|]|].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact Hq0|].
      rewrite length_le8. replace ((symaddr Symbols.Plain.s_g_file_len) + Z.of_nat 8) with (symaddr Symbols.Plain.s_g_file) by lia. exact Hq8.
    - change (Z.of_nat (cells_size [C8 (wz (gn g)); C8 (wz (gsrc g))])) with 16.
      split; [lia|]. split; [lia|]. intros i Hi.
      exact (proj1 (img_w_wr mem ((symaddr Symbols.Plain.s_g_file_len) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia))). }
  assert (HGCn : rw_cells rsegs (MemNorm.normalize rsegs mem) (symaddr Symbols.Plain.s_g_file_len) [C8 (wz (gn g)); C8 (wz (gsrc g))]).
  { apply (ac_rw_norm mem _ _ HMIr HGC). intros i Hi.
    change (Z.of_nat (cells_size [C8 (wz (gn g)); C8 (wz (gsrc g))])) with 16 in Hi.
    exact (proj1 (proj2 (img_w_wr mem ((symaddr Symbols.Plain.s_g_file_len) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia)))). }
  apply (ss_kA_run_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) /\ getr R 10 = wz (fsp g + 32) /\ getr R 11 = wz (symaddr (Symbols.Plain.Sec.s_rodata + 0xe9)%Z) /\
       getr R 20 = wz b /\ KP [2; 3; 4; 8; 22] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open) /\
       munch [(fsp g + 32, fsp g + 56); (b, b + gn g); ((symaddr Symbols.Plain.s_g_file), (symaddr Symbols.Plain.s_environ))] (MemNorm.normalize rsegs mem) m' /\
       wmono rsegs (MemNorm.normalize rsegs mem) m' /\
       rw_cells rsegs m' (fsp g + 32) ps_a5 /\ rw_cells rsegs m' (symaddr Symbols.Plain.s_g_file_len) [C8 (wz (gn g)); C8 (wz b)] /\
       (gn g <> 0 -> rw_cells rsegs m' b [CB (length (gF g)) (gF g)]))
    (oOUT g) (Post_o B APIf ra g) Hh Hl HMI).
  - rewrite ss_mkR_of. eapply evt_mono.
    + apply (pcap_A_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (MemNorm.normalize rsegs mem) (gF g) jb (wz (gsrc g)) (fsp g) b (gsrc g) (gn g) (g_S g - SLOT_K)
        memcpy.memcpy_holds USP H10 H9 H18 H22 eq_refl ltac:(lia)
        (MemNorm.bytes_at_normalize rsegs mem _ _ HMIr HSRC) HBn
        ltac:(rewrite HfS; exact (ss_fr_stk B APIf ra empty FF g km _ L A regs mem md HF))
        ltac:(lia) ltac:(lia) HGCn (MemNorm.mem_inv_normalize rsegs mem)).
    + intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM &
        _ & _ & PS & GC & HB').
      do 3 eexists. split; [reflexivity|]. cbv beta.
      do 4 (split; [reflexivity|]).
      split; [intros k Hk; cbn [In] in Hk; destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity|].
      split; [reflexivity|]. exact (conj MU (conj WM (conj PS (conj GC HB')))).
  - intros R pc' m0 regs' mem' (H1 & H10' & H11' & H20' & HKP & -> & MU & WM & HPS & HGF & HBF) Hx Hrel Hsame.
    pose proof (MemNorm.mem_rel_normalize rsegs mem HMIr) as HR0.
    pose proof (MemNorm.munch_rel rsegs _ mem (MemNorm.normalize rsegs mem) mem' m0 HR0 Hrel Hsame MU) as MU'.
    pose proof (MemNorm.wmono_rel rsegs mem (MemNorm.normalize rsegs mem) mem' m0 HR0 Hrel Hsame WM) as WM'.
    assert (HF' : FR B APIf ra empty g km (hb_b g b) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g km _ L A regs mem md regs' mem'
        [(fsp g + 32, fsp g + 56); (b, b + gn g); ((symaddr Symbols.Plain.s_g_file), (symaddr Symbols.Plain.s_environ))] HF HP); [| | | exact MU' | exact WM' |].
      - rewrite (ss_getr_eqv _ _ _ Hx). exact (HKP 2 ltac:(ss_in)).
      - rewrite (ss_getr_eqv _ _ _ Hx). exact (HKP 3 ltac:(ss_in)).
      - rewrite (ss_getr_eqv _ _ _ Hx). exact (HKP 4 ltac:(ss_in)).
      - intros lo hi y Hin Hy. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
        + left. lia.
        + right. left. exists b, (gn g). split; [unfold hb_b; left; reflexivity | exact Hy].
        + right. right. split; [apply (proj2 (img_w_iff _)); right; left; lia|].
          intros (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin.
          repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    assert (E1 : getr regs' 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z)) by (rewrite (ss_getr_eqv _ _ _ Hx); exact H1).
    assert (E20 : getr regs' 20 = wz b) by (rewrite (ss_getr_eqv _ _ _ Hx); exact H20').
    assert (HIK : forall x, 0x10000 <= x < (symaddr ImgPages.Plain.top) -> ~ ((symaddr Symbols.Plain.s_g_file) <= x < (symaddr Symbols.Plain.s_environ)) ->
                  mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
    { intros x Hx1 Hx2. apply (ac_mb _ _ mem mem' x MU'); [lia|]. cbn [outside].
      destruct HBA as [E|E]; [|unfold img_apart in E]; repeat split; lia. }
    pose proof (ac_rw_back mem' m0 _ _ Hrel HPS) as HPS'.
    pose proof (ac_rw_back mem' m0 _ _ Hrel HGF) as HGF'.
    pose proof (ss_cells_bytes mem' _ _ HGF') as HGB. cbn [cells_bytes cbytes] in HGB. rewrite app_nil_r in HGB.
    apply bytes_at_app in HGB. destruct HGB as [Hq0' Hq8'].
    rewrite length_le8 in Hq8'. replace ((symaddr Symbols.Plain.s_g_file_len) + Z.of_nat 8) with (symaddr Symbols.Plain.s_g_file) in Hq8' by lia.
    assert (HBF' : bytes_at rsegs mem' b (gF g)).
    { destruct (Z.eq_dec (gn g) 0) as [E|E].
      - unfold gn in E. split; [lia|]. split; [lia|]. intros i Hi. lia.
      - exact (ss_rw_bytes mem' b _ _ (ac_rw_back mem' m0 _ _ Hrel (HBF E))). }
    assert (HOFL' : ofl_empty mem').
    { apply (ac_ofl mem mem' 0 HOFL). intros x Hx'. apply HIK; unfold A_OFL_HEAD in *; lia. }
    assert (HSTD' : stdio_ok mem').
    { apply (ac_stdio mem mem' HSTD). intros x Hx1 Hx2. apply HIK; lia. }
    assert (HERR' : err_ok mem').
    { apply (ac_err mem mem' HERR). intros x Hx'. apply HIK; unfold A_STDERR in *; lia. }
    change (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open)) with (Z_to_bv 64 PCAP_SOURCE_OPEN).
    apply (ps_open_step (fx:=fx') B APIf ra empty FF (HOPEN fx') g km (hb_b g b) L A regs' mem' md
      (fsp g + 32) (wz A5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5a5a5) (wz 0xa5a5) [a5b; a5b] b (gF g)
      (oOUT g) (Post_o B APIf ra g) HF' HP).
    + rewrite E1. apply ret_ok_even. rewrite MState.unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10'.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H11'.
    + lia.
    + lia.
    + exact Hp8.
    + exact HPS'.
    + apply bytes_at_app. split; [exact Hq0'|]. rewrite length_le8.
      replace (G_FILE_LEN + Z.of_nat 8) with (symaddr Symbols.Plain.s_g_file) by (unfold G_FILE_LEN; lia). exact Hq8'.
    + unfold gn in Hgnle. lia.
    + intros _. unfold hb_b. left. reflexivity.
    + exact HBF'.
    + exact HSTD'.
    + exact HOFL'.
    + apply resb_room_w; [exact Hroom | unfold hb_b; cbn [length]; lia | | lia].
      unfold hb_bytes, hb_b. cbn [map fold_right snd]. lia.
    + intros L' A' regs2 mem2 md2 h HGOOD HBAD HRP2 _ _ HIMG HSTD2 HGRD2 HBF2.
      assert (HERR2 : err_ok mem2).
      { apply (ac_err mem' mem2 HERR'). intros x Hx'. apply HIMG.
        - apply img_w_iff. left. exact Hx'.
        - unfold A_STDERR, A_OFL_HEAD in *. lia. }
      assert (Hq02 : q64 mem2 (symaddr Symbols.Plain.s_g_file_len) (gn g)).
      { unfold q64. apply (ac_gfile mem' mem2); [lia | rewrite length_le8; lia | exact Hq0' |].
        intros x Hx'. apply HIMG; [apply img_w_iff; right; left; exact Hx' | unfold A_OFL_HEAD; lia]. }
      rewrite E1.
      destruct (pcap_good (gF g)) eqn:EG.
      * destruct (HGOOD eq_refl) as (HF2 & HP2 & HA0 & _ & _ & HPS2 & HMS2 & HOFL2).
        apply HG. exists b, h, (km + 1).
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) (km + 1) (hb_bh g b h) (P_K2g g b h) L' A' regs2 mem2 md2
          Hfrm HF2 HP2).
        split; [exact HA0|].
        split; [ac_keep regs' regs 8 HRP2 Hx HKP H8|].
        split; [transitivity (getr regs' (Z_to_bv 5 20));
                [exact (HRP2 20 ltac:(unfold callee_saved; lia)) | exact E20]|].
        split; [ac_keep regs' regs 22 HRP2 Hx HKP H22|].
        split; [exact EG|].
        split; [split; [exact HSTD2|]; split; [exact HGRD2 | exact HERR2]|].
        split; [exact Hq02|].
        split.
        { unfold q64. apply (ac_gfile mem' mem2); [lia | rewrite length_le8; lia | exact Hq8' |].
          intros x Hx'. apply HIMG; [apply img_w_iff; right; left; exact Hx' | unfold A_OFL_HEAD; lia]. }
        split; [exists [a5b; a5b]; exact HPS2|].
        split; [exact HMS2 | exact HOFL2].
      * destruct (HBAD eq_refl) as (HF2 & HP2 & HA0 & HPS2 & HOFL2).
        apply HR. exists b, km.
        apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) km (hb_b g b) (P_K2r g b) L' A' regs2 mem2 md2
          Hfrm HF2 HP2).
        split; [exact HA0|].
        split; [ac_keep regs' regs 8 HRP2 Hx HKP H8|].
        split; [transitivity (getr regs' (Z_to_bv 5 20));
                [exact (HRP2 20 ltac:(unfold callee_saved; lia)) | exact E20]|].
        split; [ac_keep regs' regs 22 HRP2 Hx HKP H22|].
        split; [exact EG|].
        split; [split; [exact HSTD2|]; split; [exact HGRD2 | exact HERR2]|].
        split; [exact HOFL2|].
        split; [exact Hq02|].
        split; [exact HBF2|].
        exists (wz 0xa5a5a5a5), (wz 0), (wz 0), (wz 0), [a5b; a5b]. exact HPS2.
Qed.

Lemma seg_C : Hcut_o B APIf ra (Inv_KD B APIf ra empty) oKD ->
  Hcut_o B APIf ra (Inv_K3 B APIf ra empty) oOUT.
Proof.
  intros HD g c (b & h & buf & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z) km (hb_bhu g b h buf) (P_K3 g b h buf) c (oOUT g) (Post_o B APIf ra g)
    HC).
  intros fx' L A regs mem md Hfrm HF HP
    (H10 & Hbuf0 & H8 & H9 & H20 & H22 & HGOOD & (HSTD & HGRD & (fl & mdv & HE)) & Hq0 & Hq8 & (pad & HPS) &
     HMS & HOO).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _).
  pose proof HGV as (Hgn & _).
  pose proof (ss_stk_fsp B APIf ra empty g km _ L A regs mem md HF) as (_ & HIL & H8192 & HfS & HSc & HS47 & HK & Hsp).
  pose proof (ss_fr_bnd B APIf ra empty FF g km _ L A regs mem md HF) as (_ & Hf16 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as HAC.
  pose proof (ac_gn g) as Hgnle. pose proof (gcap_range g) as (Hcap & Hbn). pose proof (gd_range g) as Hd.
  unfold IMG_HI in HIL.
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md b (gn g) HF HP
    ltac:(unfold hb_bhu; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md h 1304 HF HP
    ltac:(unfold hb_bhu; right; left; reflexivity)) as (_ & Hh1 & Hh2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md buf (gbn g) HF HP
    ltac:(unfold hb_bhu; right; right; left; reflexivity)) as (_ & Hu1 & Hu2 & _).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  assert (HMIr : MemNorm.ro_agree rsegs mem) by (unfold MI in HMI; rewrite SEG in HMI; exact HMI).
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite Hsp; apply MState.unsigned_lit; lia).
  assert (Hp8 : (fsp g + 32) mod 8 = 0) by (clear - Hf16; Z.div_mod_to_equations; lia).
  assert (Ht8 : (fsp g + 24) mod 8 = 0) by (clear - Hf16; Z.div_mod_to_equations; lia).
  assert (Hh0 : h <> 0) by lia.
  assert (EO : oOUT g = psn_out h (gswz g =? 1) (gF g) (gcap g) 24 ++ oKD g).
  { unfold oOUT, psn_out. rewrite (proj2 (Z.eqb_neq h 0) Hh0). exact (OUT_good g ltac:(lia) HGOOD). }
  rewrite EO.
  apply (ss_kA_run_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z) /\ getr R 10 = wz (fsp g + 32) /\ getr R 11 = wz buf /\
       getr R 12 = wz (8 * gd g) /\ getr R 13 = wz (fsp g + 24) /\ getr R 18 = wz buf /\
       KP [2; 3; 4; 9; 20; 22] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next) /\
       munch [(fsp g + 8, fsp g + 16); (fsp g + 24, fsp g + 32)] (MemNorm.normalize rsegs mem) m' /\
       wmono rsegs (MemNorm.normalize rsegs mem) m' /\
       rw_cells rsegs m' (fsp g + 8) [C8 (wz (gd g))] /\ rw_cells rsegs m' (fsp g + 24) [C8 (wz (-1))])
    (psn_out h (gswz g =? 1) (gF g) (gcap g) 24 ++ oKD g) (Post_o B APIf ra g) Hh Hl HMI).
  - rewrite ss_mkR_of. eapply evt_mono.
    + apply (pcap_C_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (MemNorm.normalize rsegs mem) (fsp g) buf (gd g) (g_S g - SLOT_K) USP H10 ltac:(lia) H8 H9 Hd
        ltac:(rewrite HfS; exact (ss_fr_stk B APIf ra empty FF g km _ L A regs mem md HF)) ltac:(lia)
        (MemNorm.mem_inv_normalize rsegs mem)).
    + intros ms' (m' & -> & MU & WM & _ & _ & H8c & H24c).
      do 3 eexists. split; [reflexivity|]. cbv beta.
      do 6 (split; [reflexivity|]).
      split; [intros k Hk; cbn [In] in Hk; destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity|].
      split; [reflexivity|]. exact (conj MU (conj WM (conj H8c H24c))).
  - intros R pc' m0 regs' mem' (H1 & H10' & H11' & H12' & H13' & H18' & HKP & -> & MU & WM & H8c & H24c)
      Hx Hrel Hsame.
    pose proof (MemNorm.mem_rel_normalize rsegs mem HMIr) as HR0.
    pose proof (MemNorm.munch_rel rsegs _ mem (MemNorm.normalize rsegs mem) mem' m0 HR0 Hrel Hsame MU) as MU'.
    pose proof (MemNorm.wmono_rel rsegs mem (MemNorm.normalize rsegs mem) mem' m0 HR0 Hrel Hsame WM) as WM'.
    assert (HF' : FR B APIf ra empty g km (hb_bhu g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g km _ L A regs mem md regs' mem'
        [(fsp g + 8, fsp g + 16); (fsp g + 24, fsp g + 32)] HF HP); [| | | exact MU' | exact WM' |].
      - rewrite (ss_getr_eqv _ _ _ Hx). exact (HKP 2 ltac:(ss_in)).
      - rewrite (ss_getr_eqv _ _ _ Hx). exact (HKP 3 ltac:(ss_in)).
      - rewrite (ss_getr_eqv _ _ _ Hx). exact (HKP 4 ltac:(ss_in)).
      - intros lo hi y Hin Hy. cbn [In] in Hin.
        destruct Hin as [E|[E|[]]]; injection E as <- <-; left; lia. }
    assert (E1 : getr regs' 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z)) by (rewrite (ss_getr_eqv _ _ _ Hx); exact H1).
    assert (HIK : forall x, 0 <= x < fsp g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
    { intros x Hx'. apply (ac_mb _ _ mem mem' x MU'); [lia|]. cbn [outside]. repeat split; lia. }
    assert (HPS' : rw_cells rsegs mem' (fsp g + 32) (ps_cells (wz h) (wz (gswz g)) (wz 0) (wz 0) (wz 0) pad)).
    { apply (rw_cells_transport rsegs _ mem mem' _ _ HPS MU' WM').
      change (Z.of_nat (cells_size (ps_cells (wz h) (wz (gswz g)) (wz 0) (wz 0) (wz 0) pad))) with 24.
      cbn [disjoint_from]. repeat split; lia. }
    assert (HMS' : mstl mem' h b (gF g) 24 (wz 0) (wz 0)).
    { apply (pcap_source_next_lib.mstl_transport _ mem mem' h b (gF g) 24 (wz 0) (wz 0) HMS MU' WM');
        cbn [disjoint_from]; unfold gn in *; repeat split; lia. }
    assert (HOO' : ofl_one mem' h).
    { apply (ac_ofl mem mem' h HOO). intros x Hx'. apply HIK. unfold A_OFL_HEAD in *. lia. }
    assert (HSTD' : stdio_ok mem').
    { apply (ac_stdio mem mem' HSTD). intros x Hx1 Hx2. apply HIK. lia. }
    assert (HE' : errf mem' fl mdv).
    { apply (errf_keep B APIf ra empty FF mem mem' fl mdv HE). intros i Hi. apply HIK. unfold A_STDERR. lia. }
    assert (Hq0' : q64 mem' (symaddr Symbols.Plain.s_g_file_len) (gn g)).
    { unfold q64. apply (ac_by mem mem' _ _ Hq0). intros i Hi. rewrite length_le8 in Hi. apply HIK. lia. }
    assert (Hq8' : q64 mem' (symaddr Symbols.Plain.s_g_file) b).
    { unfold q64. apply (ac_by mem mem' _ _ Hq8). intros i Hi. rewrite length_le8 in Hi. apply HIK. lia. }
    pose proof (ac_rw_back mem' m0 _ _ Hrel H8c) as H8c'.
    pose proof (ac_rw_back mem' m0 _ _ Hrel H24c) as H24c'.
    destruct (ac_u8arr g km _ L A regs' mem' md buf (gbn g) HF' HP
      ltac:(unfold hb_bhu; right; right; left; reflexivity) ltac:(lia)) as (bj & HBJ & HBN).
    change (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next)) with (Z_to_bv 64 PCAP_SOURCE_NEXT).
    eapply (ps_next_step (fx:=fx') B APIf ra empty FF (HNEXT fx') g km (hb_bhu g b h buf) [(b, gn g); (h, 1304)]
      L A regs' mem' md (fsp g + 32) buf (gcap g) (fsp g + 24) h (gswz g) b 24 fl mdv (wz 0) (wz 0) (wz 0) (wz 0)
      (wz 0) (wz (-1)) pad bj (gF g) (oKD g) (Post_o B APIf ra g) HF' HP Hfrm).
    + rewrite E1. apply ret_ok_even. rewrite MState.unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10'.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H11'.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H12'.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H13'.
    + lia.
    + lia.
    + exact Hp8.
    + exact HPS'.
    + exact (Permutation_sym (Permutation_cons_append [(b, gn g); (h, 1304)] (buf, Z.max (gcap g) 1))).
    + exact HBJ.
    + exact HBN.
    + lia.
    + intros _. split; [lia|]. split; [lia|]. split; [exact Ht8|]. split; [left; lia|]. exact H24c'.
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|]. split; [exact HMS'|].
      split; [exact (gswz_01 g)|]. unfold gn in Hgnle. lia.
    + exact HE'.
    + intros regs2 mem2 Ft fc' mdv' Hfc _ HF2 HRP2 HFR2 _ HIMG HSTD2 HE2 HGRD2 _ HPO.
      rewrite E1. apply HD. exists b, h, buf, km.
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z) km (hb_bhu g b h buf) (P_KD g b h buf)
        L A regs2 mem2 md Hfc HF2 HP).
      split; [ac_keep regs' regs 9 HRP2 Hx HKP H9|].
      split; [transitivity (getr regs' (Z_to_bv 5 18)); [exact (HRP2 18 ltac:(unfold callee_saved; lia))|];
              rewrite (ss_getr_eqv _ _ _ Hx); exact H18'|].
      split; [ac_keep regs' regs 20 HRP2 Hx HKP H20|].
      split; [ac_keep regs' regs 22 HRP2 Hx HKP H22|].
      split; [exact HGOOD|].
      split; [split; [exact (HSTD2 HSTD')|]; split; [exact HGRD2 | exists fl, mdv'; exact HE2]|].
      split.
      { unfold q64. apply (ac_gfile mem' mem2); [lia | rewrite length_le8; lia | exact Hq0' |].
        intros x Hx'. apply HIMG; [apply img_w_iff; right; left; exact Hx' | unfold A_STDERR; lia]. }
      split.
      { unfold q64. apply (ac_gfile mem' mem2); [lia | rewrite length_le8; lia | exact Hq8' |].
        intros x Hx'. apply HIMG; [apply img_w_iff; right; left; exact Hx' | unfold A_STDERR; lia]. }
      split.
      { pose proof (ss_cells_bytes mem' _ _ H8c') as HB8. cbn [cells_bytes cbytes] in HB8.
        rewrite app_nil_r in HB8. unfold q64. apply (ac_by mem' mem2 _ _ HB8). intros i Hi.
        rewrite length_le8 in Hi. apply HFR2; lia. }
      split.
      { apply (ac_ofl mem' mem2 h HOO'). intros x Hx'. apply HIMG.
        - apply img_w_iff. right. right. exact Hx'.
        - unfold A_STDERR, A_OFL_HEAD in *. lia. }
      exists (wz 0), (wz 0), (wz 0), (wz (-1)), pad, bj. split; [exact HBN | exact (HPO Hh0)].
Qed.

End AC.
