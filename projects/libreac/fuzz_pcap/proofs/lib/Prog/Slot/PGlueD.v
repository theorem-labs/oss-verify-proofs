From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge Cells Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct
  pcap_source_struct_next pcap_source_next_c pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PWalkDef PWalk PSegL PCut.
Import ListNotations.
Open Scope Z_scope.

(* The glue of the segments without a callee step: seg_D (KD to K4 0 24 or K5 24) and seg_L2 (KL2 to K4 or K5). *)

Lemma gd_le8_surj : forall bs : list byte, length bs = 8%nat -> exists v : word, bs = le8 v.
Proof.
  intros bs Hl. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  rewrite <- store_bytes_8. change (width_bytes 64) with 8%nat.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as Hr. rewrite length_map, Hl in Hr.
  change (256 ^ Z.of_nat 8) with (2^64) in Hr.
  rewrite Z_to_bv_unsigned, bv_wrap_small.
  2:{ rewrite bytes_le_to_Z_le_val. change (bv_modulus 64) with (2^64). lia. }
  rewrite <- Hl. symmetry. apply Z_to_le_bytes_to_Z.
Qed.

(* Any 8 stack bytes form a writable 8-byte cell. *)
Lemma gd_c8_of_stk : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists v, rw_cells rsegs m a [C8 v].
Proof.
  intros m lo hi a ST H1 H2.
  destruct (ss_rw_of_stk m lo hi a 8 ST H1 ltac:(change (Z.of_nat 8) with 8; lia)) as (bs & [[Hwf Hb] Hw]).
  destruct Hwf as [Hl _]. destruct (gd_le8_surj bs Hl) as (v & ->). exists v.
  split; [split; [split; exact I | exact Hb] | exact Hw].
Qed.

Lemma gd_bytes_firstn : forall m a l k, bytes_at rsegs m a l -> bytes_at rsegs m a (firstn k l).
Proof.
  intros m a l k H. rewrite <- (firstn_skipn k l) in H. exact (proj1 (proj1 (bytes_at_app rsegs m a _ _) H)).
Qed.

Lemma gd_cells_rel : forall m m0 a cs, MemNorm.mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (MemNorm.wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

Lemma gd_disj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros a n a' n' H H1 H2; cbn in *; [exact I|].
  destruct H as [H3 H4]. split; [lia | exact (IH a n a' n' H4 H1 H2)].
Qed.

(* The stdio facts lie in the image (0x10000 .. 0x50000). *)
Lemma gd_sb_xfer : forall W m m', munch W m m' -> wmono rsegs m m' -> disjoint_from W 0x10000 (symaddr (ImgPages.Plain.top - ImgPages.Plain.ro_lo)%Z) ->
  sb_ok m -> sb_ok m'.
Proof.
  intros W m m' MU WM D ((S1 & S2 & S3) & (G1 & gv & G2) & (fl & md & E1 & E2)).
  split; [|split].
  - split; [|split].
    + eapply (bytes_at_transport rsegs); [exact S1 | exact MU |].
      apply (gd_disj_sub W _ _ _ _ D); cbn [length]; cbv [A_LIBC]; lia.
    + eapply (bytes_at_transport rsegs); [exact S2 | exact MU |].
      apply (gd_disj_sub W _ _ _ _ D); cbn [length]; cbv [A_LIBC]; lia.
    + eapply (bytes_at_transport rsegs); [exact S3 | exact MU |].
      apply (gd_disj_sub W _ _ _ _ D); rewrite ?length_le4; cbv [A_OFL_LOCK]; lia.
  - split.
    + eapply (bytes_at_transport rsegs); [exact G1 | exact MU |].
      apply (gd_disj_sub W _ _ _ _ D); rewrite ?length_le8; cbv [A_GOT_GUARD]; lia.
    + exists gv. eapply (bytes_at_transport rsegs); [exact G2 | exact MU |].
      apply (gd_disj_sub W _ _ _ _ D); rewrite ?length_le8; cbv [A_GUARD]; lia.
  - exists fl, md. split; [|exact E2].
    eapply (rw_cells_transport rsegs); [exact E1 | exact MU | exact WM |].
    apply (gd_disj_sub W _ _ _ _ D);
      [cbv [A_STDERR]; lia | change (Z.of_nat (cells_size (stderr_cells fl md))) with 232; cbv [A_STDERR]; lia].
Qed.

(* The facts of the loop's cuts outside the slot's frame cells and the record buffer. *)
Lemma gd_xfer : forall g W mem mem' b h q pv nx,
  munch W mem mem' -> wmono rsegs mem mem' ->
  disjoint_from W 0x10000 (symaddr (ImgPages.Plain.top - ImgPages.Plain.ro_lo)%Z) -> disjoint_from W h 1304 -> disjoint_from W b (gn g) ->
  disjoint_from W (fsp g + 8) 8 ->
  sb_ok mem -> q64 mem (symaddr Symbols.Plain.s_g_file_len) (gn g) -> q64 mem (symaddr Symbols.Plain.s_g_file) b -> q64 mem (fsp g + 8) (gd g) -> ofl_one mem h ->
  mstl mem h b (gF g) q pv nx ->
  sb_ok mem' /\ q64 mem' (symaddr Symbols.Plain.s_g_file_len) (gn g) /\ q64 mem' (symaddr Symbols.Plain.s_g_file) b /\ q64 mem' (fsp g + 8) (gd g) /\ ofl_one mem' h /\
  mstl mem' h b (gF g) q pv nx.
Proof.
  intros g W mem mem' b h q pv nx MU WM D0 Dh Db D8 Hsb H0 H8 Hd Ho Hm.
  split; [exact (gd_sb_xfer W mem mem' MU WM D0 Hsb)|].
  split.
  { eapply (bytes_at_transport rsegs); [exact H0 | exact MU |].
    apply (gd_disj_sub W _ _ _ _ D0); rewrite ?length_le8; lia. }
  split.
  { eapply (bytes_at_transport rsegs); [exact H8 | exact MU |].
    apply (gd_disj_sub W _ _ _ _ D0); rewrite ?length_le8; lia. }
  split.
  { eapply (bytes_at_transport rsegs); [exact Hd | exact MU |]. rewrite length_le8. exact D8. }
  split.
  { eapply (rw_cells_transport rsegs); [exact Ho | exact MU | exact WM |].
    apply (gd_disj_sub W _ _ _ _ D0); cbn [cells_size csize Nat.add]; cbv [A_OFL_HEAD]; lia. }
  exact (mstl_transport W mem mem' h b (gF g) q pv nx Hm MU WM Dh Db).
Qed.

Lemma gd_good_len : forall F, pcap_good F = true -> 24 <= Z.of_nat (length F).
Proof. intros F H. unfold pcap_good in H. apply andb_prop in H as [H _]. apply Z.leb_le in H. exact H. Qed.

Lemma gd_res_range : forall sw F cap q, 0 <= cap -> -1 <= res_of sw F cap q <= cap.
Proof.
  intros sw F cap q Hc. unfold res_of. destruct (kind sw F cap q) eqn:K; try lia.
  destruct (kind_fit sw F cap q K) as (_ & R & _). lia.
Qed.

Lemma gd_fit_of_pos : forall sw F cap q, 0 < res_of sw F cap q -> kind sw F cap q = KFit.
Proof. intros sw F cap q. unfold res_of. destruct (kind sw F cap q); intros H; first [reflexivity | lia]. Qed.

Lemma gd_nfit_of_npos : forall sw F cap q, res_of sw F cap q <= 0 -> kind sw F cap q <> KFit.
Proof. intros sw F cap q H K. destruct (kind_fit sw F cap q K) as (E & R & _). lia. Qed.

Lemma gd_is_fit_false : forall k, k <> KFit -> is_fit k = false.
Proof. intros k H. destruct k; try reflexivity. exfalso. apply H. reflexivity. Qed.

Section Run.
Context {fx : YK11.FPState}.

(* Segment D in the form of ss_kA_run_o. *)
Lemma gd_D_run : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (lo sp_h n0 buf : Z) (v16 : word),
  bv_unsigned x2 = sp_h -> x10 = wz n0 -> -1 <= n0 < 2 ^ 26 -> x18 = wz buf ->
  rw_cells rsegs m (sp_h + 16) [C8 v16] -> mem_inv rsegs m -> stk rsegs m lo (sp_h + 160) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       ((0 < n0 /\
         (exists a0' : word, R = Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0' (wz 0) (wz n0) x13 x14 x15 x16 x17 x18
            (wz n0) x20 (wz 0xff00) x22 x23 (wz 24) (wz 0) x26 (wz (1000000 * 2 ^ 32)) x28 x29 x30 x31) /\
         pc' = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z) /\ munch [(sp_h + 16, sp_h + 24)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (sp_h + 16) [C8 (wz (buf + 12))]) \/
        (n0 <= 0 /\
         R = Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 (wz n0) x13 x14 x15 x16 x17 x18 (wz n0) x20 x21 x22 x23
           (wz 24) x25 x26 x27 x28 x29 x30 x31 /\
         pc' = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z) /\ m' = m)))
    (MS (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
           x27 x28 x29 x30 x31) fp_regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z)) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m lo sp_h n0 buf v16 HSP E0 Hn E2 H16 MI ST.
  eapply Exec.evt_mono; [eapply pcap_D_x; eassumption|].
  intros ms [[P QD]|[P E]].
  - destruct QD as (a0' & s5' & s11' & m' & E & -> & -> & MU & WM & _ & _ & H16').
    subst ms. do 3 eexists. split; [reflexivity|]. left. split; [exact P|].
    split; [exists a0'; reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact H16'].
  - subst ms. do 3 eexists. split; [reflexivity|]. right. split; [exact P|]. split; [reflexivity|].
    split; reflexivity.
Qed.

(* Segment L2 in the form of ss_kA_run0_o. *)
Lemma gd_L2_run : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
    x25 x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (n : Z),
  x10 = wz n -> -1 <= n < 2 ^ 26 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       R = Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x19 (wz n) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
             x25 x26 x27 x28 x29 x30 x31 /\ m' = m /\
       ((0 < n /\ pc' = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x1c8)%Z)) \/ (n <= 0 /\ pc' = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z))))
    (MS (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
           x27 x28 x29 x30 x31) fp_regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z)) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m n E0 Hn.
  eapply Exec.evt_mono; [eapply pcap_L2_x; eassumption|].
  intros ms [[P E]|[P E]]; subst ms; do 3 eexists; (split; [reflexivity|]); (split; [reflexivity|]);
    (split; [reflexivity|]).
  - left. split; [exact P | reflexivity].
  - right. split; [exact P | reflexivity].
Qed.

End Run.

Section GlueD.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

(* The heap blocks of the loop's cuts lie below the slot's stack. *)
Lemma gd_heap_low {fx : YK11.FPState} : forall g km b h buf L A regs mem md,
  FR B APIf ra empty g km (hb_bhu g b h buf) L A regs mem md ->
  Permutation (blocks L A) (hb_bhu g b h buf ++ blocks (g_L g) (g_A g)) -> 24 <= gn g ->
  h + 1304 <= fsp g /\ b + gn g <= fsp g /\ buf + gbn g <= fsp g.
Proof.
  intros g km b h buf L A regs mem md HF HP Hn.
  pose proof (gcap_range g) as [_ Hbn].
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & _ & _ & HfS & _ & _ & HSK & _).
  assert (I1 : in_hb (hb_bhu g b h buf) (h + 1303)).
  { exists h, 1304. split; [unfold hb_bhu; cbn [In]; right; left; reflexivity | lia]. }
  assert (I2 : in_hb (hb_bhu g b h buf) (b + gn g - 1)).
  { exists b, (gn g). split; [unfold hb_bhu; cbn [In]; left; reflexivity | lia]. }
  assert (I3 : in_hb (hb_bhu g b h buf) (buf + gbn g - 1)).
  { exists buf, (gbn g). split; [unfold hb_bhu; cbn [In]; right; right; left; reflexivity | lia]. }
  destruct (ss_hb_low B APIf ra empty FF g _ _ L A regs mem md _ HF HP I1) as (_ & X1).
  destruct (ss_hb_low B APIf ra empty FF g _ _ L A regs mem md _ HF HP I2) as (_ & X2).
  destruct (ss_hb_low B APIf ra empty FF g _ _ L A regs mem md _ HF HP I3) as (_ & X3).
  lia.
Qed.

Lemma seg_L2 : forall i p, 0 <= i ->
  Hcut_o B APIf ra (Inv_K4 B APIf ra empty (i + 1) p) (oK4 p) ->
  Hcut_o B APIf ra (Inv_K5 B APIf ra empty p) out24 ->
  Hcut_o B APIf ra (Inv_KL2 B APIf ra empty (i + 1) p) (oKL2 p).
Proof.
  intros i p Hi H4 H5 g c (b & h & buf & km & HC).
  eapply (cut_open B APIf ra empty); [exact HC|]. clear HC.
  intros fx' L A regs mem md Hfrm HF HP HPr.
  destruct HPr as (E9 & E18 & E19 & E20 & E21 & E22 & E24 & E25 & E27 & Hjp & Hpn & Hgood & Hsb & Hq0 & Hq8 & Hqd
    & Hofl & H16 & lol & lvt & lvid & tsv & pad & bj & Hbj & H10 & Hmstl & Hps & Hbuf & Hts).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & HIH & H8k & _ & _ & _ & _ & _).
  unfold IMG_HI in HIH.
  pose proof (gcap_range g) as [Hcap Hbn].
  pose proof (gd_res_range (gsw g) (gF g) (gcap g) (gq g p) ltac:(lia)) as Hres.
  rewrite (oKL2_split p g).
  eapply (ss_kA_run0_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x440)%Z)) mem md); [exact Hh | exact Hl | |].
  { rewrite ss_mkR_of. eapply gd_L2_run with (n := res_of (gsw g) (gF g) (gcap g) (gq g p)); [exact H10 | lia]. }
  intros R pc' m' regs1 (ER & Em & Hpc) XR. subst R m'.
  assert (KP1 : KP [2; 3; 4; 9; 18; 19; 20; 21; 22; 24; 25; 27] regs regs1) by ss_kp XR regs.
  assert (HF1 : FR B APIf ra empty g km (hb_bhu g b h buf) L A regs1 mem md).
  { apply (ss_FR_hb B APIf ra empty FF g _ _ L A regs mem md regs1 mem HF HP).
    - intros k Hk. apply KP1. cbn [In] in Hk |- *. tauto.
    - intros x _ _. reflexivity.
    - apply ss_wmono_eq. intros w. reflexivity. }
  destruct Hpc as [[Pn ->] | [Pn ->]].
  - (* a fit record: K4 (i + 1) p *)
    pose proof (gd_fit_of_pos _ _ _ _ Pn) as KF.
    pose proof (kind_fit (gsw g) (gF g) (gcap g) (gq g p) KF) as (Rres & _).
    rewrite KF. cbn [is_fit].
    apply H4. exists b, h, buf, km.
    eapply (cut_close B APIf ra empty fx'); [exact Hfrm | exact HF1 | exact HP |].
    rewrite (lol_of_fit (gsw g) (gF g) (gcap g) p lol ltac:(lia) KF),
      (vt_of_fit (gsw g) (gF g) (gcap g) (psn_q (gsw g) (gF g) (gcap g) p) lvt KF),
      (vid_of_fit (gsw g) (gF g) (gcap g) (psn_q (gsw g) (gF g) (gcap g) p) lvid KF) in Hps.
    rewrite (ts_of_fit (gsw g) (gF g) (gcap g) (psn_q (gsw g) (gF g) (gcap g) p) tsv KF) in Hts.
    destruct Hbuf as (bj' & [HUb _] & _ & HFP).
    unfold P_K4.
    split; [ss_k KP1 9; exact E9|]. split; [ss_k KP1 18; exact E18|]. split; [ss_k KP1 20; exact E20|].
    split; [ss_k KP1 21; exact E21|]. split; [ss_k KP1 22; exact E22|]. split; [ss_k KP1 24; exact E24|].
    split; [ss_k KP1 25; exact E25|]. split; [ss_k KP1 27; exact E27|].
    split; [lia|]. split; [exact Hjp|]. split; [exact KF|].
    split; [rewrite (ss_getr_x _ _ 12 XR) by reflexivity; rewrite <- Rres; reflexivity|].
    split; [right; split; [lia|]; rewrite (ss_getr_x _ _ 11 XR) by reflexivity; exact E19|].
    split; [exact Hgood|]. split; [exact Hsb|]. split; [exact Hq0|]. split; [exact Hq8|]. split; [exact Hqd|].
    split; [exact Hofl|]. split; [exact Hmstl|].
    split; [exists pad; exact Hps|]. split; [exact H16|]. split; [exact (Hts ltac:(lia))|].
    pose proof (HFP (f_equal is_fit KF)) as EB. unfold gq. rewrite <- EB. apply gd_bytes_firstn. exact HUb.
  - (* no fit record: K5 p *)
    pose proof (gd_nfit_of_npos _ _ _ _ Pn) as KN.
    rewrite (gd_is_fit_false _ KN). cbn [is_fit].
    apply H5. exists b, h, buf, km.
    eapply (cut_close B APIf ra empty fx'); [exact Hfrm | exact HF1 | exact HP |].
    unfold P_K5.
    split; [rewrite (ss_getr_x _ _ 12 XR) by reflexivity; reflexivity|]. split; [exact KN|].
    split; [ss_k KP1 24; exact E24|]. split; [lia|]. split; [exact Hpn|].
    split; [ss_k KP1 9; exact E9|]. split; [ss_k KP1 18; exact E18|]. split; [ss_k KP1 19; exact E19|].
    split; [ss_k KP1 20; exact E20|]. split; [ss_k KP1 22; exact E22|].
    split; [exact Hgood|]. split; [exact Hsb|]. split; [exact Hq0|]. split; [exact Hq8|]. split; [exact Hqd|].
    split; [exact Hofl|]. split; [exact Hmstl|].
    do 4 eexists. exact Hps.
Qed.

Lemma seg_D :
  Hcut_o B APIf ra (Inv_K4 B APIf ra empty 0 24) (oK4 24) ->
  Hcut_o B APIf ra (Inv_K5 B APIf ra empty 24) out24 ->
  Hcut_o B APIf ra (Inv_KD B APIf ra empty) oKD.
Proof.
  intros H4 H5 g c (b & h & buf & km & HC).
  eapply (cut_open B APIf ra empty); [exact HC|]. clear HC.
  intros fx' L A regs mem md Hfrm HF HP HPr.
  destruct HPr as (E9 & E18 & E20 & E22 & Hgood & Hsb & Hq0 & Hq8 & Hqd & Hofl
    & lol & lvt & lvid & tsv & pad & bj & Hbj & H10 & Hmstl & Hps & Hbuf & Hts).
  pose proof (ss_segs B APIf ra empty FF) as SEG.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _).
  assert (HMIr : MemNorm.ro_agree rsegs mem) by (unfold MI in HMI; rewrite <- SEG; exact HMI).
  pose proof (MemNorm.mem_rel_normalize rsegs mem HMIr) as HR0.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty _ _ _ _ _ _ _ _ HF)) as [Hh Hl].
  pose proof (ss_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (_ & HIH & H8k & HfS & _ & HS47 & HSK & Hsp).
  unfold IMG_HI in HIH.
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as STn.
  pose proof (gcap_range g) as [Hcap Hbn].
  pose proof (gd_good_len (gF g) Hgood) as Hn24. change (Z.of_nat (length (gF g))) with (gn g) in Hn24.
  destruct (gd_heap_low g km b h buf L A regs mem md HF HP Hn24) as (BH & BB & BU).
  pose proof (gd_res_range (gsw g) (gF g) (gcap g) (gq g 24) ltac:(lia)) as Hres.
  destruct (gd_c8_of_stk (MemNorm.normalize rsegs mem) (g_S g - SLOT_K) (g_S g) (fsp g + 16) STn
              ltac:(lia) ltac:(lia)) as (v16 & H16).
  rewrite (oKD_eq g), (oKL2_split 24 g).
  eapply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x198)%Z)) mem md); [exact Hh | exact Hl | exact HMI | |].
  { rewrite ss_mkR_of.
    eapply gd_D_run with (sp_h := fsp g) (n0 := res_of (gsw g) (gF g) (gcap g) (gq g 24)) (buf := buf)
      (v16 := v16) (lo := g_S g - SLOT_K).
    - rewrite Hsp. apply unsigned_lit. lia.
    - exact H10.
    - lia.
    - exact E18.
    - exact H16.
    - apply MemNorm.mem_inv_normalize.
    - replace (fsp g + 160) with (g_S g) by lia. exact STn. }
  intros R pc' m' regs1 mem' HQ XR Hrel Hsame.
  set (W := [(fsp g + 16, fsp g + 24)]).
  assert (D0 : disjoint_from W 0x10000 (symaddr (ImgPages.Plain.top - ImgPages.Plain.ro_lo)%Z)) by (unfold W; cbn [disjoint_from]; split; [lia | exact I]).
  assert (Dh : disjoint_from W h 1304) by (unfold W; cbn [disjoint_from]; split; [lia | exact I]).
  assert (Db : disjoint_from W b (gn g)) by (unfold W; cbn [disjoint_from]; split; [lia | exact I]).
  assert (D8 : disjoint_from W (fsp g + 8) 8) by (unfold W; cbn [disjoint_from]; split; [lia | exact I]).
  assert (HW : forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g (hb_bhu g b h buf) y).
  { intros lo hi y Hin Hy. unfold W in Hin. cbn [In] in Hin. destruct Hin as [E|[]]. injection E as <- <-.
    unfold kreg. left. lia. }
  (* the memory after D differs from mem at most in the cell 16(sp) *)
  assert (XF : forall m0, munch W (MemNorm.normalize rsegs mem) m0 -> wmono rsegs (MemNorm.normalize rsegs mem) m0 ->
            MemNorm.mem_rel rsegs mem' m0 -> munch W mem mem' /\ wmono rsegs mem mem').
  { intros m0 MU WM HR.
    split; [exact (MemNorm.munch_rel rsegs W mem _ mem' m0 HR0 HR Hsame MU)|].
    exact (MemNorm.wmono_rel rsegs mem _ mem' m0 HR0 HR Hsame WM). }
  destruct HQ as [(Pn & (a0' & ER) & Epc & MU & WM & H16') | (Pn & ER & Epc & Em)].
  - (* a fit record: K4 0 24 *)
    subst R pc'.
    destruct (XF m' MU WM Hrel) as [MUm WMm].
    assert (KP1 : KP [2; 3; 4; 9; 18; 20; 22] regs regs1) by ss_kp XR regs.
    assert (HF1 : FR B APIf ra empty g km (hb_bhu g b h buf) L A regs1 mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g km _ L A regs mem md regs1 mem' W HF HP
               (KP1 2 ltac:(ss_in)) (KP1 3 ltac:(ss_in)) (KP1 4 ltac:(ss_in)) MUm WMm HW). }
    pose proof (gd_fit_of_pos _ _ _ _ Pn) as KF.
    pose proof (kind_fit (gsw g) (gF g) (gcap g) (gq g 24) KF) as (Rres & _).
    rewrite KF. cbn [is_fit].
    apply H4. exists b, h, buf, km.
    eapply (cut_close B APIf ra empty fx'); [exact Hfrm | exact HF1 | exact HP |].
    destruct (gd_xfer g W mem mem' b h _ _ _ MUm WMm D0 Dh Db D8 Hsb Hq0 Hq8 Hqd Hofl Hmstl)
      as (Xsb & Xq0 & Xq8 & Xqd & Xofl & Xmstl).
    rewrite (lol_of_fit (gsw g) (gF g) (gcap g) 24 lol ltac:(lia) KF),
      (vt_of_fit (gsw g) (gF g) (gcap g) (psn_q (gsw g) (gF g) (gcap g) 24) lvt KF),
      (vid_of_fit (gsw g) (gF g) (gcap g) (psn_q (gsw g) (gF g) (gcap g) 24) lvid KF) in Hps.
    rewrite (ts_of_fit (gsw g) (gF g) (gcap g) (psn_q (gsw g) (gF g) (gcap g) 24) tsv KF) in Hts.
    destruct Hbuf as (bj' & [HUb _] & HLb & HFP).
    unfold P_K4.
    split; [ss_k KP1 9; exact E9|]. split; [ss_k KP1 18; exact E18|]. split; [ss_k KP1 20; exact E20|].
    split; [rewrite (ss_getr_x _ _ 21 XR) by reflexivity; reflexivity|].
    split; [ss_k KP1 22; exact E22|].
    split; [rewrite (ss_getr_x _ _ 24 XR) by reflexivity; reflexivity|].
    split; [rewrite (ss_getr_x _ _ 25 XR) by reflexivity; reflexivity|].
    split; [rewrite (ss_getr_x _ _ 27 XR) by reflexivity; reflexivity|].
    split; [lia|]. split; [lia|]. split; [exact KF|].
    split; [rewrite (ss_getr_x _ _ 12 XR) by reflexivity; rewrite <- Rres; reflexivity|].
    split; [left; split; [reflexivity | symmetry; exact Rres]|].
    split; [exact Hgood|]. split; [exact Xsb|]. split; [exact Xq0|]. split; [exact Xq8|]. split; [exact Xqd|].
    split; [exact Xofl|]. split; [exact Xmstl|].
    split.
    { exists pad. eapply (rw_cells_transport rsegs); [exact Hps | exact MUm | exact WMm |].
      unfold W. cbn [disjoint_from cells_size csize ps_cells Nat.add]. split; [lia | exact I]. }
    split; [exact (gd_cells_rel mem' m' _ _ Hrel H16')|].
    split.
    { eapply (rw_cells_transport rsegs); [exact (Hts ltac:(lia)) | exact MUm | exact WMm |].
      unfold W. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | exact I]. }
    pose proof (HFP (f_equal is_fit KF)) as EB. unfold gq. rewrite <- EB. apply gd_bytes_firstn.
    eapply (bytes_at_transport rsegs); [exact HUb | exact MUm |].
    unfold W. cbn [disjoint_from]. rewrite HLb, Hbj. split; [lia | exact I].
  - (* no fit record: K5 24 *)
    subst R pc' m'.
    destruct (XF _ (munch_refl W _) (wmono_refl rsegs _) Hrel) as [MUm WMm].
    assert (KP1 : KP [2; 3; 4; 9; 18; 20; 22] regs regs1) by ss_kp XR regs.
    assert (HF1 : FR B APIf ra empty g km (hb_bhu g b h buf) L A regs1 mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g km _ L A regs mem md regs1 mem' W HF HP
               (KP1 2 ltac:(ss_in)) (KP1 3 ltac:(ss_in)) (KP1 4 ltac:(ss_in)) MUm WMm HW). }
    pose proof (gd_nfit_of_npos _ _ _ _ Pn) as KN.
    rewrite (gd_is_fit_false _ KN). cbn [is_fit].
    apply H5. exists b, h, buf, km.
    eapply (cut_close B APIf ra empty fx'); [exact Hfrm | exact HF1 | exact HP |].
    destruct (gd_xfer g W mem mem' b h _ _ _ MUm WMm D0 Dh Db D8 Hsb Hq0 Hq8 Hqd Hofl Hmstl)
      as (Xsb & Xq0 & Xq8 & Xqd & Xofl & Xmstl).
    unfold P_K5.
    split; [rewrite (ss_getr_x _ _ 12 XR) by reflexivity; reflexivity|]. split; [exact KN|].
    split; [rewrite (ss_getr_x _ _ 24 XR) by reflexivity; reflexivity|]. split; [lia|]. split; [lia|].
    split; [ss_k KP1 9; exact E9|]. split; [ss_k KP1 18; exact E18|].
    split; [rewrite (ss_getr_x _ _ 19 XR) by reflexivity; reflexivity|].
    split; [ss_k KP1 20; exact E20|]. split; [ss_k KP1 22; exact E22|].
    split; [exact Hgood|]. split; [exact Xsb|]. split; [exact Xq0|]. split; [exact Xq8|]. split; [exact Xqd|].
    split; [exact Xofl|]. split; [exact Xmstl|].
    do 4 eexists. eapply (rw_cells_transport rsegs); [exact Hps | exact MUm | exact WMm |].
    unfold W. cbn [disjoint_from cells_size csize ps_cells Nat.add]. split; [lia | exact I].
Qed.

End GlueD.
