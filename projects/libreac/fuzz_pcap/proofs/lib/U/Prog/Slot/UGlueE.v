From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Cells
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel libreac_fuzz_fopen_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require mread.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PGlue PImg UCut USegR7 USegE
  UGlueT UGlueW.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USROcf PInvCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Glue of segment E of the ubsan slot: from the entry (Inv_ENTRY, payload below 2^26 bytes) through ubs_E_x to
   malloc(un g) (ra 0x12cf0), then Inv_K12d28. The frame record at the call is built by ss_fr_of: the entry memory
   differs only in the slot's frame and the 16 bytes at G_FILE_LEN (img_w, outside frame_RELRO). *)

(* The image holds a byte at each of the 16 bytes at G_FILE_LEN (g_file_len, g_file), so every memory reads them. *)
Definition ue_rom_chk (a : Z) (k : nat) : bool :=
  forallb (fun i => match mrd rsegs (fun _ => None) (Z_to_bv 64 (a + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 k).

Lemma ue_rom_gfile : ue_rom_chk (symaddr Symbols.Ubsan.s_g_file_len) 16 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ue_mrd_some : forall m a k j, ue_rom_chk a k = true -> (j < k)%nat ->
  exists b, mrd rsegs m (Z_to_bv 64 (a + Z.of_nat j)) = Some b.
Proof.
  intros m a k j H Hj. unfold ue_rom_chk in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)). unfold mrd in *. cbv beta iota in H.
  destruct (m (Z_to_bv 64 (a + Z.of_nat j))) as [b|]; [exists b; reflexivity|].
  destruct (PropExec.seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat j))) as [b|]; [exists b; reflexivity | discriminate H].
Qed.

(* The 16 bytes at G_FILE_LEN are writable and present in every memory. *)
Lemma ue_gfile_stk : forall m, stk rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (symaddr Symbols.Ubsan.s_environ).
Proof.
  intros m. split; [lia|]. split; [lia|]. intros a Ha. split.
  - exact (proj1 (img_w_wr m a ltac:(apply (proj2 (img_w_iff a)); right; left; lia))).
  - replace a with ((symaddr Symbols.Ubsan.s_g_file_len) + Z.of_nat (Z.to_nat (a - (symaddr Symbols.Ubsan.s_g_file_len)))) by lia.
    unfold wa. exact (ue_mrd_some m (symaddr Symbols.Ubsan.s_g_file_len) 16 (Z.to_nat (a - (symaddr Symbols.Ubsan.s_g_file_len))) ue_rom_gfile ltac:(lia)).
Qed.

Lemma ue_gfile_cells : forall m, exists v0 v1, rw_cells rsegs m (symaddr Symbols.Ubsan.s_g_file_len) [C8 v0; C8 v1].
Proof.
  intros m.
  destruct (c8_of_stk m (symaddr Symbols.Ubsan.s_g_file_len) (symaddr Symbols.Ubsan.s_environ) (symaddr Symbols.Ubsan.s_g_file_len) (ue_gfile_stk m) ltac:(lia) ltac:(lia)) as (v0 & H0).
  destruct (c8_of_stk m (symaddr Symbols.Ubsan.s_g_file_len) (symaddr Symbols.Ubsan.s_environ) (symaddr Symbols.Ubsan.s_g_file) (ue_gfile_stk m) ltac:(lia) ltac:(lia)) as (v1 & H1).
  exists v0, v1. exact (mread.rw_cells_app_r rsegs m (symaddr Symbols.Ubsan.s_g_file_len) [C8 v0] [C8 v1] H0 H1).
Qed.

(* The 16 bytes at G_FILE_LEN lie outside frame_RELRO. *)
Lemma ue_not_relro : forall a, (symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ) -> ~ in_globals frame_RELRO a.
Proof.
  intros a Ha (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Section E.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

(* Inv_ENTRY 0x12c4c (payload below 2^26 bytes): ubs_E_x, then malloc(un g) (ra 0x12cf0), then Inv_K12d28. *)
Lemma ug_E : Hcut_o B APIf ra (Inv_K12d28 B APIf ra empty) (fun g => PW.OUT (g_in g)) ->
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof.
  intros HX g c (fx' & -> & Hfrm & HGV & Hpre & HMI & Hres & HGI & Hfd).
  pose proof (sg_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HgR & HgSn & HgFs & HgFd).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (sg_GV_S B empty g HGV) as [Esp _].
  destruct (stdio_of_entry B APIf ra empty FF g HGV Hpre) as (HSTD0 & HOFL0 & HGRD0).
  destruct (errf_of_img B APIf ra empty FF 0%nat (g_mem g) HgR HGI) as (mdv & _ & HE0).
  destruct (sg_md B APIf (g_L g) (g_A g) (g_mem g) (g_md g) HM) as [Hh Hl].
  assert (HMI' : ro_agree rsegs (g_mem g)) by (unfold MI in HMI; rewrite SEGS in HMI; exact HMI).
  assert (Efsp : fsp g = g_S g - 176) by reflexivity.
  assert (EK : SLOT_K = 65536) by reflexivity.
  assert (Hun : 0 <= un g < 2 ^ 26) by (pose proof (un_le_n g); unfold un, zlen in *; lia).
  (* the payload block: its range and its bytes *)
  assert (Hrange : 0 < g_p g /\ g_p g + g_n g <= alloc_ceiling).
  { destruct Hnp as [[Hn0 Hpe] | [Hnpos Hin]].
    - rewrite Hpe, Hn0, EMP. lia.
    - destruct (ss_blk_facts (fx:=fx') B APIf ra empty FF _ _ _ _ _ _ 0 HM Hin ltac:(lia)) as (_ & H1 & H2 & _).
      lia. }
  assert (HBA : bytes_at rsegs (g_mem g) (g_p g) (g_in g)).
  { split; [lia|]. split; [unfold g_n in Hrange; lia|]. intros i Hi.
    pose proof (Hblk (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity. }
  pose proof (bytes_at_normalize rsegs (g_mem g) (g_p g) (g_in g) HMI' HBA) as HBN.
  assert (HSTK : stk rsegs (normalize rsegs (g_mem g)) (g_S g - SLOT_K) (fsp g + 176)).
  { rewrite Efsp. replace (g_S g - 176 + 176) with (g_S g) by lia.
    apply ss_stk_norm; [exact HMI' | unfold SS_TOP; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha. }
  destruct (c8_of_stk _ _ _ (fsp g) HSTK ltac:(lia) ltac:(lia)) as (vc & HC0).
  destruct (ue_gfile_cells (normalize rsegs (g_mem g))) as (v0 & v1 & HG0).
  assert (HCASE : (g_n g = 0 /\ un g = 0 /\ ud g = 0 /\ usrc g = g_p g) \/
    (1 <= g_n g /\ un g = g_n g - 1 /\ ud g = bv_unsigned (hd z8 (g_in g)) /\ usrc g = g_p g + 1 /\
     bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) [hd z8 (g_in g)] /\
     (g_p g + g_n g <= g_S g - SLOT_K \/ fsp g + 176 <= g_p g))).
  { unfold usrc. destruct (Z.eqb_spec (g_n g) 0) as [E0|E0].
    - left. split; [exact E0|]. unfold g_n in E0. split; [|split; [|reflexivity]].
      + unfold un, uF, zlen. destruct (g_in g); [reflexivity | cbn [length] in E0; lia].
      + unfold ud. destruct (g_in g); [reflexivity | cbn [length] in E0; lia].
    - right. split; [lia|]. split.
      + unfold un, uF, zlen, g_n. unfold g_n in E0. destruct (g_in g); cbn [length tl] in *; lia.
      + split; [unfold ud; unfold g_n in E0; destruct (g_in g); [cbn [length] in E0; lia | reflexivity]|].
        split; [reflexivity|]. split.
        * unfold g_n in E0. destruct (g_in g) as [|d F] eqn:Eg; [cbn [length] in E0; lia|].
          try rewrite Eg in HBN. cbn [hd]. exact (proj1 (proj1 (bytes_at_app _ _ _ [d] F) HBN)).
        * left. lia. }
  apply (ss_kA_run_o (fx:=fx') B APIf ra empty FF (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)
    (fun R pc' m' => getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z) /\ getr R 2 = wz (fsp g) /\
       getr R 3 = getr (g_regs g) 3 /\ getr R 4 = getr (g_regs g) 4 /\ getr R 9 = wz (usrc g) /\
       getr R 10 = wz (un g) /\ getr R 18 = wz (un g) /\ getr R 26 = wz G_FILE_LEN /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc) /\
       munch [(fsp g, fsp g + 176); ((symaddr Symbols.Ubsan.s_g_file_len), (symaddr Symbols.Ubsan.s_environ))] (normalize rsegs (g_mem g)) m' /\
       wmono rsegs (normalize rsegs (g_mem g)) m' /\
       bytes_at rsegs m' (g_S g - 104) (saved_bytes ra g) /\
       rw_cells rsegs m' (fsp g) [C8 (wz (ud g))] /\
       rw_cells rsegs m' (symaddr Symbols.Ubsan.s_g_file_len) [C8 (wz (un g)); C8 (wz (usrc g))])
    _ _ Hh Hl HMI).
  - rewrite ss_mkR_of. unfold ENTRY. eapply evt_mono.
    + eapply ubs_E_x with (m := normalize rsegs (g_mem g)) (lo := g_S g - SLOT_K) (sp_h := fsp g) (p := g_p g)
        (z := g_n g) (n := un g) (c0 := ud g) (P := usrc g) (d := hd z8 (g_in g)) (vc := vc) (v0 := v0) (v1 := v1).
      * rewrite HgS. unfold wz. f_equal. lia.
      * exact Hp.
      * exact Hnn.
      * exact Hn.
      * lia.
      * pose proof alloc_ceiling_value. lia.
      * exact HCASE.
      * apply mem_inv_normalize.
      * exact HSTK.
      * lia.
      * lia.
      * exact HC0.
      * exact HG0.
    + intros ms' (a1' & a2' & m0 & -> & MU & WM & _ & _ & SB & C0 & GC).
      do 3 eexists. split; [reflexivity|]. cbv beta.
      do 9 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|].
      split; [|split; [exact C0 | exact GC]].
      replace (g_S g - 104) with (fsp g + 72) by lia.
      unfold saved_bytes. rewrite <- Hra. exact SB.
  - intros R pc' m0 regs' m' (H1 & H2 & H3 & H4 & H9 & H10 & H18 & H26 & -> & MU & WM & SB & C0 & GC) Hx Hrel Hsame.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI') as HR0.
    pose proof (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m0 HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m0 HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs (g_mem g) m' HMI' Hsame) as Hro'.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (fsp g <= a < fsp g + 176) -> ~ ((symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ)) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha N1 N2.
      apply (ss_munch_unch (fun y => (fsp g <= y < fsp g + 176) \/ ((symaddr Symbols.Ubsan.s_g_file_len) <= y < (symaddr Symbols.Ubsan.s_environ))) _ _ _ MU');
        [| exact Ha | cbv beta; tauto].
      intros lo hi y Hin Hy. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; [left | right]; exact Hy. }
    assert (UNm : forall a, 0 <= a < (symaddr Symbols.Ubsan.s_g_file_len) \/ (symaddr Symbols.Ubsan.s_environ) <= a < fsp g ->
                  mbyte rsegs m' a = mbyte rsegs (g_mem g) a).
    { intros a Ha. exact (proj1 (ss_eq_at (g_mem g) m' a (UN a ltac:(lia) ltac:(lia) ltac:(lia)))). }
    assert (UNb : forall a bs, (forall i, 0 <= i < Z.of_nat (length bs) ->
                    0 <= a + i < (symaddr Symbols.Ubsan.s_g_file_len) \/ (symaddr Symbols.Ubsan.s_environ) <= a + i < fsp g) ->
                  bytes_at rsegs (g_mem g) a bs -> bytes_at rsegs m' a bs).
    { intros a bs Hr HBs. apply (ss_bytes_same rsegs (g_mem g) m'); [|exact HBs].
      intros i Hi. specialize (Hr i Hi). apply UN; lia. }
    (* the stdio state, the open-file head and the stderr FILE at the call, from the entry memory *)
    assert (HSTD' : stdio_ok m').
    { destruct HSTD0 as (S1 & S2 & S3). split; [|split]; (eapply UNb; [|eassumption]); intros i Hi;
        cbn [length] in Hi; rewrite ?length_le4 in Hi; unfold A_LIBC, A_OFL_LOCK; lia. }
    assert (HOFL' : ofl_empty m').
    { unfold ofl_empty in *. apply (tr_img_rw (g_mem g) m' A_OFL_HEAD _); [|exact HOFL0].
      intros i Hi. change (Z.of_nat (cells_size [C8 (wz 0)])) with 8 in Hi.
      split; [apply (proj2 (img_w_iff _)); right; right; lia|].
      apply UNm. unfold A_OFL_HEAD. lia. }
    assert (HERR' : exists fl md, errf m' fl md).
    { apply (tr_errf_se (g_mem g) m'); [|exists 5, mdv; exact HE0].
      intros x Hx'. apply UNm. unfold A_STDERR in Hx'. lia. }
    (* g_file_len, g_file, the first byte's cell and the saved registers, in the actual memory *)
    pose proof (rw_rel m' m0 _ _ Hrel GC) as GC'.
    pose proof (ss_cells_bytes m' (symaddr Symbols.Ubsan.s_g_file_len) _ GC') as GB.
    cbn [cells_bytes cbytes] in GB. rewrite app_nil_r in GB.
    apply bytes_at_app in GB. destruct GB as [GB0 GB8].
    rewrite length_le8 in GB8. replace ((symaddr Symbols.Ubsan.s_g_file_len) + Z.of_nat 8) with (G_FILE_LEN + 8) in GB8 by (unfold G_FILE_LEN; lia).
    pose proof (q64_of_rw m' (fsp g) (ud g) (rw_rel m' m0 _ _ Hrel C0)) as Q0.
    pose proof (proj2 (bytes_at_rel rsegs m' m0 _ _ Hrel) SB) as SB'.
    (* the frame record at the call *)
    assert (HF1 : FR B APIf ra empty g 0 [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (ss_fr_of (fx:=fx') B APIf ra empty FF g 0 [] (g_L g) (g_A g) (g_mem g) (g_md g) regs' m').
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [intros _; reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. exact Ha.
      - exact HgR.
      - intros a Ha N1 N2. apply UN; [exact Ha | lia |].
        intros Hr. apply N2. split; [apply (proj2 (img_w_iff a)); right; left; exact Hr | exact (ue_not_relro a Hr)].
      - exact WM'.
      - exact Hro'.
      - rewrite (ss_getr_eqv _ _ _ Hx), H2. reflexivity.
      - rewrite (ss_getr_eqv _ _ _ Hx). exact H3.
      - rewrite (ss_getr_eqv _ _ _ Hx). exact H4.
      - exact SB'. }
    assert (HP1 : Permutation (blocks (g_L g) (g_A g)) ([] ++ blocks (g_L g) (g_A g))) by apply Permutation_refl.
    rewrite <- (ss_malloc_pc B APIf ra empty FF).
    apply (ss_malloc_step (fx:=fx') B APIf ra empty FF g 0 [] (g_L g) (g_A g) regs' m' (g_md g) (un g) _ _ HF1 HP1).
    + cbn [length]. lia.
    + unfold hb_bytes. cbn [map fold_right]. lia.
    + exact Hun.
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ug_ret_ok; [lia | reflexivity].
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + exact HSTD'.
    + intros L' A' regs2 mem2 md2 b HF2 HP2 HRP2 H10b Hb FR2 _ IMG2 STD2 GRD2.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z) 1 [(b, un g)] _ L' A' regs2 mem2 md2 Hfrm HF2 HP2).
      rewrite SEGS in FR2, IMG2.
      assert (KS : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)).
      { intros r Hr. rewrite (HRP2 r Hr). exact (ss_getr_eqv _ _ _ Hx). }
      assert (IG : forall x, G_FILE_LEN <= x < G_FILE_LEN + 16 -> mbyte rsegs mem2 x = mbyte rsegs m' x).
      { intros x Hx'. apply IMG2, (proj2 (img_w_iff x)). right; left. unfold G_FILE_LEN in Hx'. lia. }
      split; [exact H10b|].
      split; [transitivity (getr R 9); [exact (KS 9 ltac:(unfold callee_saved; lia)) | exact H9]|].
      split; [transitivity (getr R 18); [exact (KS 18 ltac:(unfold callee_saved; lia)) | exact H18]|].
      split; [transitivity (getr R 26); [exact (KS 26 ltac:(unfold callee_saved; lia)) | exact H26]|].
      split; [exact STD2|]. split; [exact GRD2|].
      split; [exact (tr_errf m' mem2 IMG2 HERR')|].
      split; [exact (tr_ofl_empty m' mem2 IMG2 HOFL')|].
      split; [apply (ss_q64_tr g m' mem2 0 (ud g) FR2); [unfold SLOT_FRAME; lia|];
              unfold spk; rewrite Z.add_0_r; exact Q0|].
      split; [apply (tr_q64 m' mem2 G_FILE_LEN (un g)); [intros x Hx'; apply IG; lia | exact GB0]|].
      apply (tr_q64 m' mem2 (G_FILE_LEN + 8) (usrc g)); [intros x Hx'; apply IG; lia | exact GB8].
Qed.

(* The cut-free twin of ug_E: the malloc through the cut-free malloc contract (room_cf from the cap bound and the
   budget law). *)
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Lemma ug_E_cf : Hcut_cf B APIf ra (Inv_K12d28 B APIf ra empty) (fun g => PW.OUT (g_in g)) ->
  Hcut_cf B APIf ra (Inv_ENTRY B APIf ra empty) (fun g => PW.OUT (g_in g)).
Proof.
  intros HX g c HCAP (fx' & -> & Hfrm & HGV & Hpre & HMI & Hres & HGI & Hfd).
  pose proof (sg_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HgR & HgSn & HgFs & HgFd).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hnn & Hpp & Hrod).
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (sg_GV_S B empty g HGV) as [Esp _].
  destruct (stdio_of_entry B APIf ra empty FF g HGV Hpre) as (HSTD0 & HOFL0 & HGRD0).
  destruct (errf_of_img B APIf ra empty FF 0%nat (g_mem g) HgR HGI) as (mdv & _ & HE0).
  destruct (sg_md B APIf (g_L g) (g_A g) (g_mem g) (g_md g) HM) as [Hh Hl].
  assert (HMI' : ro_agree rsegs (g_mem g)) by (unfold MI in HMI; rewrite SEGS in HMI; exact HMI).
  assert (Efsp : fsp g = g_S g - 176) by reflexivity.
  assert (EK : SLOT_K = 65536) by reflexivity.
  assert (Hun : 0 <= un g < 2 ^ 26) by (pose proof (un_le_n g); unfold un, zlen in *; lia).
  (* the payload block: its range and its bytes *)
  assert (Hrange : 0 < g_p g /\ g_p g + g_n g <= alloc_ceiling).
  { destruct Hnp as [[Hn0 Hpe] | [Hnpos Hin]].
    - rewrite Hpe, Hn0, EMP. lia.
    - destruct (ss_blk_facts (fx:=fx') B APIf ra empty FF _ _ _ _ _ _ 0 HM Hin ltac:(lia)) as (_ & H1 & H2 & _).
      lia. }
  assert (HBA : bytes_at rsegs (g_mem g) (g_p g) (g_in g)).
  { split; [lia|]. split; [unfold g_n in Hrange; lia|]. intros i Hi.
    pose proof (Hblk (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity. }
  pose proof (bytes_at_normalize rsegs (g_mem g) (g_p g) (g_in g) HMI' HBA) as HBN.
  assert (HSTK : stk rsegs (normalize rsegs (g_mem g)) (g_S g - SLOT_K) (fsp g + 176)).
  { rewrite Efsp. replace (g_S g - 176 + 176) with (g_S g) by lia.
    apply ss_stk_norm; [exact HMI' | unfold SS_TOP; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha. }
  destruct (c8_of_stk _ _ _ (fsp g) HSTK ltac:(lia) ltac:(lia)) as (vc & HC0).
  destruct (ue_gfile_cells (normalize rsegs (g_mem g))) as (v0 & v1 & HG0).
  assert (HCASE : (g_n g = 0 /\ un g = 0 /\ ud g = 0 /\ usrc g = g_p g) \/
    (1 <= g_n g /\ un g = g_n g - 1 /\ ud g = bv_unsigned (hd z8 (g_in g)) /\ usrc g = g_p g + 1 /\
     bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) [hd z8 (g_in g)] /\
     (g_p g + g_n g <= g_S g - SLOT_K \/ fsp g + 176 <= g_p g))).
  { unfold usrc. destruct (Z.eqb_spec (g_n g) 0) as [E0|E0].
    - left. split; [exact E0|]. unfold g_n in E0. split; [|split; [|reflexivity]].
      + unfold un, uF, zlen. destruct (g_in g); [reflexivity | cbn [length] in E0; lia].
      + unfold ud. destruct (g_in g); [reflexivity | cbn [length] in E0; lia].
    - right. split; [lia|]. split.
      + unfold un, uF, zlen, g_n. unfold g_n in E0. destruct (g_in g); cbn [length tl] in *; lia.
      + split; [unfold ud; unfold g_n in E0; destruct (g_in g); [cbn [length] in E0; lia | reflexivity]|].
        split; [reflexivity|]. split.
        * unfold g_n in E0. destruct (g_in g) as [|d F] eqn:Eg; [cbn [length] in E0; lia|].
          try rewrite Eg in HBN. cbn [hd]. exact (proj1 (proj1 (bytes_at_app _ _ _ [d] F) HBN)).
        * left. lia. }
  apply (ss_kA_run_o_cf (fx:=fx') B APIf ra empty FF (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)
    (fun R pc' m' => getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z) /\ getr R 2 = wz (fsp g) /\
       getr R 3 = getr (g_regs g) 3 /\ getr R 4 = getr (g_regs g) 4 /\ getr R 9 = wz (usrc g) /\
       getr R 10 = wz (un g) /\ getr R 18 = wz (un g) /\ getr R 26 = wz G_FILE_LEN /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_malloc) /\
       munch [(fsp g, fsp g + 176); ((symaddr Symbols.Ubsan.s_g_file_len), (symaddr Symbols.Ubsan.s_environ))] (normalize rsegs (g_mem g)) m' /\
       wmono rsegs (normalize rsegs (g_mem g)) m' /\
       bytes_at rsegs m' (g_S g - 104) (saved_bytes ra g) /\
       rw_cells rsegs m' (fsp g) [C8 (wz (ud g))] /\
       rw_cells rsegs m' (symaddr Symbols.Ubsan.s_g_file_len) [C8 (wz (un g)); C8 (wz (usrc g))])
    _ _ Hh Hl HMI).
  - rewrite ss_mkR_of. unfold ENTRY. eapply evt_mono.
    + eapply ubs_E_x with (m := normalize rsegs (g_mem g)) (lo := g_S g - SLOT_K) (sp_h := fsp g) (p := g_p g)
        (z := g_n g) (n := un g) (c0 := ud g) (P := usrc g) (d := hd z8 (g_in g)) (vc := vc) (v0 := v0) (v1 := v1).
      * rewrite HgS. unfold wz. f_equal. lia.
      * exact Hp.
      * exact Hnn.
      * exact Hn.
      * lia.
      * pose proof alloc_ceiling_value. lia.
      * exact HCASE.
      * apply mem_inv_normalize.
      * exact HSTK.
      * lia.
      * lia.
      * exact HC0.
      * exact HG0.
    + intros ms' (a1' & a2' & m0 & -> & MU & WM & _ & _ & SB & C0 & GC).
      do 3 eexists. split; [reflexivity|]. cbv beta.
      do 9 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|].
      split; [|split; [exact C0 | exact GC]].
      replace (g_S g - 104) with (fsp g + 72) by lia.
      unfold saved_bytes. rewrite <- Hra. exact SB.
  - intros R pc' m0 regs' m' (H1 & H2 & H3 & H4 & H9 & H10 & H18 & H26 & -> & MU & WM & SB & C0 & GC) Hx Hrel Hsame.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI') as HR0.
    pose proof (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m0 HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m0 HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs (g_mem g) m' HMI' Hsame) as Hro'.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (fsp g <= a < fsp g + 176) -> ~ ((symaddr Symbols.Ubsan.s_g_file_len) <= a < (symaddr Symbols.Ubsan.s_environ)) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha N1 N2.
      apply (ss_munch_unch (fun y => (fsp g <= y < fsp g + 176) \/ ((symaddr Symbols.Ubsan.s_g_file_len) <= y < (symaddr Symbols.Ubsan.s_environ))) _ _ _ MU');
        [| exact Ha | cbv beta; tauto].
      intros lo hi y Hin Hy. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; [left | right]; exact Hy. }
    assert (UNm : forall a, 0 <= a < (symaddr Symbols.Ubsan.s_g_file_len) \/ (symaddr Symbols.Ubsan.s_environ) <= a < fsp g ->
                  mbyte rsegs m' a = mbyte rsegs (g_mem g) a).
    { intros a Ha. exact (proj1 (ss_eq_at (g_mem g) m' a (UN a ltac:(lia) ltac:(lia) ltac:(lia)))). }
    assert (UNb : forall a bs, (forall i, 0 <= i < Z.of_nat (length bs) ->
                    0 <= a + i < (symaddr Symbols.Ubsan.s_g_file_len) \/ (symaddr Symbols.Ubsan.s_environ) <= a + i < fsp g) ->
                  bytes_at rsegs (g_mem g) a bs -> bytes_at rsegs m' a bs).
    { intros a bs Hr HBs. apply (ss_bytes_same rsegs (g_mem g) m'); [|exact HBs].
      intros i Hi. specialize (Hr i Hi). apply UN; lia. }
    (* the stdio state, the open-file head and the stderr FILE at the call, from the entry memory *)
    assert (HSTD' : stdio_ok m').
    { destruct HSTD0 as (S1 & S2 & S3). split; [|split]; (eapply UNb; [|eassumption]); intros i Hi;
        cbn [length] in Hi; rewrite ?length_le4 in Hi; unfold A_LIBC, A_OFL_LOCK; lia. }
    assert (HOFL' : ofl_empty m').
    { unfold ofl_empty in *. apply (tr_img_rw (g_mem g) m' A_OFL_HEAD _); [|exact HOFL0].
      intros i Hi. change (Z.of_nat (cells_size [C8 (wz 0)])) with 8 in Hi.
      split; [apply (proj2 (img_w_iff _)); right; right; lia|].
      apply UNm. unfold A_OFL_HEAD. lia. }
    assert (HERR' : exists fl md, errf m' fl md).
    { apply (tr_errf_se (g_mem g) m'); [|exists 5, mdv; exact HE0].
      intros x Hx'. apply UNm. unfold A_STDERR in Hx'. lia. }
    (* g_file_len, g_file, the first byte's cell and the saved registers, in the actual memory *)
    pose proof (rw_rel m' m0 _ _ Hrel GC) as GC'.
    pose proof (ss_cells_bytes m' (symaddr Symbols.Ubsan.s_g_file_len) _ GC') as GB.
    cbn [cells_bytes cbytes] in GB. rewrite app_nil_r in GB.
    apply bytes_at_app in GB. destruct GB as [GB0 GB8].
    rewrite length_le8 in GB8. replace ((symaddr Symbols.Ubsan.s_g_file_len) + Z.of_nat 8) with (G_FILE_LEN + 8) in GB8 by (unfold G_FILE_LEN; lia).
    pose proof (q64_of_rw m' (fsp g) (ud g) (rw_rel m' m0 _ _ Hrel C0)) as Q0.
    pose proof (proj2 (bytes_at_rel rsegs m' m0 _ _ Hrel) SB) as SB'.
    (* the frame record at the call *)
    assert (HF1 : FR B APIf ra empty g 0 [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (ss_fr_of (fx:=fx') B APIf ra empty FF g 0 [] (g_L g) (g_A g) (g_mem g) (g_md g) regs' m').
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [intros _; reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. exact Ha.
      - exact HgR.
      - intros a Ha N1 N2. apply UN; [exact Ha | lia |].
        intros Hr. apply N2. split; [apply (proj2 (img_w_iff a)); right; left; exact Hr | exact (ue_not_relro a Hr)].
      - exact WM'.
      - exact Hro'.
      - rewrite (ss_getr_eqv _ _ _ Hx), H2. reflexivity.
      - rewrite (ss_getr_eqv _ _ _ Hx). exact H3.
      - rewrite (ss_getr_eqv _ _ _ Hx). exact H4.
      - exact SB'. }
    assert (HP1 : Permutation (blocks (g_L g) (g_A g)) ([] ++ blocks (g_L g) (g_A g))) by apply Permutation_refl.
    rewrite <- (ss_malloc_pc B APIf ra empty FF).
    apply (ss_malloc_step_cf (fx:=fx') B APIf ra empty FF HMALCF LIMLAW g 0 [] (g_L g) (g_A g) regs' m' (g_md g)
      (un g) _ _ HCAP HF1 HP1).
    + cbn [length]. lia.
    + unfold hb_bytes. cbn [map fold_right]. lia.
    + exact Hun.
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ug_ret_ok; [lia | reflexivity].
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + exact HSTD'.
    + intros L' A' regs2 mem2 md2 b HF2 HP2 HRP2 H10b Hb FR2 _ IMG2 STD2 GRD2.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply (HX g _ HCAP). exists b.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0xa4)%Z) 1 [(b, un g)] _ L' A' regs2 mem2 md2 Hfrm HF2 HP2).
      rewrite SEGS in FR2, IMG2.
      assert (KS : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)).
      { intros r Hr. rewrite (HRP2 r Hr). exact (ss_getr_eqv _ _ _ Hx). }
      assert (IG : forall x, G_FILE_LEN <= x < G_FILE_LEN + 16 -> mbyte rsegs mem2 x = mbyte rsegs m' x).
      { intros x Hx'. apply IMG2, (proj2 (img_w_iff x)). right; left. unfold G_FILE_LEN in Hx'. lia. }
      split; [exact H10b|].
      split; [transitivity (getr R 9); [exact (KS 9 ltac:(unfold callee_saved; lia)) | exact H9]|].
      split; [transitivity (getr R 18); [exact (KS 18 ltac:(unfold callee_saved; lia)) | exact H18]|].
      split; [transitivity (getr R 26); [exact (KS 26 ltac:(unfold callee_saved; lia)) | exact H26]|].
      split; [exact STD2|]. split; [exact GRD2|].
      split; [exact (tr_errf m' mem2 IMG2 HERR')|].
      split; [exact (tr_ofl_empty m' mem2 IMG2 HOFL')|].
      split; [apply (ss_q64_tr g m' mem2 0 (ud g) FR2); [unfold SLOT_FRAME; lia|];
              unfold spk; rewrite Z.add_0_r; exact Q0|].
      split; [apply (tr_q64 m' mem2 G_FILE_LEN (un g)); [intros x Hx'; apply IG; lia | exact GB0]|].
      apply (tr_q64 m' mem2 (G_FILE_LEN + 8) (usrc g)); [intros x Hx'; apply IG; lia | exact GB8].
Qed.

End E.
