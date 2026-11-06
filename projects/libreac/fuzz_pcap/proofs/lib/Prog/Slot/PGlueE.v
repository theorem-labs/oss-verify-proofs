From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PCut PImg PSegE PGlueR
  PGlueB.
Import ListNotations.
Open Scope Z_scope.

(* Glue of segment E: from the slot's entry (Inv_ENTRY, payload below 2^26 bytes) through pcap_E_x to
   malloc(gn g) (ra 0x12c7c), then K1. The frame record at the call is built by ss_fr_of: the entry memory
   differs only in the slot's frame and the 16 bytes at 0x2ec10 (img_w outside frame_RELRO). *)

(* The image holds a byte at each of the 16 bytes at 0x2ec10 (g_file_len, g_file), so every memory reads them. *)
Definition gl_rom_chk (a : Z) (k : nat) : bool :=
  forallb (fun i => match mrd rsegs (fun _ => None) (Z_to_bv 64 (a + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 k).

Lemma gl_rom_gfile : gl_rom_chk (symaddr Symbols.Plain.s_g_file_len) 16 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma gl_mrd_none : forall m w, mrd rsegs m w = None -> mrd rsegs (fun _ => None) w = None.
Proof. intros m w H. unfold mrd in *. destruct (m w); [discriminate | exact H]. Qed.

Lemma gl_mrd_some : forall m a k j, gl_rom_chk a k = true -> (j < k)%nat ->
  mrd rsegs m (Z_to_bv 64 (a + Z.of_nat j)) <> None.
Proof.
  intros m a k j H Hj HN. apply gl_mrd_none in HN. unfold gl_rom_chk in H. rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)). cbv beta in H. rewrite HN in H. discriminate H.
Qed.

Lemma gl_gfile_cells : forall m, rw_cells rsegs m (symaddr Symbols.Plain.s_g_file_len) [Cells.CB 16 (ss_rd_list (mrd rsegs m) (symaddr Symbols.Plain.s_g_file_len) 16)].
Proof.
  intros m. split; [split|].
  - cbn [Cells.cells_wf Cells.cell_wf]. rewrite ss_rd_list_len. split; [reflexivity | exact I].
  - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
    split; [lia|]. split; [rewrite ss_rd_list_len; lia|].
    intros j Hj. rewrite ss_rd_list_len in Hj. rewrite ss_rd_list_nth by exact Hj. unfold wa.
    pose proof (gl_mrd_some m (symaddr Symbols.Plain.s_g_file_len) 16 j gl_rom_gfile Hj) as HS.
    destruct (mrd rsegs m (Z_to_bv 64 ((symaddr Symbols.Plain.s_g_file_len) + Z.of_nat j))) as [b|]; [reflexivity | congruence].
  - change (Z.of_nat (Cells.cells_size [Cells.CB 16 (ss_rd_list (mrd rsegs m) (symaddr Symbols.Plain.s_g_file_len) 16)])) with 16.
    split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (img_w_wr m ((symaddr Symbols.Plain.s_g_file_len) + i) ltac:(apply (proj2 (img_w_iff _)); right; left; lia))).
Qed.

(* The 16 bytes at 0x2ec10 lie outside frame_RELRO. *)
Lemma gl_not_relro : forall a, (symaddr Symbols.Plain.s_g_file_len) <= a < (symaddr Symbols.Plain.s_environ) -> ~ in_globals frame_RELRO a.
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

(* The file bytes at gsrc g, from the payload block that every frame record keeps (fx0: any FP state). *)
Lemma gl_src_bytes : forall (fx0 : YK11.FPState) g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  bytes_at rsegs mem (gsrc g) (gF g).
Proof.
  intros fx0 g km hb L A regs mem md HF HP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _ & _ & _ & _ & _ & _ & HB0 & _).
  pose proof HGV as (_ & Hnp & Hblk & _).
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  unfold gsrc, gF. unfold g_n in Hnp.
  destruct (g_in g) as [|d F] eqn:Eg.
  - destruct Hnp as [[_ Hpe] | [Hnpos _]]; [|cbn [length] in Hnpos; lia].
    cbn [tl]. rewrite Hpe. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
  - cbn [tl].
    destruct Hnp as [[Hn0 _] | [Hnpos Hin]]; [cbn [length] in Hn0; lia|].
    assert (Hin' : In (g_p g, Z.of_nat (length (d :: F))) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (ss_blk_facts (fx:=fx0) B APIf ra empty FF L A mem md _ _ 0 HMR Hin' ltac:(cbn [length]; lia))
      as (_ & H1 & H2 & _).
    cbn [length] in H2.
    split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (HB0 (g_p g) _ (Z.of_nat (S i)) Hin ltac:(cbn [length]; lia)) as E1.
    pose proof (Hblk (Z.of_nat (S i)) ltac:(cbn [length]; lia)) as E2.
    rewrite Nat2Z.id in E2. cbn [nth_error] in E2. rewrite E2 in E1.
    rewrite <- E1, (ss_segs B APIf ra empty FF).
    replace (g_p g + 1 + Z.of_nat i) with (g_p g + Z.of_nat (S i)) by lia. reflexivity.
Qed.

(* Inv_ENTRY 0x12c04 (payload below 2^26 bytes): pcap_E_x, then malloc(gn g) (ra 0x12c7c), then K1. *)
Lemma seg_E : Hcut_o B APIf ra (Inv_K1 B APIf ra empty) oOUT ->
  Hcut_o B APIf ra (Inv_ENTRY B APIf ra empty) oOUT.
Proof.
  intros HX g c (fx' & -> & Hfrm & HGV & Hpre & HMI & Hres & HGI & Hfd).
  pose proof (ss_segs B APIf ra empty FF) as SEGS.
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
  unfold SLOT_K, SLOT_STACK in *.
  assert (USP : bv_unsigned (getr (g_regs g) 2) = g_S g) by (rewrite HgS; apply unsigned_lit; lia).
  (* the payload block: its range, its bytes, and its place against the frame and 0x2ec10 *)
  assert (Hrange : 0 <= g_p g /\ g_p g + g_n g <= alloc_ceiling).
  { destruct Hnp as [[Hn0 Hpe] | [Hnpos Hin]].
    - rewrite Hpe, Hn0, EMP. lia.
    - destruct (ss_blk_facts (fx:=fx') B APIf ra empty FF _ _ _ _ _ _ 0 HM Hin ltac:(lia)) as (_ & H1 & H2 & _).
      lia. }
  assert (HDJ : g_p g + g_n g <= (symaddr Symbols.Plain.s_g_file_len) \/ (symaddr Symbols.Plain.s_environ) <= g_p g).
  { destruct Hnp as [[Hn0 Hpe] | [Hnpos Hin]].
    - left. rewrite Hpe, Hn0, EMP. lia.
    - destruct (Z_le_gt_dec (g_p g + g_n g) (symaddr Symbols.Plain.s_g_file_len)) as [L1|L1]; [left; exact L1|].
      destruct (Z_le_gt_dec (symaddr Symbols.Plain.s_environ) (g_p g)) as [L2|L2]; [right; exact L2|].
      exfalso.
      destruct (ss_blk_facts (fx:=fx') B APIf ra empty FF _ _ _ _ _ _ (Z.max (g_p g) (symaddr Symbols.Plain.s_g_file_len) - g_p g) HM Hin
        ltac:(lia)) as (_ & _ & _ & _ & Himg).
      apply Himg. replace (g_p g + (Z.max (g_p g) (symaddr Symbols.Plain.s_g_file_len) - g_p g)) with (Z.max (g_p g) (symaddr Symbols.Plain.s_g_file_len)) by lia.
      exact (proj1 (ss_img_w_facts B APIf ra empty FF (Z.max (g_p g) (symaddr Symbols.Plain.s_g_file_len))
        ltac:(apply (proj2 (img_w_iff _)); right; left; lia))). }
  assert (HBA : bytes_at rsegs (g_mem g) (g_p g) (g_in g)).
  { split; [lia|]. split; [unfold g_n in Hrange; lia|]. intros i Hi.
    pose proof (Hblk (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, SEGS. reflexivity. }
  pose proof (MemNorm.bytes_at_normalize rsegs (g_mem g) (g_p g) (g_in g) HMI' HBA) as HBN.
  assert (HSTK : stk rsegs (MemNorm.normalize rsegs (g_mem g)) (g_S g - 65536) (g_S g)).
  { apply ss_stk_norm; [exact HMI' | unfold SS_TOP; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha. }
  apply (ss_kA_run_o (fx:=fx') B APIf ra empty FF (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z) /\ getr R 2 = Z_to_bv 64 (g_S g - 160) /\
       getr R 3 = getr (g_regs g) 3 /\ getr R 4 = getr (g_regs g) 4 /\ getr R 8 = Z_to_bv 64 (gd g) /\
       getr R 9 = Z_to_bv 64 (gsrc g) /\ getr R 10 = Z_to_bv 64 (gn g) /\ getr R 18 = Z_to_bv 64 (gn g) /\
       getr R 22 = Z_to_bv 64 (symaddr Symbols.Plain.s_g_file_len) /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_malloc) /\
       munch [(g_S g - 160, g_S g); ((symaddr Symbols.Plain.s_g_file_len), (symaddr Symbols.Plain.s_environ))] (MemNorm.normalize rsegs (g_mem g)) m' /\
       wmono rsegs (MemNorm.normalize rsegs (g_mem g)) m' /\
       bytes_at rsegs m' (g_S g - 104) (saved_bytes ra g) /\
       rw_cells rsegs m' (symaddr Symbols.Plain.s_g_file_len) [Cells.C8 (wz (gn g)); Cells.C8 (wz (gsrc g))])
    (oOUT g) (Post_o B APIf ra g) Hh Hl HMI).
  - rewrite ss_mkR_of. unfold ENTRY. eapply evt_mono.
    + apply (pcap_E_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (MemNorm.normalize rsegs (g_mem g)) (g_in g) _ (g_p g) (g_S g) (g_S g - 65536)
        USP Hp Hnn (proj2 Hn) HBN ltac:(left; unfold g_n in Hrange; lia) HDJ HSTK ltac:(lia) ltac:(lia)
        (gl_gfile_cells _) (MemNorm.mem_inv_normalize rsegs (g_mem g))).
    + intros ms' (a2' & m0 & -> & MU & WM & _ & _ & SB & GC & _ & _).
      do 3 eexists. split; [reflexivity|]. cbv beta.
      do 10 (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|].
      split; [unfold saved_bytes; rewrite <- Hra; exact SB | exact GC].
  - intros R pc' m0 regs' m' (H1 & H2 & H3 & H4 & H8 & H9 & H10 & H18 & H22 & -> & MU & WM & SB & GC) Hx Hrel Hsame.
    pose proof (MemNorm.mem_rel_normalize rsegs (g_mem g) HMI') as HR0.
    pose proof (MemNorm.munch_rel rsegs _ (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' m0 HR0 Hrel Hsame MU) as MU'.
    pose proof (MemNorm.wmono_rel rsegs (g_mem g) (MemNorm.normalize rsegs (g_mem g)) m' m0 HR0 Hrel Hsame WM) as WM'.
    pose proof (MemNorm.ro_agree_same rsegs (g_mem g) m' HMI' Hsame) as Hro'.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - 160 <= a < g_S g) -> ~ ((symaddr Symbols.Plain.s_g_file_len) <= a < (symaddr Symbols.Plain.s_environ)) ->
                 m' (Z_to_bv 64 a) = g_mem g (Z_to_bv 64 a)).
    { intros a Ha N1 N2.
      apply (ss_munch_unch (fun y => (g_S g - 160 <= y < g_S g) \/ ((symaddr Symbols.Plain.s_g_file_len) <= y < (symaddr Symbols.Plain.s_environ))) _ _ _ MU');
        [| exact Ha | cbv beta; tauto].
      intros lo hi y Hin Hy. cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; [left | right]; exact Hy. }
    assert (UNm : forall a, 0 <= a < (symaddr Symbols.Plain.s_g_file_len) \/ (symaddr Symbols.Plain.s_environ) <= a < g_S g - 160 ->
                  mbyte (ms_segs B) m' a = mbyte (ms_segs B) (g_mem g) a).
    { intros a Ha. rewrite SEGS. exact (proj1 (ss_eq_at (g_mem g) m' a (UN a ltac:(lia) ltac:(lia) ltac:(lia)))). }
    assert (UNb : forall a bs, (forall i, 0 <= i < Z.of_nat (length bs) ->
                    0 <= a + i < (symaddr Symbols.Plain.s_g_file_len) \/ (symaddr Symbols.Plain.s_environ) <= a + i < g_S g - 160) ->
                  bytes_at rsegs (g_mem g) a bs -> bytes_at rsegs m' a bs).
    { intros a bs Hr HBs. apply (ss_bytes_same rsegs (g_mem g) m'); [|exact HBs].
      intros i Hi. specialize (Hr i Hi). apply UN; lia. }
    (* the stdio state, the open-file head and the stderr FILE at the call, from the entry memory *)
    assert (HSTD' : stdio_ok m').
    { destruct HSTD0 as (S1 & S2 & S3). split; [|split]; (eapply UNb; [|eassumption]); intros i Hi;
        cbn [length] in Hi; rewrite ?length_le4 in Hi; unfold A_LIBC, A_OFL_LOCK; lia. }
    assert (HOFL' : ofl_empty m').
    { apply (gl_rw_keep (g_mem g) m' _ _ HOFL0). intros i Hi.
      change (Z.of_nat (Cells.cells_size [Cells.C8 (wz 0)])) with 8 in Hi.
      split; [exact (proj1 (ss_eq_at (g_mem g) m' (A_OFL_HEAD + i) (UN (A_OFL_HEAD + i)
                ltac:(unfold A_OFL_HEAD; lia) ltac:(unfold A_OFL_HEAD; lia) ltac:(unfold A_OFL_HEAD; lia))))|].
      exact (proj1 (img_w_wr m' (A_OFL_HEAD + i) ltac:(right; left; lia))). }
    assert (HERR' : err_ok m').
    { exists 5, mdv. apply (errf_keep B APIf ra empty FF (g_mem g) m' 5 mdv HE0).
      intros i Hi. apply UNm. unfold A_STDERR. lia. }
    (* g_file_len and g_file *)
    pose proof (ss_cells_bytes m0 (symaddr Symbols.Plain.s_g_file_len) _ GC) as GB.
    cbn [Cells.cells_bytes Cells.cbytes] in GB. rewrite app_nil_r in GB.
    apply bytes_at_app in GB. destruct GB as [GB0 GB8].
    rewrite length_le8 in GB8. replace ((symaddr Symbols.Plain.s_g_file_len) + Z.of_nat 8) with (symaddr Symbols.Plain.s_g_file) in GB8 by lia.
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs m' m0 _ _ Hrel) GB0) as Q0.
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs m' m0 _ _ Hrel) GB8) as Q8.
    pose proof (proj2 (MemNorm.bytes_at_rel rsegs m' m0 _ _ Hrel) SB) as SB'.
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
      - intros a Ha N1 N2. apply UN; [exact Ha | unfold SLOT_K, SLOT_STACK in N1; lia |].
        intros Hr. apply N2. split; [apply (proj2 (img_w_iff a)); right; left; exact Hr | exact (gl_not_relro a Hr)].
      - exact WM'.
      - exact Hro'.
      - rewrite (ss_getr_eqv _ _ _ Hx), H2. unfold fsp, SLOT_FRAME. reflexivity.
      - rewrite (ss_getr_eqv _ _ _ Hx). exact H3.
      - rewrite (ss_getr_eqv _ _ _ Hx). exact H4.
      - exact SB'. }
    assert (HP1 : Permutation (blocks (g_L g) (g_A g)) ([] ++ blocks (g_L g) (g_A g))) by apply Permutation_refl.
    pose proof (gl_gn B empty g HGV) as Hgn.
    rewrite <- (ss_malloc_pc B APIf ra empty FF).
    apply (ss_malloc_step B APIf ra empty FF g 0 [] (g_L g) (g_A g) regs' m' (g_md g) (gn g) (oOUT g)
      (Post_o B APIf ra g) HF1 HP1).
    + cbn [length]. lia.
    + unfold hb_bytes. cbn [map fold_right]. lia.
    + exact Hgn.
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + exact HSTD'.
    + intros L' A' regs2 mem2 md2 b HF2 HP2 HRP2 H10b Hb _ _ HIMG HSTD HGRD.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, (0 + 1).
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x78)%Z) (0 + 1) (hb_b g b) (P_K1 g b) L' A' regs2 mem2 md2 Hfrm HF2 HP2).
      assert (KS : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)).
      { intros r Hr. rewrite (HRP2 r Hr). exact (ss_getr_eqv _ _ _ Hx). }
      split; [exact H10b|]. split; [exact Hb|].
      split; [transitivity (getr R 8); [exact (KS 8 ltac:(unfold callee_saved; lia)) | exact H8]|].
      split; [transitivity (getr R 9); [exact (KS 9 ltac:(unfold callee_saved; lia)) | exact H9]|].
      split; [transitivity (getr R 18); [exact (KS 18 ltac:(unfold callee_saved; lia)) | exact H18]|].
      split; [transitivity (getr R 22); [exact (KS 22 ltac:(unfold callee_saved; lia)) | exact H22]|].
      split.
      { split; [exact HSTD|]. split; [exact HGRD|]. exact (err_keep B APIf ra empty FF m' mem2 HERR' HIMG). }
      split; [exact (ofl_keep B APIf ra empty FF m' mem2 HOFL' HIMG)|].
      split; [exact (gl_q64_keep B APIf ra empty FF m' mem2 (symaddr Symbols.Plain.s_g_file_len) (gn g) HIMG ltac:(lia) ltac:(lia) Q0)|].
      split; [exact (gl_q64_keep B APIf ra empty FF m' mem2 (symaddr Symbols.Plain.s_g_file) (gsrc g) HIMG ltac:(lia) ltac:(lia) Q8)|].
      exact (gl_src_bytes fx' g _ _ L' A' regs2 mem2 md2 HF2 HP2).
Qed.

End E.
