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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel libreac_fuzz_fopen_c
  pcap_source_struct pcap_source_struct_next pcap_source_open_c pcap_source_close_c pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PCut PImg PSteps
  PWalkDef PWalk PSegW PSegR.
Import ListNotations.
Open Scope Z_scope.

(* Glue of the slot's run after the walk: the walk's close (K5 -> K6, segment W), the reopen (K6 -> K7), the read
   after the reopen (K7 -> K8), the second close (K8 -> K9) and the read of the closed reader (K9 -> K10). Each
   lemma runs the segment from its cut to the call (ss_kA_run0_o: no segment here stores to memory), takes the
   callee's step (PSteps) and closes the next cut. *)

(* A callee-saved register through a segment that keeps it (HK) and a call that preserves it (HRP). *)
Ltac rn_keep regs1 regs0 k HRP Hx HK H :=
  transitivity (getr regs1 (Z_to_bv 5 k)); [exact (HRP k ltac:(unfold callee_saved; lia))|];
  rewrite (ss_getr_eqv _ _ _ Hx); transitivity (getr regs0 (Z_to_bv 5 k)); [exact (HK k ltac:(ss_in)) | exact H].

(* The f cell and the byte-order cell of the reader's cells. *)
Lemma rn_ps_f : forall m a f sw o v i pad, rw_cells rsegs m a (ps_cells f sw o v i pad) -> bytes_at rsegs m a (le8 f).
Proof.
  intros m a f sw o v i pad H. pose proof (ss_cells_bytes m a _ H) as HB.
  cbn [ps_cells cells_bytes cbytes] in HB. apply bytes_at_app in HB as [HB _]. exact HB.
Qed.

Lemma rn_ps_sw : forall m a f sw o v i pad, rw_cells rsegs m a (ps_cells f sw o v i pad) ->
  bytes_at rsegs m (a + 8) (le4 sw).
Proof.
  intros m a f sw o v i pad H. pose proof (ss_cells_bytes m a _ H) as HB.
  cbn [ps_cells cells_bytes cbytes] in HB. apply bytes_at_app in HB as [_ HB]. rewrite length_le8 in HB.
  apply bytes_at_app in HB as [HB _]. exact HB.
Qed.

Section RN.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HCLOSE : forall fx : YK11.FPState, @pcap_source_close_contract fx rc B (APIf rc).
Hypothesis HOPEN : forall fx : YK11.FPState, @pcap_source_open_contract fx rc B (APIf rc).
Hypothesis HNEXT : forall fx : YK11.FPState, @pcap_source_next_contract fx.

(* The file is shorter than the payload. *)
Lemma rn_gn : forall g, GV B empty g -> 0 <= gn g < 2 ^ 26.
Proof.
  intros g (Hn & _). unfold gn, gF. unfold g_n in Hn.
  destruct (g_in g) as [|d l]; cbn [tl length] in *; lia.
Qed.

(* A heap block of the cut holds some bytes, all writable. *)
Lemma rn_u8arr : forall g km hb L A regs mem md a k,
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

(* The open-file head and the stderr FILE through a callee that keeps their bytes. *)
Lemma rn_ofl : forall m m' h, ofl_one m h ->
  (forall x, A_OFL_HEAD <= x < A_OFL_HEAD + 8 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> ofl_one m' h.
Proof.
  intros m m' h [[Hwf HB] _] HK. rewrite (ss_segs B APIf ra empty FF) in HK.
  split; [split; [exact Hwf|]|].
  - apply (ss_bytes_mbyte rsegs m m'); [|exact HB]. intros i Hi.
    assert (L8 : Z.of_nat (length (cells_bytes [C8 (wz h)])) = 8) by reflexivity.
    rewrite L8 in Hi. apply HK. lia.
  - change (Z.of_nat (cells_size [C8 (wz h)])) with 8.
    split; [unfold A_OFL_HEAD; lia|]. split; [unfold A_OFL_HEAD; lia|]. intros i Hi.
    exact (proj1 (img_w_wr m' (A_OFL_HEAD + i) ltac:(right; left; lia))).
Qed.

Lemma rn_err : forall m m', err_ok m ->
  (forall x, A_STDERR <= x < A_STDERR + 232 -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> err_ok m'.
Proof.
  intros m m' (fl & md & HE) HK. exists fl, md.
  apply (errf_keep B APIf ra empty FF m m' fl md HE). intros i Hi. apply HK. lia.
Qed.

(* The slot's sp and the reader's cells at sp + 32. *)
Lemma rn_sp : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  bv_unsigned (getr regs 2) = fsp g /\ fsp g + SLOT_FRAME = g_S g /\ (fsp g + 32) mod 8 = 0.
Proof.
  intros g km hb L A regs mem md HF.
  pose proof (ss_stk_fsp B APIf ra empty g km _ L A regs mem md HF) as (_ & _ & _ & HfS & HSc & HS47 & HSK & Hsp).
  pose proof (ss_fr_bnd B APIf ra empty FF g km _ L A regs mem md HF) as (_ & Hf16 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  split; [rewrite Hsp; rewrite unsigned_lit by lia; reflexivity|].
  split; [exact HfS|]. Z.div_mod_to_equations. lia.
Qed.

(* K9 0x13148: the closed reader is read once more (pcap_R4_x, pcap_source_next with ts NULL): it answers -1
   and outputs nothing; then K10. *)
Lemma seg_R4 : Hcut_o B APIf ra (Inv_K10 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K9 B APIf ra empty) oNil.
Proof.
  intros HX g c (b & buf & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z) km (hb_bu g b buf) (P_K9 g b buf) c (oNil g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H9 & H18 & H20 & HSB & HOFL & (sw & olen & vtag & vid & pad & HPS)).
  destruct (rn_sp g km _ L A regs mem md HF) as (USP & HfS & Hp8). unfold SLOT_FRAME in HfS.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z) /\ getr R 10 = Z_to_bv 64 (fsp g + 32) /\
       getr R 11 = getr regs 18 /\ getr R 12 = getr regs 9 /\ getr R 13 = Z_to_bv 64 0 /\
       KP [2; 3; 4; 18; 20] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next) /\ m' = mem)
    (oNil g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono; [eapply pcap_R4_x; exact USP|].
    intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
    do 5 (split; [reflexivity|]). split; [|split; reflexivity].
    intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10 & H11 & H12 & H13 & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_bu g b buf) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). apply HK. cbn [In] in Hk |- *. tauto. }
    destruct HSB as (HSTD & HGRD & (fl & mdv & HEF)).
    destruct (rn_u8arr g km _ L A regs mem md buf (gbn g) HF HP ltac:(unfold hb_bu; right; left; reflexivity)
      ltac:(pose proof (gcap_range g); lia)) as (bj & HBJ & HBN).
    pose proof (gcap_range g) as (HC1 & HC2).
    replace (oNil g) with (psn_out 0 (bv_unsigned sw =? 1) (gF g) (gcap g) 24 ++ oNil g) by reflexivity.
    eapply (ps_next_step (fx:=fx') B APIf ra empty FF (HNEXT fx') g km (hb_bu g b buf) [(b, gn g)] L A regs' mem md
      (fsp g + 32) buf (gcap g) 0 0 (bv_unsigned sw) b 24 fl mdv olen vtag vid (wz 0) (wz 0) (wz 0) pad bj (gF g)
      (oNil g) (Post_o B APIf ra g) HF' HP Hfrm).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + rewrite (ss_getr_eqv _ _ _ Hx), H11. exact H18.
    + rewrite (ss_getr_eqv _ _ _ Hx), H12. exact H9.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H13.
    + lia.
    + lia.
    + exact Hp8.
    + unfold wz at 2. rewrite Z_to_bv_bv_unsigned. exact HPS.
    + unfold hb_bu, gbn. apply perm_swap.
    + exact HBJ.
    + exact HBN.
    + lia.
    + intros C. congruence.
    + intros C. congruence.
    + exact HEF.
    + intros regs2 mem2 Ft fc' mdv' Hfc _ HF2 HRP2 _ _ HIMG HSTD2 HEF2 HGRD2 H10' _.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, buf, km.
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z) km (hb_bu g b buf) (P_K10 g b buf)
        L A regs2 mem2 md Hfc HF2 HP).
      split; [exact (H10' eq_refl)|].
      split; [rn_keep regs' regs 18 HRP2 Hx HK H18|].
      split; [rn_keep regs' regs 20 HRP2 Hx HK H20|].
      split; [split; [exact (HSTD2 HSTD)|]; split; [exact HGRD2 | exists fl, mdv'; exact HEF2]|].
      apply (rn_ofl mem mem2 0 HOFL). intros x Hx'. apply HIMG.
      * apply img_w_iff. right. right. exact Hx'.
      * unfold A_STDERR, A_OFL_HEAD in *. lia.
Qed.

(* K8 0x1313c: the second close (pcap_R3_x, a0 = s3 = the first answer; pcap_source_close of the open reader
   h): h is freed and the f cell holds 0; then K9. *)
Lemma seg_R3 : Hcut_o B APIf ra (Inv_K9 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K8 B APIf ra empty) oNil.
Proof.
  intros HX g c (b & buf & h & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z) km (hb_buh g b buf h) (P_K8 g b buf h) c (oNil g) (Post_o B APIf ra g)
    HC).
  intros fx' L A regs mem md Hfrm HF HP
    (H10 & H9 & H18 & H19 & H20 & HSB & (sw & olen & vtag & vid & pad & HPS) & (q & HMS) & HOFL).
  destruct (rn_sp g km _ L A regs mem md HF) as (USP & HfS & Hp8). unfold SLOT_FRAME in HfS.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z) /\ getr R 10 = Z_to_bv 64 (fsp g + 32) /\
       KP [2; 3; 4; 9; 18; 20] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close) /\ m' = mem)
    (oNil g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono.
    + eapply pcap_R3_x; [exact USP | transitivity (wz (gfirst g)); [exact H10 | symmetry; exact H19]].
    + intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
      do 2 (split; [reflexivity|]). split; [|split; reflexivity].
      intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10' & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_buh g b buf h) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). apply HK. cbn [In] in Hk |- *. tauto. }
    destruct HSB as (HSTD & HGRD & HERR).
    change (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close)) with (Z_to_bv 64 PCAP_SOURCE_CLOSE).
    apply (ps_close_step (fx:=fx') B APIf ra empty FF (HCLOSE fx') g km [(b, gn g); (buf, gbn g)] h [] L A regs'
      mem md (fsp g + 32) sw olen vtag vid pad b (gF g) q (oNil g) (Post_o B APIf ra g) HF' HP).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10'.
    + lia.
    + lia.
    + exact Hp8.
    + exact HPS.
    + cbn [app In]. left. reflexivity.
    + exact HMS.
    + exact HOFL.
    + exact HSTD.
    + intros L' A' regs2 mem2 md2 HF2 HP2 HRP2 _ _ HIMG HPS2 HOFL2 HSTD2 HGRD2 _.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, buf, km.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x544)%Z) km (hb_bu g b buf) (P_K9 g b buf) L' A' regs2 mem2 md2
        Hfrm HF2 HP2).
      split; [rn_keep regs' regs 9 HRP2 Hx HK H9|].
      split; [rn_keep regs' regs 18 HRP2 Hx HK H18|].
      split; [rn_keep regs' regs 20 HRP2 Hx HK H20|].
      split.
      { split; [exact HSTD2|]. split; [exact HGRD2|].
        apply (rn_err mem mem2 HERR). intros x Hx'. apply HIMG.
        - apply img_w_iff. left. exact Hx'.
        - unfold A_STDERR, A_OFL_HEAD in *. lia. }
      split; [exact HOFL2|]. exists sw, olen, vtag, vid, pad. exact HPS2.
Qed.

(* K7 0x13124: the read after the reopen (pcap_R2_x, pcap_source_next from position 24 with ts NULL): it outputs
   out24 and answers the first answer; then K8. *)
Lemma seg_R2 : Hcut_o B APIf ra (Inv_K8 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K7 B APIf ra empty) out24.
Proof.
  intros HX g c (b & buf & h & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z) km (hb_buh g b buf h) (P_K7 g b buf h) c (out24 g) (Post_o B APIf ra g)
    HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & H9 & H18 & H19 & H20 & HSB & (pad & HPS) & HMS & HOFL).
  destruct (rn_sp g km _ L A regs mem md HF) as (USP & HfS & Hp8). unfold SLOT_FRAME in HfS.
  pose proof HF as (HGV & _).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z) /\ getr R 10 = Z_to_bv 64 (fsp g + 32) /\
       getr R 11 = getr regs 18 /\ getr R 12 = getr regs 9 /\ getr R 13 = Z_to_bv 64 0 /\
       KP [2; 3; 4; 9; 18; 19; 20] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_next) /\ m' = mem)
    (out24 g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono; [eapply pcap_R2_x; [exact USP | exact H10]|].
    intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
    do 5 (split; [reflexivity|]). split; [|split; reflexivity].
    intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10' & H11 & H12 & H13 & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_buh g b buf h) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). apply HK. cbn [In] in Hk |- *. tauto. }
    destruct HSB as (HSTD & HGRD & (fl & mdv & HEF)).
    destruct (ss_hb_blk (fx:=fx0) B APIf ra empty FF g km _ L A regs mem md h 1304 HF HP
      ltac:(unfold hb_buh; right; right; left; reflexivity)) as (_ & Hh4 & _).
    destruct (rn_u8arr g km _ L A regs mem md buf (gbn g) HF HP ltac:(unfold hb_buh; right; left; reflexivity)
      ltac:(pose proof (gcap_range g); lia)) as (bj & HBJ & HBN).
    pose proof (gcap_range g) as (HC1 & HC2).
    assert (E : out24 g = psn_out h (gswz g =? 1) (gF g) (gcap g) 24 ++ oNil g).
    { unfold psn_out, oNil, out24, gsw. rewrite (proj2 (Z.eqb_neq h 0)) by lia. rewrite app_nil_r. reflexivity. }
    rewrite E.
    eapply (ps_next_step (fx:=fx') B APIf ra empty FF (HNEXT fx') g km (hb_buh g b buf h) [(b, gn g); (h, 1304)]
      L A regs' mem md (fsp g + 32) buf (gcap g) 0 h (gswz g) b 24 fl mdv (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0)
      pad bj (gF g) (oNil g) (Post_o B APIf ra g) HF' HP Hfrm).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10'.
    + rewrite (ss_getr_eqv _ _ _ Hx), H11. exact H18.
    + rewrite (ss_getr_eqv _ _ _ Hx), H12. exact H9.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H13.
    + lia.
    + lia.
    + exact Hp8.
    + exact HPS.
    + unfold hb_buh, gbn. apply perm_swap.
    + exact HBJ.
    + exact HBN.
    + lia.
    + intros C. congruence.
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|]. split; [exact HMS|].
      split; [exact (gswz_01 g)|]. exact (proj2 (rn_gn g HGV)).
    + exact HEF.
    + intros regs2 mem2 Ft fc' mdv' Hfc _ HF2 HRP2 _ _ HIMG HSTD2 HEF2 HGRD2 _ HPOST.
      destruct (HPOST ltac:(lia)) as (HA0 & HMS2 & HPS2 & _ & _).
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, buf, h, km.
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x538)%Z) km (hb_buh g b buf h) (P_K8 g b buf h)
        L A regs2 mem2 md Hfc HF2 HP).
      split; [exact HA0|].
      split; [rn_keep regs' regs 9 HRP2 Hx HK H9|].
      split; [rn_keep regs' regs 18 HRP2 Hx HK H18|].
      split; [rn_keep regs' regs 19 HRP2 Hx HK H19|].
      split; [rn_keep regs' regs 20 HRP2 Hx HK H20|].
      split; [split; [exact (HSTD2 HSTD)|]; split; [exact HGRD2 | exists fl, mdv'; exact HEF2]|].
      split; [do 5 eexists; exact HPS2|].
      split; [eexists; exact HMS2|].
      apply (rn_ofl mem mem2 h HOFL). intros x Hx'. apply HIMG.
      * apply img_w_iff. right. right. exact Hx'.
      * unfold A_STDERR, A_OFL_HEAD in *. lia.
Qed.

(* K6 0x1310c: the reopen (pcap_R1_x: the f cell holds 0; pcap_source_open of the accepted file at b): the reader
   opens a new FILE h2 at position 24; then K7. *)
Lemma seg_R1 : Hcut_o B APIf ra (Inv_K7 B APIf ra empty) out24 ->
  Hcut_o B APIf ra (Inv_K6 B APIf ra empty) out24.
Proof.
  intros HX g c (b & buf & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z) km (hb_bu g b buf) (P_K6 g b buf) c (out24 g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP
    (H9 & H18 & H19 & H20 & HGOOD & HSB & HOFL & HFL & HFP & HBF & (sw & olen & vtag & vid & pad & HPS)).
  destruct (rn_sp g km _ L A regs mem md HF) as (USP & HfS & Hp8). unfold SLOT_FRAME in HfS.
  pose proof HF as (HGV & _). pose proof HGV as (_ & _ & _ & _ & _ & _ & Hroom & _).
  pose proof (rn_gn g HGV) as HGN. pose proof (gcap_range g) as (HC1 & HC2).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z) /\ getr R 10 = Z_to_bv 64 (fsp g + 32) /\
       getr R 11 = Z_to_bv 64 (symaddr (Symbols.Plain.Sec.s_rodata + 0xe9)%Z) /\
       KP [2; 3; 4; 9; 18; 19; 20] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open) /\ m' = mem)
    (out24 g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono; [eapply pcap_R1_x; [exact USP | exact (rn_ps_f _ _ _ _ _ _ _ _ HPS)]|].
    intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
    do 3 (split; [reflexivity|]). split; [|split; reflexivity].
    intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10 & H11 & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_bu g b buf) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). apply HK. cbn [In] in Hk |- *. tauto. }
    destruct HSB as (HSTD & HGRD & HERR).
    change (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_open)) with (Z_to_bv 64 PCAP_SOURCE_OPEN).
    apply (ps_open_step (fx:=fx') B APIf ra empty FF (HOPEN fx') g km (hb_bu g b buf) L A regs' mem md
      (fsp g + 32) (wz 0) sw olen vtag vid pad b (gF g) (out24 g) (Post_o B APIf ra g) HF' HP).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H11.
    + lia.
    + lia.
    + exact Hp8.
    + exact HPS.
    + apply bytes_at_app. split; [exact HFL|]. rewrite length_le8.
      replace (G_FILE_LEN + Z.of_nat 8) with (symaddr Symbols.Plain.s_g_file) by (unfold G_FILE_LEN; lia). exact HFP.
    + exact (proj2 HGN).
    + intros _. unfold hb_bu. left. reflexivity.
    + exact HBF.
    + exact HSTD.
    + exact HOFL.
    + apply resb_room_w; [exact Hroom | unfold hb_bu; cbn [length]; lia | | lia].
      unfold hb_bytes, hb_bu. cbn [map fold_right snd]. lia.
    + intros L' A' regs2 mem2 md2 h2 HG _ HRP2 _ _ HIMG HSTD2 HGRD2 _.
      destruct (HG HGOOD) as (HF2 & HP2 & HA0 & _ & _ & HPS2 & HMS2 & HOFL2).
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, buf, h2, (km + 1).
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x520)%Z) (km + 1) (hb_buh g b buf h2) (P_K7 g b buf h2) L' A' regs2
        mem2 md2 Hfrm HF2 HP2).
      split; [exact HA0|].
      split; [rn_keep regs' regs 9 HRP2 Hx HK H9|].
      split; [rn_keep regs' regs 18 HRP2 Hx HK H18|].
      split; [rn_keep regs' regs 19 HRP2 Hx HK H19|].
      split; [rn_keep regs' regs 20 HRP2 Hx HK H20|].
      split.
      { split; [exact HSTD2|]. split; [exact HGRD2|].
        apply (rn_err mem mem2 HERR). intros x Hx'. apply HIMG.
        - apply img_w_iff. left. exact Hx'.
        - unfold A_STDERR, A_OFL_HEAD in *. lia. }
      split; [exists pad; exact HPS2|]. split; [exact HMS2 | exact HOFL2].
Qed.

(* Bytes of g_file_len and g_file through a callee that keeps the bytes of img_w outside the open-file head. *)
Lemma rn_gfile : forall m m' a bs, (symaddr Symbols.Plain.s_g_file_len) <= a -> a + Z.of_nat (length bs) <= (symaddr Symbols.Plain.s_environ) -> bytes_at rsegs m a bs ->
  (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs H1 H2 HB HK. apply (ss_bytes_mbyte rsegs m m'); [|exact HB].
  intros i Hi. rewrite <- (ss_segs B APIf ra empty FF). apply HK.
  - apply img_w_iff. right. left. lia.
  - unfold A_OFL_HEAD. lia.
Qed.

(* K5 p 0x1305c: the walk's end (pcap_W_x: the reader's last answer is the end loop's value); the close of the
   reader h (pcap_source_close): h is freed, the f cell holds 0 and b still holds the file; then K6. *)
Lemma seg_W : Hcut_o B APIf ra (Inv_K6 B APIf ra empty) out24 ->
  forall p, Hcut_o B APIf ra (Inv_K5 B APIf ra empty p) out24.
Proof.
  intros HX p g c (b & h & buf & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z) km (hb_bhu g b h buf) (P_K5 g p b h buf) c (out24 g) (Post_o B APIf ra g)
    HC).
  intros fx' L A regs mem md Hfrm HF HP
    (H12 & HKQ & H24 & Hp24 & HpF & H9 & H18 & H19 & H20 & H22 & HGOOD & HSB & HFL & HFP & HD & HOFL & HMS &
     (lol & lvt & lvid & pad & HPS)).
  destruct (rn_sp g km _ L A regs mem md HF) as (USP & HfS & Hp8). unfold SLOT_FRAME in HfS.
  pose proof HF as (HGV & _). pose proof (rn_gn g HGV) as HGN.
  assert (HSWB : bytes_at rsegs mem (fsp g + 40) (le4 (wz (gswz g)))).
  { replace (fsp g + 40) with (fsp g + 32 + 8) by lia. exact (rn_ps_sw _ _ _ _ _ _ _ _ HPS). }
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x458)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z) /\ getr R 10 = Z_to_bv 64 (fsp g + 32) /\
       KP [2; 3; 4; 9; 18; 19; 20] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close) /\ m' = mem)
    (out24 g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono.
    + eapply (pcap_W_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (gF g) (gsw g) (fsp g) (res_of (gsw g) (gF g) (gcap g) (gq g p)) p (gq g p) (gcap g) (gd g) b (gswz g)).
      * exact USP.
      * exact H12.
      * reflexivity.
      * exact HKQ.
      * exact H24.
      * exact Hp24.
      * exact HpF.
      * apply psn_q_skips. lia.
      * exact H9.
      * reflexivity.
      * exact (gd_range g).
      * exact HD.
      * exact H20.
      * exact (mstl_bytes _ _ _ _ _ _ _ HMS).
      * exact H22.
      * exact HFL.
      * exact HSWB.
      * exact (gswz_01 g).
      * reflexivity.
      * exact (proj2 HGN).
    + intros ms' (t0' & t1' & t2' & a1' & a3' & a4' & a5' & a6' & a7' & s8' & ->).
      do 3 eexists. split; [reflexivity|]. cbv beta.
      do 2 (split; [reflexivity|]). split; [|split; reflexivity].
      intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10 & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_bhu g b h buf) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). apply HK. cbn [In] in Hk |- *. tauto. }
    destruct HSB as (HSTD & HGRD & HERR).
    change (Z_to_bv 64 (symaddr Symbols.Plain.s_pcap_source_close)) with (Z_to_bv 64 PCAP_SOURCE_CLOSE).
    apply (ps_close_step (fx:=fx') B APIf ra empty FF (HCLOSE fx') g km [(b, gn g)] h [(buf, gbn g)] L A regs'
      mem md (fsp g + 32) (wz (gswz g)) lol lvt lvid pad b (gF g) (pos_of (gsw g) (gF g) (gcap g) (gq g p))
      (out24 g) (Post_o B APIf ra g) HF' HP).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + lia.
    + lia.
    + exact Hp8.
    + exact HPS.
    + cbn [app In]. left. reflexivity.
    + exact HMS.
    + exact HOFL.
    + exact HSTD.
    + intros L' A' regs2 mem2 md2 HF2 HP2 HRP2 _ _ HIMG HPS2 HOFL2 HSTD2 HGRD2 HBF2.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, buf, km.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x508)%Z) km (hb_bu g b buf) (P_K6 g b buf) L' A' regs2 mem2 md2
        Hfrm HF2 HP2).
      split; [rn_keep regs' regs 9 HRP2 Hx HK H9|].
      split; [rn_keep regs' regs 18 HRP2 Hx HK H18|].
      split; [rn_keep regs' regs 19 HRP2 Hx HK H19|].
      split; [rn_keep regs' regs 20 HRP2 Hx HK H20|].
      split; [exact HGOOD|].
      split.
      { split; [exact HSTD2|]. split; [exact HGRD2|].
        apply (rn_err mem mem2 HERR). intros x Hx'. apply HIMG.
        - apply img_w_iff. left. exact Hx'.
        - unfold A_STDERR, A_OFL_HEAD in *. lia. }
      split; [exact HOFL2|].
      split; [unfold q64; apply (rn_gfile mem mem2); [lia | rewrite length_le8; lia | exact HFL | exact HIMG]|].
      split; [unfold q64; apply (rn_gfile mem mem2); [lia | rewrite length_le8; lia | exact HFP | exact HIMG]|].
      split; [exact HBF2|]. exists (wz (gswz g)), lol, lvt, lvid, pad. exact HPS2.
Qed.

End RN.
