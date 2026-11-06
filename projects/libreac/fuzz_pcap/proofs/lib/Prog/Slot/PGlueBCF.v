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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel pcap_source_struct
  pcap_source_next_lib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PInvCF PSROcf PContractCF PCut PImg PSegB PGlueR PGlueRCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Glue of segment B (0x12cc4, after pcap_source_open): an accepted file goes to malloc(buf) and K3, a refused
   one to free(b) and K12. Segment B does not store to memory. *)

(* The reader's cells: the f word at their start, the sw word at offset 8, 24 bytes in all. *)
Lemma gl_ps_f : forall m a f sw olen vtag vid pad,
  rw_cells rsegs m a (ps_cells f sw olen vtag vid pad) -> bytes_at rsegs m a (le8 f).
Proof.
  intros m a f sw olen vtag vid pad [[_ Hb] _]. unfold ps_cells in Hb.
  cbn [Cells.cells_bytes Cells.cbytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma gl_ps_sw : forall m a f sw olen vtag vid pad,
  rw_cells rsegs m a (ps_cells f sw olen vtag vid pad) -> bytes_at rsegs m (a + 8) (le4 sw).
Proof.
  intros m a f sw olen vtag vid pad [[_ Hb] _]. unfold ps_cells in Hb.
  cbn [Cells.cells_bytes Cells.cbytes] in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite length_le8 in Hb. change (Z.of_nat 8) with 8 in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma gl_ps_size : forall f sw olen vtag vid pad, Z.of_nat (Cells.cells_size (ps_cells f sw olen vtag vid pad)) = 24.
Proof. reflexivity. Qed.

(* Cells whose bytes are kept and which stay writable. *)
Lemma gl_rw_keep : forall m m' a cs, rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) ->
     mbyte rsegs m' (a + i) = mbyte rsegs m (a + i) /\ writable_at rsegs m' (a + i)) ->
  rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf HB] (W1 & W2 & _)] HK. split; [split; [exact Hwf|]|].
  - apply (ss_bytes_mbyte rsegs m m'); [|exact HB]. intros i Hi.
    rewrite (Cells.cells_bytes_length cs Hwf) in Hi. exact (proj1 (HK i Hi)).
  - split; [exact W1|]. split; [exact W2|]. intros i Hi. exact (proj2 (HK i Hi)).
Qed.

(* The reader's FILE (1304 bytes at h) and the file copy at b, kept. *)
Lemma gl_mstl_keep : forall (m m' : word -> option byte) h b F p pv nx,
  (forall i, 0 <= i < 1304 -> mbyte rsegs m' (h + i) = mbyte rsegs m (h + i) /\ writable_at rsegs m' (h + i)) ->
  (forall i, 0 <= i < Z.of_nat (length F) -> mbyte rsegs m' (b + i) = mbyte rsegs m (b + i)) ->
  mstl m h b F p pv nx -> mstl m' h b F p pv nx.
Proof.
  intros m m' h b F p pv nx HH HB HM.
  destruct (mstl_frame m h b F p pv nx HM) as (cs & Hcs & HC & HBF & _ & _ & K).
  apply K.
  - apply (gl_rw_keep m m' h cs HC). intros i Hi. rewrite Hcs in Hi. apply HH. lia.
  - exact (ss_bytes_mbyte rsegs m m' b F HB HBF).
Qed.

Section B.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Hypothesis HMALCF : forall fx' : YK11.FPState, @malloc_contract_cf fx' rc B (APIf rc).
Hypothesis HFREECF : forall fx' : YK11.FPState, @free_contract_cf fx' rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).

Lemma gl_gn : forall g, GV B empty g -> 0 <= gn g < 2 ^ 26.
Proof.
  intros g (Hn & _). unfold gn, gF. unfold g_n in Hn. destruct (g_in g) as [|d F]; cbn [tl length] in *; lia.
Qed.

(* Bytes of img_w across a callee that keeps img_w. *)
Lemma gl_img_bytes : forall m m' a bs, (forall x, img_w x -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> img_w (a + i)) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs HK HW HB. apply (ss_bytes_mbyte rsegs m m'); [|exact HB].
  intros i Hi. rewrite <- (ss_segs B APIf ra empty FF). exact (HK _ (HW i Hi)).
Qed.

Lemma gl_q64_keep : forall m m' a v, (forall x, img_w x -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  (symaddr Symbols.Plain.s_g_file_len) <= a -> a + 8 <= (symaddr Symbols.Plain.s_environ) -> q64 m a v -> q64 m' a v.
Proof.
  intros m m' a v HK H1 H2 HB. unfold q64 in *. apply (gl_img_bytes m m' a _ HK); [|exact HB].
  intros i Hi. rewrite length_le8 in Hi. apply (proj2 (img_w_iff _)). right. left. lia.
Qed.

Lemma gl_ofl_keep : forall m m' v, rw_cells rsegs m A_OFL_HEAD [Cells.C8 v] ->
  (forall x, img_w x -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) ->
  rw_cells rsegs m' A_OFL_HEAD [Cells.C8 v].
Proof.
  intros m m' v HC HK. apply (gl_rw_keep m m' _ _ HC). intros i Hi.
  change (Z.of_nat (Cells.cells_size [Cells.C8 v])) with 8 in Hi.
  assert (Hw : img_w (A_OFL_HEAD + i)) by (right; left; lia).
  split; [rewrite <- (ss_segs B APIf ra empty FF); exact (HK _ Hw) | exact (proj1 (img_w_wr m' _ Hw))].
Qed.

(* A heap block of the cut, kept by a callee, stays writable (ss_hb_blk on the callee's frame record; fx0 is any
   FP state, ss_hb_blk reads the allocator facts at one). *)
Lemma gl_hb_keep : forall (fx0 : YK11.FPState) g km hb L A regs mem md (m0 : word -> option byte) a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb ->
  (forall i, 0 <= i < k -> mbyte (ms_segs B) mem (a + i) = mbyte (ms_segs B) m0 (a + i)) ->
  forall i, 0 <= i < k -> mbyte rsegs mem (a + i) = mbyte rsegs m0 (a + i) /\ writable_at rsegs mem (a + i).
Proof.
  intros fx0 g km hb L A regs mem md m0 a k HF HP Hin HK i Hi.
  destruct (ss_hb_blk (fx:=fx0) B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (HW & _).
  rewrite <- (ss_segs B APIf ra empty FF). split; [exact (HK i Hi) | exact (proj1 (HW i Hi))].
Qed.

(* Cells of the slot's frame, kept by a callee, stay writable (the frame record's stack window). *)
Lemma gl_fr_keep : forall g km hb L A regs mem md (m0 : word -> option byte),
  FR B APIf ra empty g km hb L A regs mem md ->
  (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem x = mbyte (ms_segs B) m0 x) ->
  forall a cs, fsp g <= a -> a + Z.of_nat (Cells.cells_size cs) <= g_S g ->
  rw_cells rsegs m0 a cs -> rw_cells rsegs mem a cs.
Proof.
  intros g km hb L A regs mem md m0 HF HK a cs H1 H2 HC.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin).
  apply (gl_rw_keep m0 mem a cs HC). intros i Hi. rewrite <- (ss_segs B APIf ra empty FF).
  split; [apply HK; lia | apply Hwin; unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *; lia].
Qed.

(* K2g 0x12cc4: pcap_B_x for an accepted file, then malloc(gbn g) (ra 0x12d74), then K3. *)
Lemma seg_B_good_cf : Hcut_cf B APIf ra (Inv_K3 B APIf ra empty) oOUT ->
  Hcut_cf B APIf ra (Inv_K2g B APIf ra empty) oOUT.
Proof.
  intros HX g c HCAP (b & h & km & HC).
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) km (hb_bh g b h) (P_K2g g b h) c (oOUT g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H20 & H22 & HG & HSB & HQ0 & HQ8 & HPS & HMS & HO1).
  pose proof HF as (HGV & _).
  pose proof (gl_gn g HGV) as Hgn. pose proof (gd_range g) as Hgd. pose proof (gcap_range g) as Hcap.
  pose proof (ss_stk_fsp B APIf ra empty g km _ L A regs mem md HF) as (_ & _ & _ & HfS & HSc & HS47 & HSK & Hsp).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite Hsp; apply unsigned_lit; lia).
  destruct HPS as (pad & HPS).
  pose proof (gl_ps_sw mem _ _ _ _ _ _ _ HPS) as HSW.
  replace (fsp g + 32 + 8) with (fsp g + 40) in HSW by lia.
  apply (ss_kA_run0_o_cf (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z) /\ getr R 10 = Z_to_bv 64 (gbn g) /\
       getr R 9 = Z_to_bv 64 (gcap g) /\ KP [2; 3; 4; 8; 20; 22] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_malloc) /\ m' = mem)
    (oOUT g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono.
    + apply (pcap_B_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (gF g) (fsp g) b 0 (gd g)
        USP H10 H20 (mstl_bytes mem h b (gF g) 24 _ _ HMS) H22 HQ0 (proj2 Hgn) H8 Hgd).
      left. split; [exact HG|]. split; [reflexivity | exact HSW].
    + intros ms' [(_ & a1' & a2' & a3' & a4' & a5' & ->) | (HG' & _)]; [|congruence].
      do 3 eexists. split; [reflexivity|]. cbv beta.
      split; [reflexivity|]. split.
      { transitivity (wz (if gd g =? 0 then 1 else 8 * gd g)); [reflexivity|].
        unfold wz, gbn, gcap. f_equal. destruct (Z.eqb_spec (gd g) 0); lia. }
      split; [reflexivity|]. split; [|split; reflexivity].
      intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10' & H9 & HK & -> & ->) Hx.
    assert (KR : forall r, In r [2; 3; 4; 8; 20; 22] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. rewrite (ss_getr_eqv _ _ _ Hx). exact (HK r Hr). }
    assert (HF' : FR B APIf ra empty g km (hb_bh g b h) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. apply KR. cbn [In] in Hk |- *. tauto. }
    rewrite <- (ss_malloc_pc B APIf ra empty FF).
    apply (ss_malloc_step_cf B APIf ra empty FF HMALCF LIMLAW g km (hb_bh g b h) L A regs' mem md (gbn g) (oOUT g)
      (Post_o B APIf ra g) HCAP HF' HP).
    + cbn [hb_bh length]. lia.
    + unfold hb_bh, hb_bytes. cbn [map fold_right snd]. lia.
    + lia.
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10'.
    + exact (proj1 HSB).
    + intros L' A' regs2 mem2 md2 buf HF2 HP2 HRP2 H10b Hbuf HFRM HHB HIMG HSTD HGRD.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX; [exact HCAP|]. exists b, h, buf, (km + 1).
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x170)%Z) (km + 1) (hb_bhu g b h buf) (P_K3 g b h buf) L' A' regs2 mem2
        md2 Hfrm HF2 HP2).
      assert (KS : forall r, In r [8; 20; 22] -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
      { intros r Hr. transitivity (getr regs' (Z_to_bv 5 r)).
        - apply HRP2. unfold callee_saved. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; lia.
        - apply KR. cbn [In] in Hr |- *. tauto. }
      split; [exact H10b|]. split; [exact Hbuf|].
      split; [transitivity (getr regs 8); [exact (KS 8 ltac:(ss_in)) | exact H8]|].
      split.
      { transitivity (getr regs' 9); [exact (HRP2 9 ltac:(unfold callee_saved; lia))|].
        rewrite (ss_getr_eqv _ _ _ Hx). exact H9. }
      split; [transitivity (getr regs 20); [exact (KS 20 ltac:(ss_in)) | exact H20]|].
      split; [transitivity (getr regs 22); [exact (KS 22 ltac:(ss_in)) | exact H22]|].
      split; [exact HG|].
      split.
      { split; [exact HSTD|]. split; [exact HGRD|].
        exact (err_keep B APIf ra empty FF mem mem2 (proj2 (proj2 HSB)) HIMG). }
      split; [exact (gl_q64_keep mem mem2 (symaddr Symbols.Plain.s_g_file_len) (gn g) HIMG ltac:(lia) ltac:(lia) HQ0)|].
      split; [exact (gl_q64_keep mem mem2 (symaddr Symbols.Plain.s_g_file) b HIMG ltac:(lia) ltac:(lia) HQ8)|].
      split.
      { exists pad. apply (gl_fr_keep g _ _ L' A' regs2 mem2 md2 mem HF2 HFRM).
        - unfold fsp, SLOT_FRAME in *. lia.
        - rewrite gl_ps_size. unfold fsp, SLOT_FRAME in *. lia.
        - exact HPS. }
      split.
      { apply (gl_mstl_keep mem mem2 h b (gF g) 24 (wz 0) (wz 0)); [| |exact HMS].
        - exact (gl_hb_keep fx' g _ _ L' A' regs2 mem2 md2 mem h 1304 HF2 HP2 ltac:(unfold hb_bh; cbn [app]; ss_in)
            (fun i Hi => HHB h 1304 i ltac:(unfold hb_bh; ss_in) Hi)).
        - intros i Hi. rewrite <- (ss_segs B APIf ra empty FF).
          exact (HHB b (gn g) i ltac:(unfold hb_bh; ss_in) Hi). }
      exact (gl_ofl_keep mem mem2 (wz h) HO1 HIMG).
Qed.

(* K2r 0x12cc4: pcap_B_x for a refused file, then free(b) (ra 0x13174), then K12; the output is []. *)
Lemma seg_B_ref_cf : Hcut_cf B APIf ra (Inv_K12 B APIf ra empty) oNil ->
  Hcut_cf B APIf ra (Inv_K2r B APIf ra empty) oOUT.
Proof.
  intros HX g c HCAP (b & km & HC).
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z) km (hb_b g b) (P_K2r g b) c (oOUT g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & H8 & H20 & H22 & HG & HSB & HOFL & HQ0 & HBF & HPS).
  assert (EO : oOUT g = oNil g) by (unfold oOUT, oNil; exact (OUT_refused g HG)).
  rewrite EO.
  pose proof HF as (HGV & _).
  pose proof (gl_gn g HGV) as Hgn. pose proof (gd_range g) as Hgd.
  pose proof (ss_stk_fsp B APIf ra empty g km _ L A regs mem md HF) as (_ & _ & _ & HfS & HSc & HS47 & HSK & Hsp).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite Hsp; apply unsigned_lit; lia).
  destruct HPS as (sw & olen & vtag & vid & pad & HPS).
  pose proof (gl_ps_f mem _ _ _ _ _ _ _ HPS) as HF0.
  apply (ss_kA_run0_o_cf (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0xc0)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z) /\ getr R 10 = Z_to_bv 64 b /\
       KP [2; 3; 4] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_free) /\ m' = mem)
    (oNil g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono.
    + apply (pcap_B_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (gF g) (fsp g) b (-1)
        (gd g) USP H10 H20 HBF H22 HQ0 (proj2 Hgn) H8 Hgd).
      right. split; [exact HG|]. split; [reflexivity | exact HF0].
    + intros ms' [(HG' & _) | (_ & a1' & a2' & a3' & a4' & a5' & ->)]; [congruence|].
      do 3 eexists. split; [reflexivity|]. cbv beta.
      split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
      intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10' & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_b g b) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). exact (HK k Hk). }
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step_cf B APIf ra empty FF HFREECF g km [] b (gn g) [] L A regs' mem md (oNil g) (Post_o B APIf ra g)
      HF' HP).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10'.
    + exact (proj1 HSB).
    + intros L' A' regs2 mem2 md2 HF2 HP2 _ _ HIMG _ _.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX; [exact HCAP|]. exists km.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z) km [] P_K12 L' A' regs2 mem2 md2 Hfrm HF2 HP2).
      split; [exact (err_keep B APIf ra empty FF mem mem2 (proj2 (proj2 HSB)) HIMG)
             | exact (ofl_keep B APIf ra empty FF mem mem2 HOFL HIMG)].
Qed.

End B.
