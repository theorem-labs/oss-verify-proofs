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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PGlue PCut PImg PSegR.
Import ListNotations.
Open Scope Z_scope.

(* Glue of segment R after its last call of pcap_source_next: free(buf) (K10 -> K11), free(b) (K11 -> K12) and
   the return (K12 -> Post_o). None of these stretches stores to memory. *)

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

(* The stderr FILE and the open-file head lie in img_w: a callee that keeps the bytes of img_w keeps them. *)
Lemma err_keep : forall m m', err_ok m ->
  (forall x, img_w x -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> err_ok m'.
Proof.
  intros m m' (fl & md & HE) HK. exists fl, md.
  apply (errf_keep B APIf ra empty FF m m' fl md HE). intros i Hi. apply HK. right. right. lia.
Qed.

Lemma ofl_keep : forall m m', ofl_empty m ->
  (forall x, img_w x -> mbyte (ms_segs B) m' x = mbyte (ms_segs B) m x) -> ofl_empty m'.
Proof.
  intros m m' [[Hwf HB] _] HK. split; [split; [exact Hwf|]|].
  - apply (ss_bytes_mbyte rsegs m m'); [|exact HB]. intros i Hi.
    assert (L8 : Z.of_nat (length (Cells.cells_bytes [Cells.C8 (wz 0)])) = 8) by reflexivity.
    rewrite L8 in Hi. rewrite <- (ss_segs B APIf ra empty FF). apply HK. right. left. lia.
  - change (Z.of_nat (Cells.cells_size [Cells.C8 (wz 0)])) with 8.
    split; [unfold A_OFL_HEAD; lia|]. split; [unfold A_OFL_HEAD; lia|]. intros i Hi.
    exact (proj1 (img_w_wr m' (A_OFL_HEAD + i) ltac:(right; left; lia))).
Qed.

(* K12 0x13174: a0 = 0, the saved registers back, return to ra (pcap_R7_x). *)
Lemma seg_R7 : Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil.
Proof.
  intros g c (km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z) km [] P_K12 c (oNil g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (HERR & HOFL).
  pose proof HF as (HGV & _ & Hgp & Htp & HSV & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & HgS & _).
  pose proof (ss_stk_fsp B APIf ra empty g km [] L A regs mem md HF) as (_ & _ & _ & HfS & HSc & HS47 & HSK & Hsp).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  pose proof (ss_ra B APIf ra empty FF) as Hra.
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km [] L A regs mem md HF)) as [Hh Hl].
  assert (USP : bv_unsigned (getr regs 2) = g_S g - 160).
  { rewrite Hsp. rewrite unsigned_lit by lia. lia. }
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z)) mem md
    (fun R pc' m' => getr R 10 = Z_to_bv 64 0 /\ regs_preserved (g_regs g) R /\
       pc' = ret_pc (Z_to_bv 64 ra) /\ m' = mem)
    (oNil g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono.
    + apply (pcap_R7_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem
        (Z_to_bv 64 ra) (getr (g_regs g) 8) (getr (g_regs g) 9) (getr (g_regs g) 18) (getr (g_regs g) 19)
        (getr (g_regs g) 20) (getr (g_regs g) 21) (getr (g_regs g) 22) (getr (g_regs g) 23) (getr (g_regs g) 24)
        (getr (g_regs g) 25) (getr (g_regs g) 26) (getr (g_regs g) 27) (g_S g) USP HSV).
    + intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
      split; [reflexivity|]. split; [|split; reflexivity].
      intros r Hr. ss_cs_split r Hr; try reflexivity.
      * transitivity (Z_to_bv 64 (g_S g)); [reflexivity | symmetry; exact HgS].
      * exact Hgp.
      * exact Htp.
  - intros R pc' m' regs' (H10 & HRP & -> & ->) Hx.
    rewrite (ss_ret_pc_ra ra Hra). unfold oNil. apply SRO_ret.
    apply (post_FR B APIf ra empty FF g km L A regs regs' mem md fx' HF HP).
    + rewrite (ss_getr_eqv _ _ _ Hx). exact H10.
    + intros r Hr. rewrite (ss_getr_eqv _ _ _ Hx). exact (HRP r Hr).
    + exact (ofl_back B APIf ra empty FF g mem HGV HOFL).
    + destruct HERR as (fl & mdv & HE). exact (GI_of_errf O mem fl mdv HE).
    + exact Hfrm.
Qed.

(* K11 0x1316c: free(b) (pcap_R6_x), then K12. *)
Lemma seg_R6 : Hcut_o B APIf ra (Inv_K12 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K11 B APIf ra empty) oNil.
Proof.
  intros HX g c (b & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z) km (hb_b g b) (P_K11 b) c (oNil g) (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H20 & HSB & HOFL).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z) /\ getr R 10 = getr regs 20 /\
       KP [2; 3; 4] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_free) /\ m' = mem)
    (oNil g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono; [apply pcap_R6_x|].
    intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
    split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
    intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10 & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_b g b) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). exact (HK k Hk). }
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step B APIf ra empty FF g km [] b (gn g) [] L A regs' mem md (oNil g) (Post_o B APIf ra g)
      HF' HP).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx), H10. exact H20.
    + exact (proj1 HSB).
    + intros L' A' regs2 mem2 md2 HF2 HP2 _ _ HIMG _ _.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists km.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x570)%Z) km [] P_K12 L' A' regs2 mem2 md2 Hfrm HF2 HP2).
      split; [exact (err_keep mem mem2 (proj2 (proj2 HSB)) HIMG) | exact (ofl_keep mem mem2 HOFL HIMG)].
Qed.

(* K10 0x1315c: free(buf) (pcap_R5_x), then K11. *)
Lemma seg_R5 : Hcut_o B APIf ra (Inv_K11 B APIf ra empty) oNil ->
  Hcut_o B APIf ra (Inv_K10 B APIf ra empty) oNil.
Proof.
  intros HX g c (b & buf & km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z) km (hb_bu g b buf) (P_K10 g b buf) c (oNil g) (Post_o B APIf ra g)
    HC).
  intros fx' L A regs mem md Hfrm HF HP (Ha0 & H18 & H20 & HSB & HOFL).
  destruct (sg_md B APIf L A mem md (FR_MR B APIf ra empty g km _ L A regs mem md HF)) as [Hh Hl].
  apply (ss_kA_run0_o (fx:=fx') B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x558)%Z)) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z) /\ getr R 10 = getr regs 18 /\
       KP [2; 3; 4; 20] regs R /\ pc' = Z_to_bv 64 (symaddr Symbols.Plain.s_free) /\ m' = mem)
    (oNil g) (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of. eapply evt_mono; [apply pcap_R5_x; exact Ha0|].
    intros ms' ->. do 3 eexists. split; [reflexivity|]. cbv beta.
    split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity].
    intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[<-|[<-|[]]]]]; reflexivity.
  - intros R pc' m' regs' (H1 & H10 & HK & -> & ->) Hx.
    assert (HF' : FR B APIf ra empty g km (hb_bu g b buf) L A regs' mem md).
    { apply (ss_FR_hb B APIf ra empty FF g km _ L A regs mem md regs' mem HF HP);
        [| intros x _ _; reflexivity | apply wmono_refl].
      intros k Hk. rewrite (ss_getr_eqv _ _ _ Hx). apply HK. cbn [In] in Hk |- *. tauto. }
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step B APIf ra empty FF g km [(b, gn g)] buf (gbn g) [] L A regs' mem md (oNil g)
      (Post_o B APIf ra g) HF' HP).
    + rewrite (ss_getr_eqv _ _ _ Hx), H1. apply ret_ok_even. rewrite unsigned_lit by lia. reflexivity.
    + rewrite (ss_getr_eqv _ _ _ Hx), H10. exact H18.
    + exact (proj1 HSB).
    + intros L' A' regs2 mem2 md2 HF2 HP2 HRP2 _ HIMG HSTD HGRD.
      rewrite (ss_getr_eqv _ _ _ Hx), H1. apply HX. exists b, km.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Plain.s_LLVMFuzzerTestOneInput + 0x568)%Z) km (hb_b g b) (P_K11 b) L' A' regs2 mem2 md2 Hfrm HF2 HP2).
      split.
      { transitivity (getr regs' 20); [exact (HRP2 20 ltac:(unfold callee_saved; lia))|].
        rewrite (ss_getr_eqv _ _ _ Hx). transitivity (getr regs 20); [exact (HK 20 ltac:(ss_in)) | exact H20]. }
      split; [|exact (ofl_keep mem mem2 HOFL HIMG)].
      split; [exact HSTD|]. split; [exact HGRD|]. exact (err_keep mem mem2 (proj2 (proj2 HSB)) HIMG).
Qed.

End R.
