From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_reject_clean_starved_c CrsRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c fuzz_free_c PjWriteNeed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_live_c fuzz_alloc_count_c fuzz_alloc_fail_c check_reject_clean_c strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section T.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable KW : Z.
Variable F : ResForm.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HG : globals_free B API omx_G.
Hypothesis LIVEC : fuzz_alloc_live_c.fuzz_alloc_live_contract.
Hypothesis COUNTC : fuzz_alloc_count_c.fuzz_alloc_count_contract.
Hypothesis FAILC : fuzz_alloc_fail_c.fuzz_alloc_fail_contract.
Hypothesis CRCC : check_reject_clean_c.check_reject_clean_contract.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_parse_contract fx rc B API F.
Hypothesis WRITE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_write_need fx rc B API F KW.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @fuzz_free_contract fx rc B API F.

Theorem check_reject_clean_starved_holds : @check_reject_clean_starved_contract fx rc B API F KW.
Proof.
  unfold check_reject_clean_starved_contract.
  intros L A regs mem md Lam peak cnt b data size took doc tb t D Henv G10 G11 G12 G13 HKW HSZ HD0 HDH HLEN HDB
    HBLK HDNO HTOOK HDOC HLED HCNT HRES HRUN HR0 HR1 HRAN HOWN.
  pose proof Henv as (SEG & TP & ERR & GGD & GRD & PRE & SPHI & SPLO & FZ & CELLS).
  assert (DOCHI : doc <> 0 -> spZ regs <= doc /\ doc mod 8 = 0).
  { intros Hd. destruct HDOC as [E|(_ & _ & _ & H4 & H5 & _)]; [contradiction | split; [exact H5 | exact H4]]. }
  assert (DSUB : doc <> 0 -> forall a k, In (a, k) D -> In (a, k) Lam).
  { intros Hd. destruct HDOC as [E|(_ & _ & H3 & _)]; [contradiction | exact H3]. }
  assert (DOCT : doc <> 0 -> json_read jr_strtod (zb tb) = Some t /\ pj_node (ms_segs B) mem (lin Lam) doc t D /\
    Z.of_nat (length (wdoc t false)) + 1 < 2 ^ 24 /\ Z.of_nat (length (wdoc t true)) + 1 < 2 ^ 28 /\
    (depth t <= 32)%nat).
  { intros Hd. destruct HDOC as [E|(H1 & H2 & _ & _ & _ & H6 & H7 & H8)]; [contradiction|].
    split; [exact H1|]. split; [exact H2|]. split; [exact H6|]. split; [exact H7 | exact H8]. }
  assert (DBYT : Mem.bytes_at rsegs mem data tb) by (rewrite <- SEG; exact HDB).
  assert (RAN0 : Mem.bytes_at rsegs mem fuzz_alloc_ran_out_c.G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)))
    by (rewrite <- SEG; exact HRAN).
  assert (OWN0 : Mem.bytes_at rsegs mem GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0))) by (rewrite <- SEG; exact HOWN).
  set (Gq := fun bf : rf_R F =>
    (took = 0 -> bf = crs_after_doc F b cnt (zb tb) doc t) /\
    (took <> 0 -> exists tr D', crs_parse_left cnt (zb tb) took tr D' /\
       bf = crs_after_doc F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) doc t)).
  assert (GQ0 : took = 0 -> Gq (crs_after_doc F b cnt (zb tb) doc t)).
  { intros Ht. split; [intros _; reflexivity | intros Hn; contradiction]. }
  assert (GQ1 : took <> 0 -> forall tr D', crs_parse_left cnt (zb tb) took tr D' ->
    Gq (crs_after_doc F (rf_frees F (rf_run F b tr) D') (cnt + Z.of_nat (calls tr)) (zb tb) doc t)).
  { intros Ht tr D' HL. split; [intros E; contradiction | intros _; exists tr, D'; split; [exact HL | reflexivity]]. }
  assert (HRUN' : 0 < took -> room_run F b (snd (jr_run jr_strtod (zb tb) []))) by (intros Ht; apply HRUN; lia).
  eapply SR_mono.
  - exact (crs_entry_all B API KW F Gq SEG ERR GGD GRD TP AX HG LIVEC COUNTC FAILC CRCC L A regs mem md Lam peak cnt b
      data size took doc tb t D PRE SPHI SPLO HKW HLEN DBYT DOCHI DSUB HD0 HDH HSZ HBLK HDNO HTOOK DOCT
      HCNT PARSE WRITE FREE HRES HLED CELLS RAN0 OWN0
      (conj HRUN' (conj HR0 (conj HR1 (conj GQ0 GQ1)))) fx FZ G10 G11 G12 G13).
  - intros c' (fx' & L' & A' & regs' & mem' & md' & Lam' & peak' & E & FZ' & RP & RD & LG & HP & HPk & HN &
      (bf & Hrf & Hq0 & Hq1)).
    exists fx', L', A', regs', mem', md', Lam', peak'.
    split; [exact E|]. split; [exact FZ'|]. split; [exact RP|]. split; [exact RD|]. split; [exact LG|].
    split; [exact HP|]. split; [exact HPk|]. split; [exact HN|].
    split.
    + intros Ht. rewrite <- (Hq0 Ht). exact Hrf.
    + intros Ht. destruct (Hq1 Ht) as (tr & D' & HL & Eb). exists tr, D'. split; [exact HL|]. rewrite <- Eb. exact Hrf.
Qed.

End T.
