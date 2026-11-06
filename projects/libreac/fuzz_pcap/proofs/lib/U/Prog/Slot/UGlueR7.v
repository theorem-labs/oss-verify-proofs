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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PGlue UCut UGlueT USegR7.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USROcf PInvCF.
Import ListNotations.
Open Scope Z_scope.

(* Glue of R7: from 0x130d4 (every block of the call freed, the reader closed) the epilogue returns to ra with
   a0 = 0 and the callee-saved registers of the entry: the slot's post. *)

Section R7.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma ug_saved : forall g, saved_bytes ra g =
  ubs_saved (wz ra) (getr (g_regs g) 8) (getr (g_regs g) 9) (getr (g_regs g) 18) (getr (g_regs g) 19)
    (getr (g_regs g) 20) (getr (g_regs g) 21) (getr (g_regs g) 22) (getr (g_regs g) 23) (getr (g_regs g) 24)
    (getr (g_regs g) 25) (getr (g_regs g) 26) (getr (g_regs g) 27).
Proof. reflexivity. Qed.

Lemma ug_R7 : HCT B APIf ra (Inv_K1310c B APIf ra empty).
Proof.
  intros g c (km & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) km [] _ c [] (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (Hstd & Hgd & (fl & md' & Herr) & Hofl).
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & _ & HMI & _ & HM & _).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
  destruct (sg_md B APIf L A mem md HM) as (Hh & Hl).
  pose proof (sg_GV_S _ _ g HGV) as (HgS & HSc).
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  rewrite ug_saved in Hsv.
  replace (g_S g - 104) with (fsp g + 72) in Hsv by (unfold fsp, SLOT_FRAME; lia).
  set (R0 := g_regs g) in *.
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    m' = mem /\ pc' = wz ra /\ getr R 10 = wz 0 /\ getr R 2 = wz (fsp g + 176) /\ getr R 3 = getr regs 3 /\
    getr R 4 = getr regs 4 /\
    forall r, (r = 8 \/ r = 9 \/ 18 <= r <= 27) -> getr R (Z_to_bv 5 r) = getr R0 (Z_to_bv 5 r)).
  apply (@ss_kA_run0_o fx' B APIf SH SK ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) mem md Q [] (Post_o B APIf ra g) Hh Hl).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_R7_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem
      (fsp g) _ _ _ _ _ _ _ _ _ _ _ _ _ USP Hsv)|].
    intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [unfold wz; rewrite (ss_ret_pc_ra ra (ss_ra B APIf ra empty FF)); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact eq_refl|].
    intros r Hr. destruct Hr as [->|[->|Hr]]; [reflexivity | reflexivity |].
    assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
  - intros R pc' m' regs' (-> & -> & G10 & G2 & G3 & G4 & GS) XR.
    apply SRO_ret. unfold wz.
    apply (post_FR B APIf ra empty FF g km L A regs regs' mem md fx' HF HP).
    + rewrite (ss_getr_eqv _ _ 10 XR). exact G10.
    + intros r Hr. unfold callee_saved in Hr. rewrite (ss_getr_eqv _ _ _ XR).
      destruct Hr as [->|[->|[->|Hr]]].
      * etransitivity; [exact G2|].
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HGV)))))))) as E.
        symmetry. etransitivity; [exact E|]. unfold wz, fsp, SLOT_FRAME. f_equal. lia.
      * etransitivity; [exact G3 | exact Hgp].
      * etransitivity; [exact G4 | exact Htp].
      * apply GS. exact Hr.
    + exact (ofl_back B APIf ra empty FF g mem HGV Hofl).
    + exact (GI_of_errf mem fl md' 0 Herr).
    + exact Hfrm.
Qed.

(* The cut-free twin of ug_R7. *)
Lemma ug_R7_cf : Hcut_cf B APIf ra (Inv_K1310c B APIf ra empty) (fun _ => []).
Proof.
  intros g c HCAP (km & HC).
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) km [] _ c [] (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (Hstd & Hgd & (fl & md' & Herr) & Hofl).
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & _ & HMI & _ & HM & _).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
  destruct (sg_md B APIf L A mem md HM) as (Hh & Hl).
  pose proof (sg_GV_S _ _ g HGV) as (HgS & HSc).
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  rewrite ug_saved in Hsv.
  replace (g_S g - 104) with (fsp g + 72) in Hsv by (unfold fsp, SLOT_FRAME; lia).
  set (R0 := g_regs g) in *.
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    m' = mem /\ pc' = wz ra /\ getr R 10 = wz 0 /\ getr R 2 = wz (fsp g + 176) /\ getr R 3 = getr regs 3 /\
    getr R 4 = getr regs 4 /\
    forall r, (r = 8 \/ r = 9 \/ 18 <= r <= 27) -> getr R (Z_to_bv 5 r) = getr R0 (Z_to_bv 5 r)).
  apply (@ss_kA_run0_o_cf fx' B APIf SH SK ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) mem md Q [] (Post_o B APIf ra g)
    Hh Hl).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_R7_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr mem
      (fsp g) _ _ _ _ _ _ _ _ _ _ _ _ _ USP Hsv)|].
    intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [unfold wz; rewrite (ss_ret_pc_ra ra (ss_ra B APIf ra empty FF)); reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [exact eq_refl|].
    intros r Hr. destruct Hr as [->|[->|Hr]]; [reflexivity | reflexivity |].
    assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
  - intros R pc' m' regs' (-> & -> & G10 & G2 & G3 & G4 & GS) XR.
    apply SROcf_ret. unfold wz.
    apply (post_FR B APIf ra empty FF g km L A regs regs' mem md fx' HF HP).
    + rewrite (ss_getr_eqv _ _ 10 XR). exact G10.
    + intros r Hr. unfold callee_saved in Hr. rewrite (ss_getr_eqv _ _ _ XR).
      destruct Hr as [->|[->|[->|Hr]]].
      * etransitivity; [exact G2|].
        pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HGV)))))))) as E.
        symmetry. etransitivity; [exact E|]. unfold wz, fsp, SLOT_FRAME. f_equal. lia.
      * etransitivity; [exact G3 | exact Hgp].
      * etransitivity; [exact G4 | exact Htp].
      * apply GS. exact Hr.
    + exact (ofl_back B APIf ra empty FF g mem HGV Hofl).
    + exact (GI_of_errf mem fl md' 0 Herr).
    + exact Hfrm.
Qed.

End R7.
