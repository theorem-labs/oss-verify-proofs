From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import CJBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require IImgU InstU.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_Scan_iface G_strtod.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Prelim FloatScan FloatScanProps NumFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.P Require FmtFp_facts3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c.
Import ListNotations.
Open Scope Z_scope.

Lemma c_segs : @CJ.RL.Reloc.RStep.img_segs IImgU.N_img = rsegs.
Proof. reflexivity. Qed.
Lemma c_strtod : @G_Scan_iface.RSTRTOD IImgU.N_img = STRTOD.
Proof. vm_compute. reflexivity. Qed.
Lemma c_errno : @G_Scan_iface.RERRNO IImgU.N_img = STRTOD_ERRNO.
Proof. vm_compute. reflexivity. Qed.
Lemma c_atp : @G_Scan_iface.RATP IImgU.N_img = STRTOD_TP.
Proof. vm_compute. reflexivity. Qed.
Lemma c_gtop : @G_Scan_iface.RGLOBALS_TOP IImgU.N_img = STRTOD_GLOBALS_TOP.
Proof. vm_compute. reflexivity. Qed.
Lemma c_got : @G_Scan_iface.G_shgetc_A.got_ssp IImgU.N_img = STRTOD_GOT_GUARD.
Proof. vm_compute. reflexivity. Qed.
Lemma c_guard : @G_Scan_iface.G_shgetc_A.ssp_guard IImgU.N_img = STRTOD_GUARD.
Proof. vm_compute. reflexivity. Qed.

Theorem strtod_holds : strtod_contract.
Proof.
  unfold strtod_contract. intros until ev.
  intros Ha0 Ha1 Htp BY NUM LEN SLOT ST GT SPH S4 SE HT HE SE8 SEP GG QQ ERR MI TM FRM.
  assert (BYT : Forall (fun c => 0 <= c < 256) txt)
    by (eapply Forall_impl; [| exact NUM]; intros c Hc; exact (NumFacts.is_numch_byte c Hc)).
  assert (NOX : Forall (fun c => c <> 120 /\ c <> 88) txt)
    by (eapply Forall_impl; [| exact NUM]; intros c Hc; exact (NumFacts.is_numch_nox c Hc)).
  destruct (FloatScanProps.scan_strtod_total_gen txt BYT NOX) as (bits & c & SC & Hc0).
  assert (BYT' : Forall (fun c => 0 <= c < 256) (txt ++ [0])).
  { apply Forall_app. split; [exact BYT | constructor; [lia | constructor]]. }
  assert (ZL : Prelim.zlength (txt ++ [0]) = Z.of_nat (length txt) + 1).
  { unfold Prelim.zlength. rewrite length_app. cbn [length]. lia. }
  assert (ZT : Prelim.zlength txt = Z.of_nat (length txt)) by reflexivity.
  pose proof InstU.N_rstrtod_wide_proof_c as RS.
  unfold G_strtod.rstrtod_wide_proof_c, G_strtod.rstrtod_wide_stmt in RS.
  specialize (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc m s e (txt ++ [0]) txt [] bits c ejunk (bv_unsigned sp - STRTOD_K) canary ev).
  rewrite c_segs, c_strtod, c_errno, c_atp, c_gtop in RS.
  unfold G_Scan_iface.G_shgetc_A.ssp_cells in RS. rewrite c_segs, c_got, c_guard in RS.
  unfold G_strtod.RIMG_LO, G_Scan_iface.RSTRTOD_DEPTH in RS.
  rewrite ZL, ZT in RS.
  unfold STRTOD_K, STRTOD_GLOBALS_TOP, STRTOD_IMG_LO in *.
  specialize (RS BY BYT' eq_refl NUM ltac:(lia) ltac:(lia)
                 (proj2 (rw_cells_iff rsegs m e [lib.Lib.Cells.C8 ejunk]) SLOT)
                 SC ST ltac:(lia) ltac:(lia) SPH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 (conj (proj2 (rw_cells_iff rsegs m STRTOD_GOT_GUARD [lib.Lib.Cells.C8 (Z_to_bv 64 STRTOD_GUARD)]) GG)
                       (proj2 (rw_cells_iff rsegs m STRTOD_GUARD [lib.Lib.Cells.C8 canary]) QQ))
                 (proj2 (rw_cells_iff rsegs m STRTOD_ERRNO [lib.Lib.Cells.C4 ev]) ERR)
                 (mem_inv_to_cj rsegs m MI TM) FRM Htp Ha0 Ha1).
  eapply evt_bridge; [| exact RS].
  intros ms' P. unfold G_Scan_iface.rstrtod_post in P.
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & ev'
                 & Hms & MU & WM & MI' & FRM' & FOK & FA0 & ST' & PEC & BY' & SSP' & ERR' & Hused).
  rewrite c_segs in *. rewrite c_errno in MU, ERR'.
  destruct (mem_inv_of_cj rsegs m' MI') as [MI2 TM2].
  unfold strtod_post.
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m', ev', c, bits.
  split; [rewrite Hms; reflexivity|].
  split; [unfold strtod_model; exact SC|].
  split; [lia|].
  split; [exact (proj1 (rw_cells_iff rsegs m' e [lib.Lib.Cells.C8 (Z_to_bv 64 (s + c))]) PEC)|].
  split; [exact FA0|].
  split; [exact FOK|].
  split; [exact FRM'|].
  split; [exact (proj1 (rw_cells_iff rsegs m' STRTOD_ERRNO [lib.Lib.Cells.C4 ev']) ERR')|].
  split; [exact MU|].
  split; [exact WM|].
  split; [exact MI2|].
  split; [exact TM2|].
  exact ST'.
Qed.
