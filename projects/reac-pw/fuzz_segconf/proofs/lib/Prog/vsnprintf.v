From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_pad G_pop_arg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require G_sn_write G_vsnprintf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.I Require InstFmtP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import printf_facts_c snprintf_c printf_model_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import vsnprintf_c snprintf.
Import ListNotations.
Open Scope Z_scope.

(** vsnprintf_holds: the unit-level vsnprintf contract from the closed relocatable statement
    [InstFmtP.N_vsnprintf] (G_vsnprintf.vsnprintf_x_stmt on segconf's plain image), on the pattern of
    snprintf.v's snprintf_stk_holds (which does the same from InstFmtP.N_snprintf). *)

Lemma pm_arg_to_g : forall m S lo D n dn r a,
  pm_arg_ok m S lo D n r a -> lo + 232 <= S -> Z.of_nat dn <= n ->
  @PI.arg_ok InstFmtP.N_img_fmt lo lo 0 lo 0 D (Z.of_nat dn) m lo S lo r a.
Proof.
  intros m S lo D n dn r [s|i|u|g|u] H HS Hd; cbn [pm_arg_ok] in H.
  - exact (str_ok m S lo D n dn r s H HS Hd).
  - exact H.
  - exact H.
  - destruct H.
  - exact H.
Qed.

Lemma pm_args_to_g : forall m S lo D n dn args rs,
  pm_args_ok m S lo D n rs args -> lo + 232 <= S -> Z.of_nat dn <= n ->
  @PI.args_ok InstFmtP.N_img_fmt lo lo 0 lo 0 D (Z.of_nat dn) m lo S lo rs args.
Proof.
  intros m S lo D n dn args. induction args as [|a args IH]; intros rs H HS Hd; [destruct rs; exact I|].
  destruct rs as [|r rs]; [destruct H|]. destruct H as [H1 H2].
  split; [exact (pm_arg_to_g m S lo D n dn r a H1 HS Hd) | exact (IH rs H2 HS Hd)].
Qed.

Lemma post_of_cj_r : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D n (dn : nat) r o m canary ms',
  1 <= n -> Z.of_nat dn = Z.min (Z.of_nat (length o)) (n - 1) + 1 ->
  @G_vsnprintf.vsnprintf_x_post InstFmtP.N_img_fmt ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn
    (map (Z_to_bv 8) (firstn (Z.to_nat (n - 1)) o) ++ [Z_to_bv 8 0]) r lo canary m ms' ->
  printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo D r (firstn (Z.to_nat (n - 1)) o) m ms'.
Proof.
  intros until ms'. intros Hn Hdn P. unfold G_vsnprintf.vsnprintf_x_post in P.
  destruct P as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & m'
                 & Hms & MU & WM & MI & FRM & FOK & ST & _ & DST).
  destruct (mem_inv_of_cj rsegs m' MI) as [MI2 TM2].
  unfold printf_post. exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', m'.
  split; [exact Hms|].
  split; [replace (D + Z.of_nat (length (firstn (Z.to_nat (n - 1)) o)) + 1) with (D + Z.of_nat dn)
            by (rewrite length_firstn; lia); exact MU|].
  split; [exact WM|]. split; [exact MI2|]. split; [exact TM2|]. split; [exact FRM|]. split; [exact FOK|].
  split; [exact ST|].
  destruct DST as [[_ B] _]. cbn [CJ.Lib.Cells.cells_bytes CJ.Lib.Cells.cbytes] in B. rewrite app_nil_r in B.
  unfold pf_bytes. rewrite map_app. exact B.
Qed.

Lemma fmt_bytes0 : forall fmt : list Z, Forall (fun c => 0 <= c < 256) fmt -> Forall (fun c => 0 <= c < 256) (fmt ++ [0]).
Proof. intros fmt H. apply Forall_app. split; [exact H | constructor; [lia | constructor]]. Qed.

Lemma c_vsnprintf : @RStep.sym InstFmtP.N_img_fmt 0x7f000200 = VSNPRINTF.
Proof. vm_compute. reflexivity. Qed.

Theorem vsnprintf_holds : vsnprintf_contract.
Proof.
  unfold vsnprintf_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
         fmt slots args r o junk.
  cbv zeta.
  intros BYF RLO REND HF P1 VAA QVA VAHI AOK MODEL DST Hn D0 DLO IMGF ST LO IMGLO SHI FRM MI TM GG GQ.
  assert (Edn : exists dn : nat, Z.of_nat dn = Z.min (Z.of_nat (length o)) (bv_unsigned a1 - 1) + 1)
    by (exists (Z.to_nat (Z.min (Z.of_nat (length o)) (bv_unsigned a1 - 1) + 1)); lia).
  destruct Edn as [dn Hdn].
  pose proof (task_bound m (bv_unsigned a0) _ junk MI TM DST ltac:(lia)) as DT.
  pose proof (img_free_bound (bv_unsigned a0) (bv_unsigned a1) ltac:(lia) ltac:(lia) IMGF) as IF.
  pose proof (proj2 (rw_cells_iff rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk]) DST) as DST1.
  cbn [map cell_to] in DST1.
  replace (Z.to_nat (bv_unsigned a1)) with (dn + (Z.to_nat (bv_unsigned a1) - dn))%nat in DST1 by lia.
  destruct (G_sn_write.rw_CB_split _ _ _ _ _ _ DST1) as [DSTd _].
  unfold VSNPRINTF_K, RO_LO, RO_END in *.
  pose proof (pm_args_to_g m (bv_unsigned sp) lo (bv_unsigned a0) (bv_unsigned a1) dn args slots AOK
                ltac:(lia) ltac:(lia)) as AOKg.
  pose proof (ssp_of_bytes m canary GG GQ) as SSP.
  pose proof (mem_inv_to_cj rsegs m MI TM) as MIc.
  pose proof (fmt_bytes0 fmt HF) as HF0.
  pose proof InstFmtP.N_vsnprintf as RS. unfold G_vsnprintf.vsnprintf_x_stmt in RS.
  specialize (RS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a3) dn (firstn dn junk) (fmt ++ [0])
                 slots args lo canary r o).
  cbv zeta in RS. rewrite c_vsnprintf, c_gtop in RS. unfold PI.STATIC_SPLIT, G_vsnprintf.VSN_DEPTH in RS.
  pose proof c_pages as PG. unfold IMG_END, IMG_PAGES, TASK_SIZE in *.
  specialize (RS (eq_sym (Z_to_bv_bv_unsigned a0)) (eq_sym (Z_to_bv_bv_unsigned a1)) (eq_sym (Z_to_bv_bv_unsigned a2))
                 (eq_sym (Z_to_bv_bv_unsigned a3))
                 DSTd Hdn BYF HF0 P1 VAA AOKg MODEL Hn ST ltac:(lia) ltac:(lia) SHI SSP MIc FRM
                 ltac:(unfold Prelim.zlength; rewrite length_app; cbn [length]; lia) RLO QVA
                 ltac:(unfold Prelim.zlength; lia) D0 ltac:(lia) ltac:(unfold Prelim.zlength; lia) ltac:(lia)).
  eapply evt_bridge; [| exact RS].
  intros ms' P. exact (post_of_cj_r ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo (bv_unsigned a0) (bv_unsigned a1)
                         dn r o m canary ms' (proj1 Hn) Hdn P).
Qed.
