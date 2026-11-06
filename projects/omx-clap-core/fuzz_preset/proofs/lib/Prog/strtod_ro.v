From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm RoAdapt RoAdaptCJ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import strtod_c strtod_ro_c strtod.
Import ListNotations.
Open Scope Z_scope.

Lemma strtod_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Ltac not_ro_lit :=
  let i := fresh "i" in let Hi := fresh "Hi" in let Hc := fresh "Hc" in
  intros i Hi;
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia;
  repeat (destruct Hc as [Hc | Hc]; [subst i; vm_compute; reflexivity |]);
  subst i; vm_compute; reflexivity.

Ltac cell_bound := cbn [cells_size csize Nat.add];
  unfold STRTOD_GOT_GUARD, STRTOD_GUARD, STRTOD_ERRNO, TASK_SIZE in *; lia.

Theorem strtod_ro_of : strtod_contract -> strtod_ro_contract.
Proof.
  intros H. unfold strtod_ro_contract. intros until ev.
  intros Ha0 Ha1 Htp BY NUM LEN SLOT SLOTN ST STN GT SPT S4 STE SPL SEL ETE SEP GG QQ ERR HRO FRM.
  pose proof (MemNorm.mem_rel_cj_normalize rsegs m HRO) as REL.
  pose proof (MemNorm.mem_inv_cj_normalize rsegs m) as MCJ.
  assert (NG : RoAdapt.not_ro rsegs STRTOD_GOT_GUARD 8) by not_ro_lit.
  assert (NQ : RoAdapt.not_ro rsegs STRTOD_GUARD 8) by not_ro_lit.
  assert (NE : RoAdapt.not_ro rsegs STRTOD_ERRNO 4) by not_ro_lit.
  assert (BY0 : bytes_at rsegs (MemNorm.normalize_cj rsegs m) s (map (Z_to_bv 8) (txt ++ [0]))).
  { apply MemNorm.bytes_at_normalize_cj_low; [exact HRO | | exact BY].
    rewrite length_map, length_app. cbn [length]. lia. }
  pose proof (RoAdaptCJ.rw_cells_norm_cj rsegs m e [C8 ejunk] HRO ltac:(cbn [cells_size csize Nat.add]; lia)
                SLOTN SLOT) as SLOT0.
  assert (STN' : RoAdapt.not_ro rsegs (bv_unsigned sp - STRTOD_K) (bv_unsigned sp - (bv_unsigned sp - STRTOD_K))).
  { replace (bv_unsigned sp - (bv_unsigned sp - STRTOD_K)) with STRTOD_K by lia. exact STN. }
  pose proof (RoAdaptCJ.stk_norm_cj rsegs m _ _ HRO SPT STN' ST) as ST0.
  pose proof (RoAdaptCJ.rw_cells_norm_cj rsegs m STRTOD_GOT_GUARD [C8 (Z_to_bv 64 STRTOD_GUARD)] HRO
                ltac:(cell_bound) NG GG) as GG0.
  pose proof (RoAdaptCJ.rw_cells_norm_cj rsegs m STRTOD_GUARD [C8 canary] HRO ltac:(cell_bound) NQ QQ) as QQ0.
  pose proof (RoAdaptCJ.rw_cells_norm_cj rsegs m STRTOD_ERRNO [C4 ev] HRO ltac:(cell_bound) NE ERR) as ERR0.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc (MemNorm.normalize_cj rsegs m) s e txt ejunk canary ev Ha0 Ha1 Htp BY0 NUM LEN SLOT0 ST0 GT
                ltac:(unfold TASK_SIZE in *; lia) S4 ltac:(unfold TASK_SIZE in *; lia) SPL SEL
                ltac:(unfold TASK_SIZE in *; lia) SEP GG0 QQ0 ERR0
                (MemNorm.mem_inv_cj_inv rsegs _ MCJ) (MemNorm.mem_inv_cj_task rsegs _ MCJ) FRM) as E0.
  pose proof (MemNorm.evt_normalize_cj rsegs _ _ F _ fc None m (seg_rom rsegs) strtod_wx HRO E0) as E.
  eapply evt_mono; [exact E|].
  intros st (s0' & P & MR & CS). unfold strtod_post in P.
  destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc'
                 & m' & ev' & c & bits & E1 & SC & Hc & PEC & FA0 & FOK & FRM' & ERR' & MU & WM & MI' & TM' & ST').
  subst s0'.
  destruct st as [regs fregs pc svc resv fcsr mem rom].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem).
  cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, CS.
  unfold strtod_ro_post.
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', mem, ev', c, bits.
  split; [unfold MS; subst; reflexivity|].
  split; [exact SC|]. split; [exact Hc|].
  split; [exact (RoAdaptCJ.rw_cells_back_cj rsegs _ _ _ _ Hmem PEC)|].
  split; [exact FA0|]. split; [exact FOK|]. split; [exact FRM'|].
  split; [exact (RoAdaptCJ.rw_cells_back_cj rsegs _ _ _ _ Hmem ERR')|].
  split; [eapply MemNorm.munch_rel_cj; [exact REL | exact Hmem | exact CS | exact MU]|].
  split; [eapply MemNorm.wmono_rel_cj; [exact REL | exact Hmem | exact CS | exact WM]|].
  split; [exact (MemNorm.ro_agree_same_cj rsegs _ _ HRO CS)|].
  exact (RoAdaptCJ.stk_back_cj rsegs _ _ _ _ Hmem ST').
Qed.

Theorem strtod_ro_holds : strtod_ro_contract.
Proof. exact (strtod_ro_of strtod_holds). Qed.
