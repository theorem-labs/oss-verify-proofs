From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memcpy_c memmove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memmove_ro_c memmove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import RoAdapt.
Import ListNotations.
Open Scope bv_scope.

Lemma memmove_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u8arr_ro_norm : forall m A bs, MemNorm.ro_agree rsegs m -> u8arr rsegs m A bs ->
  not_ro rsegs A (Z.of_nat (length bs)) -> u8arr rsegs (MemNorm.normalize rsegs m) A bs.
Proof.
  intros m A bs HR [Hb Hw] Hn. split.
  - apply MemNorm.bytes_at_normalize; assumption.
  - exact (wr_at_norm' rsegs m A _ HR Hw Hn).
Qed.

Lemma u8arr_ro_back : forall m m0 A bs, MemNorm.mem_rel rsegs m m0 -> u8arr rsegs m0 A bs -> u8arr rsegs m A bs.
Proof.
  intros m m0 A bs REL [Hb Hw]. split.
  - exact (bytes_at_back rsegs m m0 A bs REL Hb).
  - exact (MemNorm.wr_at_rel rsegs m m0 A _ REL Hw).
Qed.

Theorem memmove_ro_of : memmove_contract -> memmove_ro_contract.
Proof.
  intros H. unfold memmove_ro_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m U us HU HNU H8 HA1 HA0 HA2 HRO.
  pose proof (MemNorm.mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  { eapply MemNorm.evt_normalize; [exact memmove_wx | exact HRO | ].
    apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (MemNorm.normalize rsegs m) U us).
    - exact (u8arr_ro_norm m U us HRO HU HNU).
    - exact H8.
    - exact HA1.
    - exact HA0.
    - exact HA2.
    - exact (MemNorm.mem_inv_normalize rsegs m). }
  intros s (s0' & P & MR & RS).
  destruct P as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                 MU & WM & MI & UA).
  destruct s as [regs fregs pc svc resv fcsr mem rom].
  destruct MR as (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hmem). cbn in Hr, Hf, Hpc, Hsvc, Hres, Hfc, Hrom, Hmem, RS.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mem.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - unfold MS. subst. reflexivity.
  - eapply MemNorm.munch_rel; [exact REL|exact Hmem|exact RS|exact MU].
  - eapply MemNorm.wmono_rel; [exact REL|exact Hmem|exact RS|exact WM].
  - eapply MemNorm.ro_agree_same; [exact HRO|exact RS].
  - exact (u8arr_ro_back mem m' U _ Hmem UA).
Qed.

Theorem memmove_ro_holds : memcpy_contract -> memmove_ro_contract.
Proof. intros H0. exact (memmove_ro_of (memmove_holds H0)). Qed.
