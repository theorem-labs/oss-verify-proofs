From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require strchr_c strncasecmp_c LibcNeeds_c.
Import ListNotations.
Open Scope Z_scope.

Lemma find_byte_idx : forall c (l : list byte),
  find_byte c l = find_idx (fun x => x =? c) (zbytes l).
Proof.
  intros c l. unfold zbytes. induction l as [|b l IH]; cbn; [reflexivity|].
  destruct (bv_unsigned b =? c); [reflexivity|]. rewrite IH. destruct (find_idx _ _); reflexivity.
Qed.

Lemma not_in0_of_forall : forall l : list byte, Forall (fun b => bv_unsigned b <> 0) l -> ~ In (Z_to_bv 8 0) l.
Proof. intros l HF Hin. rewrite Forall_forall in HF. apply (HF _ Hin). reflexivity. Qed.

Theorem strchr_adapt : strchr_c.strchr_contract -> LibcNeeds_c.strchr_contract.
Proof.
  intros H. unfold LibcNeeds_c.strchr_contract, LibcNeeds_c.STRCHR_K, off_stack.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs slack
    [HB [HF HW]] HC MI ST LO SEP.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs slack lo
             ST HB (not_in0_of_forall bs HF) HW MI); [lia|].
    rewrite !Nat2Z.inj_add in SEP. cbn [Z.of_nat Pos.of_succ_nat] in SEP. lia.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & _).
    unfold kret. exists t0', t1', t2'.
    exists (Z_to_bv 64 (strchr_c.strchr_val (bv_unsigned a0) (bv_unsigned a1 mod 256) bs)).
    exists a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    unfold strchr_c.strchr_val, strchr_res. rewrite Z.mod_small by lia.
    replace (bv_unsigned a1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite find_byte_idx. destruct (find_idx _ _); reflexivity.
Qed.

Theorem strncasecmp_adapt : strncasecmp_c.strncasecmp_contract -> LibcNeeds_c.strncasecmp_contract.
Proof.
  intros H. unfold LibcNeeds_c.strncasecmp_contract, LibcNeeds_c.STRNCASECMP_K, LibcNeeds_c.cstr0, off_stack.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb rb
    [HL FL] [HR FR] MI ST LO SL SR.
  rewrite Nat2Z.inj_add in SL, SR. cbn [Z.of_nat Pos.of_succ_nat] in SL, SR.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lb rb lo
             ST HL (not_in0_of_forall lb FL) HR (not_in0_of_forall rb FR) MI); lia.
  - intros ms' (r & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & _ & _ & HI).
    unfold kret. exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    + intros Hr. apply (proj1 HI). apply bv_eq. rewrite Hr. reflexivity.
    + intros Heq. apply (proj2 HI) in Heq. rewrite Heq. reflexivity.
Qed.
